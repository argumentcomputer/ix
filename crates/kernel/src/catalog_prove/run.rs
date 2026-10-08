use super::*;
use std::{
  io::{BufRead, BufReader},
  process::{Command, Stdio},
};

pub(super) trait Runner {
  fn run(&mut self, args: &[String]) -> Result<Vec<Address>, String>;
}

struct ProcessRunner<'a> {
  executable: &'a Path,
}

impl Runner for ProcessRunner<'_> {
  fn run(&mut self, args: &[String]) -> Result<Vec<Address>, String> {
    eprintln!("[catalog prove] ix {}", args.join(" "));
    let mut child = Command::new(self.executable)
      .args(args)
      .stdin(Stdio::null())
      .stdout(Stdio::piped())
      .stderr(Stdio::inherit())
      .spawn()
      .map_err(|e| {
        format!("start ix {}: {e}", args.first().map_or("", String::as_str))
      })?;
    let result = (|| {
      let stdout = child.stdout.take().ok_or("child stdout unavailable")?;
      let mut proofs = Vec::new();
      for line in BufReader::new(stdout).lines() {
        let line = line.map_err(|e| format!("read child output: {e}"))?;
        eprintln!("{line}");
        if let Ok(a) = address(line.trim()) {
          proofs.push(a);
        }
      }
      let status = child.wait().map_err(|e| format!("wait for ix: {e}"))?;
      if !status.success() {
        return Err(format!("ix {} failed: {status}", args[0]));
      }
      Ok(proofs)
    })();
    if result.is_err() {
      let _ = child.kill();
      let _ = child.wait();
    }
    result
  }
}

/// Prove or inspect a catalog with the ordinary CLI backends. The advisory
/// file lock lasts through all subprocesses and is released on process exit.
pub fn run_catalog(options: &Options) -> Result<Value, String> {
  let home_dir = std::env::var_os("HOME").ok_or("HOME is not set")?;
  let ix_root = PathBuf::from(home_dir).join(".ix");
  execute(
    options,
    &ix_root,
    &mut ProcessRunner { executable: &options.executable },
  )
}

fn verify_args(
  artifacts: &Artifacts,
  proof: &str,
  options: &Options,
) -> Vec<String> {
  vec![
    "verify".into(),
    "--aggregate".into(),
    "--ixe".into(),
    artifacts.env_path.display().to_string(),
    "--ixes".into(),
    artifacts.manifest_path.display().to_string(),
    "--structural-above".into(),
    options.structural_above.to_string(),
    proof.into(),
  ]
}

fn store_path(ix_root: &Path, addr: &Address) -> PathBuf {
  let hex = addr.hex();
  ix_root
    .join("store")
    .join(&hex[..2])
    .join(&hex[2..4])
    .join(&hex[4..6])
    .join(&hex[6..])
}

fn proof_claim(ix_root: &Path, addr: &Address) -> Result<Address, String> {
  let bytes = read(&store_path(ix_root, addr))?;
  if Address::hash(&bytes) != *addr {
    return Err("proof store object has the wrong hash".into());
  }
  let mut cursor = bytes.as_slice();
  let proof = ixon::Proof::get(&mut cursor)
    .map_err(|e| format!("decode proof {}: {e}", addr.hex()))?;
  if !cursor.is_empty() {
    return Err("trailing proof bytes".into());
  }
  let mut claim = Vec::new();
  proof.claim.put(&mut claim);
  Ok(Address::hash(&claim))
}

/// These pointers are hints only. `ix prove --skip-proven` verifies the
/// wrapper's exact claim and its proof with the active verifier before reuse.
fn seed_index(
  ix_root: &Path,
  dir: &Path,
  record: &Value,
) -> Result<(), String> {
  fs::create_dir_all(&dir).map_err(|e| format!("create shard index: {e}"))?;
  for leaf in record["leaves"].as_array().ok_or("missing leaf records")? {
    let claim = address(string(leaf, "claim")?)?;
    let proof = address(string(leaf, "proof")?)?;
    match proof_claim(ix_root, &proof) {
      Ok(actual) if actual == claim => {
        atomic_write(
          &dir.join(claim.hex()),
          format!("{}\n", proof.hex()).as_bytes(),
        )?;
      },
      _ => eprintln!(
        "[catalog prove] cached leaf {} unavailable or corrupt; proof lookup will miss unless another valid entry exists",
        claim.hex()
      ),
    }
  }
  Ok(())
}

fn bind_leaf_proofs(
  ix_root: &Path,
  leaves: &[plan::Leaf],
  proofs: &[Address],
) -> Result<Vec<Value>, String> {
  let mut by_claim = std::collections::BTreeMap::new();
  for proof in proofs {
    let claim = proof_claim(ix_root, proof)?;
    if by_claim.insert(claim, proof).is_some() {
      return Err("more than one proof for a leaf claim".into());
    }
  }
  if by_claim.len() != leaves.len() {
    return Err(
      "prover did not return exactly one proof per final shard".into(),
    );
  }
  leaves
    .iter()
    .map(|leaf| {
      let proof = by_claim
        .get(&leaf.claim)
        .ok_or_else(|| format!("no proof for final leaf {}", leaf.id))?;
      let mut row = leaf.json();
      row["proof"] = Value::String(proof.hex());
      Ok(row)
    })
    .collect()
}

fn claim_summary(
  leaves: &[plan::Leaf],
  base: Option<&Value>,
) -> Result<Value, String> {
  let mut previous = rustc_hash::FxHashSet::default();
  if let Some(base) = base {
    for leaf in base["leaves"].as_array().ok_or("missing base leaves")? {
      previous.insert(address(string(leaf, "claim")?)?);
    }
  }
  let mut retained = 0;
  let mut subjects_in_new_claims = 0;
  let claims = leaves
    .iter()
    .map(|leaf| {
      let reused = previous.contains(&leaf.claim);
      if reused {
        retained += 1;
      } else {
        subjects_in_new_claims += leaf.subjects.len();
      }
      json!({"id": leaf.id, "claim": leaf.claim.hex(),
        "subjects": leaf.subjects.len(), "frontier": leaf.frontier.len(),
        "retainedFromBase": reused})
    })
    .collect::<Vec<_>>();
  Ok(json!({"shards": leaves.len(), "claims": claims,
    "retainedClaims": retained, "changedBaseClaims": previous.len() - retained,
    "newClaims": leaves.len() - retained,
    "subjectsInNewClaims": subjects_in_new_claims}))
}

/// An unchanged partition and corpus can carry the verified base root into a
/// new snapshot. Leaf wrappers remain required for later incremental updates.
fn reusable_base_root(
  ix_root: &Path,
  artifacts: &Artifacts,
  base: Option<&Value>,
) -> Result<Option<(Address, Vec<Value>)>, String> {
  let Some(base) = base else { return Ok(None) };
  if inventory_root(&artifacts.inventory)?.hex() != string(base, "corpusRoot")?
    || file_hash(&artifacts.manifest_path)?.hex()
      != string(base, "partitionHash")?
  {
    return Ok(None);
  }
  let proofs = base["leaves"]
    .as_array()
    .ok_or("missing base leaves")?
    .iter()
    .map(|leaf| address(string(leaf, "proof")?))
    .collect::<Result<Vec<_>, _>>()?;
  match bind_leaf_proofs(ix_root, &artifacts.leaves, &proofs) {
    Ok(rows) => Ok(Some((address(string(base, "rootProof")?)?, rows))),
    Err(error) => {
      eprintln!("[catalog prove] base leaf artifacts need recovery: {error}");
      Ok(None)
    },
  }
}

fn binding(
  snapshot: &Snapshot,
  profile: &Value,
  base: Option<&Value>,
) -> Value {
  json!({"schema": SCHEMA, "snapshotHash": snapshot.manifest_hash.hex(),
    "contentRoot": snapshot.catalog.content_root.hex(), "membersRoot": snapshot.catalog.members_root.hex(),
    "profile": profile, "baseRecord": base.map(digest_json).map(|a| a.hex())})
}

fn ensure_pending_binding(
  pending: &Value,
  expected: &Value,
) -> Result<(), String> {
  for key in [
    "schema",
    "snapshotHash",
    "contentRoot",
    "membersRoot",
    "profile",
    "baseRecord",
  ] {
    if pending.get(key) != expected.get(key) {
      return Err(format!(
        "pending plan has different {key}; resume with its original catalog, base and profile"
      ));
    }
  }
  Ok(())
}

fn prove_and_aggregate(
  options: &Options,
  ix_root: &Path,
  runner: &mut dyn Runner,
  artifacts: &mut Artifacts,
  base_record: Option<&Value>,
  pending: &mut Value,
) -> Result<Address, String> {
  let use_lanes = options.lanes > 0 && artifacts.leaves.len() > 1;
  let index_dir = if use_lanes {
    std::env::var_os("AIUR_LANES_CACHE_DIR")
      .map(PathBuf::from)
      .unwrap_or_else(|| ix_root.join("cache"))
      .join("shard-proofs")
  } else {
    ix_root.join("cache/shard-proofs")
  };
  if let Some(record) = base_record {
    seed_index(ix_root, &index_dir, record)?;
  }
  if pending["status"] == "leaves-proved" {
    seed_index(ix_root, &index_dir, pending)?;
  }
  let next_manifest = artifacts.work.join("refined.ixes");
  let mut prove = vec![
    "prove".into(),
    "--ixe".into(),
    artifacts.env_path.display().to_string(),
    "--ixes".into(),
    artifacts.manifest_path.display().to_string(),
    "--skip-proven".into(),
    "--out-ixes".into(),
    next_manifest.display().to_string(),
  ];
  if options.max_ram != 0 {
    prove.extend(["--max-ram".into(), options.max_ram.to_string()]);
  }
  if options.trace_shards || use_lanes {
    prove.push("--trace-shards".into());
  }
  if use_lanes {
    eprintln!(
      "[catalog prove] using {} GPU lane(s) for pipelined proving and aggregation",
      options.lanes
    );
    prove.extend([
      "--lanes".into(),
      options.lanes.to_string(),
      "--structural-above".into(),
      options.structural_above.to_string(),
    ]);
  } else {
    prove.push("--leaf-only".into());
  }
  if options.exec_jobs != 0 {
    prove.extend(["--exec-jobs".into(), options.exec_jobs.to_string()]);
  }
  let produced = runner.run(&prove)?;
  let refined =
    crate::shard::ShardManifest::from_bytes(&read(&next_manifest)?)?;
  let final_leaves =
    plan::leaves(&artifacts.env, &artifacts.inventory, &refined)?;
  let (proofs, lane_root) = if use_lanes {
    if produced.len() != 1 {
      return Err("GPU pipeline did not return exactly one root proof".into());
    }
    let proofs = final_leaves
      .iter()
      .map(|leaf| {
        let bytes = read(&index_dir.join(leaf.claim.hex()))?;
        let text = std::str::from_utf8(&bytes)
          .map_err(|_| format!("invalid proof index for leaf {}", leaf.id))?;
        address(text.trim())
      })
      .collect::<Result<Vec<_>, String>>()?;
    (proofs, Some(produced[0].clone()))
  } else {
    (produced, None)
  };
  let proof_rows = bind_leaf_proofs(ix_root, &final_leaves, &proofs)?;
  atomic_write(&artifacts.manifest_path, &refined.to_bytes())?;
  artifacts.manifest = refined;
  artifacts.leaves = final_leaves;
  pending["status"] = json!("leaves-proved");
  pending["partitionHash"] = json!(file_hash(&artifacts.manifest_path)?.hex());
  pending["leaves"] = json!(proof_rows);
  write_json(&artifacts.work.join("pending.json"), pending)?;

  let mut aggregate = vec![
    "aggregate".into(),
    "--ixe".into(),
    artifacts.env_path.display().to_string(),
    "--ixes".into(),
    artifacts.manifest_path.display().to_string(),
    "--structural-above".into(),
    options.structural_above.to_string(),
  ];
  if options.max_ram != 0 {
    aggregate.extend(["--max-ram".into(), options.max_ram.to_string()]);
  }
  if options.jobs != 0 {
    aggregate.extend(["--jobs".into(), options.jobs.to_string()]);
  }
  if options.trace_shards {
    aggregate.push("--trace-shards".into());
  }
  aggregate.extend(proofs.iter().map(Address::hex));
  let roots = match lane_root {
    Some(root) => vec![root],
    None => runner.run(&aggregate)?,
  };
  if roots.len() != 1 {
    return Err("aggregate did not return exactly one root proof".into());
  }
  Ok(roots[0].clone())
}

pub(super) fn execute(
  options: &Options,
  ix_root: &Path,
  runner: &mut dyn Runner,
) -> Result<Value, String> {
  if options.plan_only && options.verify_only {
    return Err("--plan-only and verify-proof are mutually exclusive".into());
  }
  let lock = fs::OpenOptions::new()
    .read(true)
    .write(true)
    .create(true)
    .truncate(false)
    .open(options.catalog.join(".proving.lock"))
    .map_err(|e| format!("open catalog proving lock: {e}"))?;
  lock.try_lock().map_err(|e| {
    format!("catalog is already being processed, or cannot be locked: {e}")
  })?;
  let snapshot = Snapshot::load(&options.catalog)?;
  let record_path = options.catalog.join(RECORD);
  let existing =
    if record_path.exists() { Some(read_json(&record_path)?) } else { None };
  let base_record = if let Some(dir) = &options.base {
    Some(read_json(&dir.join(RECORD))?)
  } else {
    None
  };
  let profile =
    make_profile(options, existing.as_ref().or(base_record.as_ref()))?;
  if options.verify_only
    && options.allow_axioms.is_none()
    && !addresses(&profile["allowedAxioms"])?.is_empty()
  {
    return Err(
      "verify-proof requires an independently reviewed --allow-axioms file for a nonempty policy".into(),
    );
  }

  if let Some(record) = &existing {
    let artifacts =
      Artifacts::recorded(&options.catalog, &snapshot, record, &profile)?;
    proof_claim(ix_root, &address(string(record, "rootProof")?)?)?;
    runner.run(&verify_args(
      &artifacts,
      string(record, "rootProof")?,
      options,
    ))?;
    return Ok(
      json!({"status": if options.verify_only { "verified" } else { "reused" },
      "rootProof": record["rootProof"], "record": record_path, "newProofs": 0,
      "snapshotHash": snapshot.manifest_hash.hex(), "contentRoot": snapshot.catalog.content_root.hex(),
      "corpusRoot": record["corpusRoot"], "axioms": record["axioms"], "profile": profile,
      "snapshotSubjects": snapshot.addresses.len(), "corpusSubjects": artifacts.inventory.addresses.len()}),
    );
  }
  if options.verify_only {
    return Err("catalog has no completed proving record".into());
  }

  let base = if let (Some(dir), Some(record)) = (&options.base, &base_record) {
    let base_snapshot = Snapshot::load(dir)?;
    let artifacts = Artifacts::recorded(dir, &base_snapshot, record, &profile)?;
    proof_claim(ix_root, &address(string(record, "rootProof")?)?)?;
    runner.run(&verify_args(
      &artifacts,
      string(record, "rootProof")?,
      options,
    ))?;
    Some(artifacts)
  } else {
    None
  };

  let work = options.catalog.join("proving").join(digest_json(&profile).hex());
  fs::create_dir_all(&work)
    .map_err(|e| format!("create proving directory: {e}"))?;
  let pending_path = work.join("pending.json");
  let expected = binding(&snapshot, &profile, base_record.as_ref());
  let mut pending;
  let mut artifacts;
  if pending_path.exists() {
    pending = read_json(&pending_path)?;
    ensure_pending_binding(&pending, &expected)?;
    artifacts = Artifacts::open(work)?;
    if string(&pending, "corpusFileHash")?
      != file_hash(&artifacts.env_path)?.hex()
    {
      return Err("pending corpus bytes changed".into());
    }
  } else {
    let mut pieces = snapshot.pieces.clone();
    if let Some(base) = &base {
      pieces.insert(0, base.env_path.clone());
    }
    let env_path = work.join("corpus.ixe");
    catalog::merge_anon(&pieces, &env_path)?;
    let env = Env::get_anon_mmap(&env_path)?;
    let inventory = plan::Inventory::read(&env)?;
    inventory.check_axioms(&addresses(&profile["allowedAxioms"])?)?;
    snapshot.check_coverage(&inventory)?;
    let plan = plan::extend(
      &env,
      &inventory,
      base.as_ref().map(|a| (&a.env, &a.inventory, &a.manifest)),
      options.shards,
    )?;
    atomic_write(&work.join("shards.ixes"), &plan.manifest.to_bytes())?;
    pending = expected;
    pending["status"] = json!("planned");
    pending["corpusFileHash"] = json!(file_hash(&env_path)?.hex());
    pending["newSubjects"] = json!(plan.new_subjects);
    pending["retainedClaims"] = json!(plan.retained_claims);
    pending["changedBaseClaims"] = json!(plan.changed_base_claims);
    write_json(&pending_path, &pending)?;
    artifacts = Artifacts {
      work: work.clone(),
      env_path,
      manifest_path: work.join("shards.ixes"),
      env,
      inventory,
      manifest: plan.manifest,
      leaves: plan.leaves,
    };
  }
  drop(base);
  snapshot.check_coverage(&artifacts.inventory)?;
  artifacts.inventory.check_axioms(&addresses(&profile["allowedAxioms"])?)?;
  let mut report = json!({"status": "planned", "record": record_path, "work": artifacts.work,
    "snapshotHash": snapshot.manifest_hash.hex(), "contentRoot": snapshot.catalog.content_root.hex(),
    "corpusRoot": inventory_root(&artifacts.inventory)?.hex(),
    "axioms": addresses_json(&artifacts.inventory.axioms), "profile": profile,
    "snapshotSubjects": snapshot.addresses.len(), "corpusSubjects": artifacts.inventory.addresses.len(),
    "newSubjects": pending["newSubjects"]});
  report.as_object_mut().unwrap().extend(
    claim_summary(&artifacts.leaves, base_record.as_ref())?
      .as_object()
      .unwrap()
      .clone(),
  );
  eprintln!(
    "[catalog prove] snapshot={} corpus={} new={} retained-claims={} changed-base-claims={} new-claims={} subjects-in-new-claims={} shards={}",
    snapshot.addresses.len(),
    artifacts.inventory.addresses.len(),
    pending["newSubjects"],
    report["retainedClaims"],
    report["changedBaseClaims"],
    report["newClaims"],
    report["subjectsInNewClaims"],
    artifacts.leaves.len()
  );
  if options.plan_only {
    return Ok(report);
  }

  let root = if let Some((root, rows)) =
    reusable_base_root(ix_root, &artifacts, base_record.as_ref())?
  {
    eprintln!("[catalog prove] reusing verified base root; no new proof work");
    pending["status"] = json!("leaves-proved");
    pending["partitionHash"] =
      json!(file_hash(&artifacts.manifest_path)?.hex());
    pending["leaves"] = json!(rows);
    write_json(&pending_path, &pending)?;
    report["reusedBaseRoot"] = json!(true);
    report["newProofs"] = json!(0);
    root
  } else {
    report["reusedBaseRoot"] = json!(false);
    prove_and_aggregate(
      options,
      ix_root,
      runner,
      &mut artifacts,
      base_record.as_ref(),
      &mut pending,
    )?
  };
  proof_claim(ix_root, &root)?;
  runner.run(&verify_args(&artifacts, &root.hex(), options))?;
  let final_snapshot = Snapshot::load(&options.catalog)?;
  if final_snapshot.manifest_hash != snapshot.manifest_hash {
    return Err("catalog manifest changed during proving".into());
  }
  final_snapshot.check_coverage(&artifacts.inventory)?;
  if file_hash(&artifacts.env_path)?.hex()
    != string(&pending, "corpusFileHash")?
  {
    return Err("corpus changed during proving".into());
  }
  if file_hash(&artifacts.manifest_path)?.hex()
    != string(&pending, "partitionHash")?
  {
    return Err("partition changed during proving".into());
  }
  pending["status"] = json!("certified");
  pending["rootProof"] = json!(root.hex());
  pending["corpusRoot"] = json!(inventory_root(&artifacts.inventory)?.hex());
  pending["axioms"] = addresses_json(&artifacts.inventory.axioms);
  let summary = claim_summary(&artifacts.leaves, base_record.as_ref())?;
  for key in
    ["retainedClaims", "changedBaseClaims", "newClaims", "subjectsInNewClaims"]
  {
    pending[key] = summary[key].clone();
  }
  write_json(&record_path, &pending)?;
  report["status"] = json!("certified");
  report["rootProof"] = json!(root.hex());
  report.as_object_mut().unwrap().extend(summary.as_object().unwrap().clone());
  Ok(report)
}
