use super::run::{Runner, execute};
use super::*;
use crate::shard::{AggNode, ShardManifest};
use ix_common::env::DefinitionSafety;
use ixon::constant::{
  Axiom, Constant, ConstantInfo, DefKind, Definition, DefinitionProj, MutConst,
};
use ixon::expr::Expr;
use std::sync::atomic::{AtomicU64, Ordering};

fn definition(seed: u64, dependency: Option<Address>) -> Constant {
  Constant::with_tables(
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: seed,
      typ: Expr::sort(0),
      value: if dependency.is_some() {
        Expr::reference(0, Vec::new())
      } else {
        Expr::sort(0)
      },
    }),
    Vec::new(),
    dependency.into_iter().collect(),
    Vec::new(),
  )
}

fn insert(env: &Env, constant: Constant) -> Address {
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let addr = Address::hash(&bytes);
  env.store_const(addr.clone(), constant);
  addr
}

fn copy_env(old: &Env) -> Env {
  let env = Env::new();
  for entry in old.consts.iter() {
    env.store_const(
      entry.key().clone(),
      (*entry.value().get().unwrap()).clone(),
    );
  }
  env
}

fn baseline(env: &Env, shards: usize) -> plan::Plan {
  plan::extend(env, &plan::Inventory::read(env).unwrap(), None, shards).unwrap()
}

#[test]
fn append_preserves_old_claims_tree_and_dependency_frontier() {
  let old = Env::new();
  let a = insert(&old, definition(0, None));
  insert(&old, definition(1, Some(a.clone())));
  let old_plan = baseline(&old, 2);
  let new = copy_env(&old);
  let c = insert(&new, definition(2, Some(a.clone())));
  let before = plan::Inventory::read(&old).unwrap();
  let after = plan::Inventory::read(&new).unwrap();
  let update =
    plan::extend(&new, &after, Some((&old, &before, &old_plan.manifest)), 1)
      .unwrap();
  assert_eq!(update.new_subjects, 1);
  assert_eq!(update.retained_claims, 2);
  assert_eq!(update.changed_base_claims, 0);
  assert_eq!(update.leaves[2].subjects, vec![c]);
  assert_eq!(update.leaves[2].frontier, vec![a]);
  assert_eq!(
    update.manifest.tree,
    Some(AggNode::Internal(
      Box::new(old_plan.manifest.tree.unwrap()),
      Box::new(AggNode::Leaf(2))
    ))
  );
}

#[test]
fn identical_corpus_preserves_partition_without_rebalancing() {
  let env = Env::new();
  let a = insert(&env, definition(0, None));
  insert(&env, definition(1, Some(a)));
  let plan = baseline(&env, 2);
  let inventory = plan::Inventory::read(&env).unwrap();
  let again = plan::extend(
    &env,
    &inventory,
    Some((&env, &inventory, &plan.manifest)),
    99,
  )
  .unwrap();
  assert_eq!(again.manifest, plan.manifest);
  assert_eq!(again.new_subjects, 0);
  assert_eq!(again.retained_claims, 2);
}

#[test]
fn new_projection_invalidates_its_old_owner_instead_of_false_reuse() {
  let old = Env::new();
  let ConstantInfo::Defn(defn) = definition(0, None).info else {
    unreachable!()
  };
  let block =
    insert(&old, Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(defn)])));
  let initial = baseline(&old, 1);
  let new = copy_env(&old);
  insert(
    &new,
    Constant::new(ConstantInfo::DPrj(DefinitionProj { idx: 0, block })),
  );
  let update = plan::extend(
    &new,
    &plan::Inventory::read(&new).unwrap(),
    Some((&old, &plan::Inventory::read(&old).unwrap(), &initial.manifest)),
    1,
  )
  .unwrap();
  assert_eq!(update.new_subjects, 1);
  assert_eq!(update.manifest.shards.len(), 1);
  assert_eq!(update.retained_claims, 0);
  assert_eq!(update.changed_base_claims, 1);
  assert_ne!(update.leaves[0].claim, initial.leaves[0].claim);
}

#[test]
fn missing_dependencies_and_duplicate_ownership_fail_closed() {
  let invalid = Env::new();
  insert(&invalid, definition(0, Some(Address::hash(b"absent"))));
  assert!(
    plan::Inventory::read(&invalid)
      .err()
      .unwrap()
      .contains("missing dependency")
  );
  let env = Env::new();
  insert(&env, definition(1, None));
  let mut plan = baseline(&env, 1);
  let mut duplicate = plan.manifest.shards[0].clone();
  duplicate.id = 1;
  plan.manifest.shards.push(duplicate);
  plan.manifest.num_shards = 2;
  assert!(
    plan::leaves(&env, &plan::Inventory::read(&env).unwrap(), &plan.manifest)
      .err()
      .unwrap()
      .contains("duplicate block")
  );
}

struct Fixture {
  dir: PathBuf,
  store: PathBuf,
  executable: PathBuf,
}

impl Fixture {
  fn new() -> Self {
    static SERIAL: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
      "ix-catalog-prove-{}-{}",
      std::process::id(),
      SERIAL.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&dir).unwrap();
    let executable = dir.join("ix");
    fs::write(&executable, b"fixture backend identity").unwrap();
    Self { store: dir.join("ix-store"), executable, dir }
  }

  fn catalog(&self, name: &str, env: &Env) -> PathBuf {
    let piece = self.dir.join(format!("{name}.ixe"));
    env.put_file(&piece).unwrap();
    let dir = self.dir.join(format!("{name}.ixc"));
    catalog::assemble_into(
      &dir,
      &[catalog::MemberSpec {
        path: piece,
        label: "Library".into(),
        toolchain: "fixture".into(),
        source_pin: format!("git:fixture@{name}"),
        deps: Vec::new(),
      }],
    )
    .unwrap();
    dir
  }

  fn options(&self, dir: PathBuf) -> Options {
    Options {
      catalog: dir,
      base: None,
      executable: self.executable.clone(),
      allow_axioms: None,
      shards: 1,
      structural_above: 4096,
      max_ram: 0,
      jobs: 0,
      exec_jobs: 0,
      lanes: 0,
      trace_shards: false,
      plan_only: false,
      verify_only: false,
    }
  }

  fn runner(&self) -> Backend {
    Backend {
      store: self.store.clone(),
      calls: Vec::new(),
      proved_claims: Vec::new(),
      reused_claims: Vec::new(),
      fail: None,
    }
  }
}

impl Drop for Fixture {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.dir);
  }
}

/// Subprocess results are simulated to test publication, binding and resume
/// boundaries without running a STARK prover. Proof validity itself belongs to
/// the existing verifier suites; a failed verifier must prevent publication.
struct Backend {
  store: PathBuf,
  calls: Vec<Vec<String>>,
  proved_claims: Vec<Address>,
  reused_claims: Vec<Address>,
  fail: Option<String>,
}

impl Backend {
  fn proof_path(&self, address: &Address) -> PathBuf {
    let hex = address.hex();
    self
      .store
      .join("store")
      .join(&hex[..2])
      .join(&hex[2..4])
      .join(&hex[4..6])
      .join(&hex[6..])
  }

  fn cached_leaf(&self, claim: &Address) -> Option<Address> {
    let pointer = fs::read_to_string(
      self.store.join("cache/shard-proofs").join(claim.hex()),
    )
    .ok()?;
    let address = address(pointer.trim()).ok()?;
    let bytes = read(&self.proof_path(&address)).ok()?;
    if Address::hash(&bytes) != address {
      return None;
    }
    let mut cursor = bytes.as_slice();
    let wrapper = ixon::Proof::get(&mut cursor).ok()?;
    let mut claim_bytes = Vec::new();
    wrapper.claim.put(&mut claim_bytes);
    (cursor.is_empty()
      && wrapper.proof == [1]
      && Address::hash(&claim_bytes) == *claim)
      .then_some(address)
  }

  fn save(&self, claim: ixon::Claim, marker: u8) -> Address {
    let wrapper = ixon::Proof::new(claim, vec![marker]);
    let mut bytes = Vec::new();
    wrapper.put(&mut bytes);
    let address = Address::hash(&bytes);
    let path = self.proof_path(&address);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
    address
  }
}

impl Runner for Backend {
  fn run(&mut self, args: &[String]) -> Result<Vec<Address>, String> {
    self.calls.push(args.to_vec());
    if self.fail.as_deref() == Some(&args[0]) {
      return Err(format!("fixture {} failure", args[0]));
    }
    let flag = |name: &str| -> &str {
      &args[args.iter().position(|s| s == name).unwrap() + 1]
    };
    match args[0].as_str() {
      "verify" => Ok(Vec::new()),
      "prove" => {
        assert!(args.iter().any(|s| s == "--skip-proven"));
        let env = Env::get_anon_mmap(Path::new(flag("--ixe")))?;
        let manifest =
          ShardManifest::from_bytes(&read(Path::new(flag("--ixes")))?)?;
        let inventory = plan::Inventory::read(&env)?;
        let leaves = plan::leaves(&env, &inventory, &manifest)?;
        fs::copy(flag("--ixes"), flag("--out-ixes")).unwrap();
        let index = self.store.join("cache/shard-proofs");
        fs::create_dir_all(&index).unwrap();
        let proofs = leaves
          .iter()
          .map(|leaf| {
            if let Some(proof) = self.cached_leaf(&leaf.claim) {
              self.reused_claims.push(leaf.claim.clone());
              return proof;
            }
            let (claim, _) =
              ixon::shard_claim::shard_check_env_claim(&env, &leaf.subjects)
                .unwrap();
            self.proved_claims.push(leaf.claim.clone());
            let proof = self.save(claim, 1);
            fs::write(index.join(leaf.claim.hex()), proof.hex()).unwrap();
            proof
          })
          .collect::<Vec<_>>();
        if args.iter().any(|arg| arg == "--lanes") {
          if self.fail.as_deref() == Some("lane-index") {
            fs::write(index.join(leaves[0].claim.hex()), proofs[1].hex())
              .unwrap();
          }
          let root = inventory_root(&inventory)?;
          Ok(vec![
            self.save(ixon::Claim::CheckEnv { root, assumptions: None }, 2),
          ])
        } else {
          Ok(proofs)
        }
      },
      "aggregate" => {
        let env = Env::get_anon_mmap(Path::new(flag("--ixe")))?;
        let root = inventory_root(&plan::Inventory::read(&env)?)?;
        Ok(vec![
          self.save(ixon::Claim::CheckEnv { root, assumptions: None }, 2),
        ])
      },
      command => Err(format!("unexpected subprocess {command}")),
    }
  }
}

#[test]
fn static_catalog_partition_balances_serialized_work() {
  let env = Env::new();
  for seed in 0..256 {
    insert(&env, definition(seed, None));
  }
  let plan = baseline(&env, 8);
  assert_eq!(plan.leaves.len(), 8);
  assert_eq!(
    plan.leaves.iter().map(|leaf| leaf.subjects.len()).sum::<usize>(),
    256
  );
  assert!(plan.leaves.iter().all(|leaf| leaf.subjects.len() <= 64));
}

#[test]
fn gpu_pipeline_publishes_verified_root_without_separate_aggregation() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  insert(&env, definition(1, None));
  let mut options = fixture.options(fixture.catalog("A", &env));
  options.shards = 2;
  options.lanes = 2;
  options.structural_above = 0;
  let mut runner = fixture.runner();
  let report = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(report["status"], "certified");
  assert_eq!(
    runner.calls.iter().map(|call| call[0].as_str()).collect::<Vec<_>>(),
    ["prove", "verify"]
  );
  assert!(runner.calls[0].windows(2).any(|args| args == ["--lanes", "2"]));
  assert!(
    runner.calls[0].windows(2).any(|args| args == ["--structural-above", "0"])
  );
  let record = read_json(&options.catalog.join(RECORD)).unwrap();
  assert_eq!(record["leaves"].as_array().unwrap().len(), 2);
  runner.calls.clear();
  let repeat = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(repeat["status"], "reused");
  assert_eq!(runner.calls.len(), 1);
  assert_eq!(runner.calls[0][0], "verify");
}

#[test]
fn gpu_pipeline_rejects_wrong_leaf_bindings_and_failed_verification() {
  for failure in ["lane-index", "verify"] {
    let fixture = Fixture::new();
    let env = Env::new();
    insert(&env, definition(0, None));
    insert(&env, definition(1, None));
    let mut options = fixture.options(fixture.catalog("A", &env));
    options.shards = 2;
    options.lanes = 2;
    let mut runner = fixture.runner();
    runner.fail = Some(failure.into());
    assert!(execute(&options, &fixture.store, &mut runner).is_err());
    assert!(!options.catalog.join(RECORD).exists());
  }
}

#[test]
fn plan_only_writes_no_certificate_and_runs_no_prover() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let mut options = fixture.options(fixture.catalog("A", &env));
  options.plan_only = true;
  let mut runner = fixture.runner();
  let report = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(report["status"], "planned");
  assert_eq!(report["newSubjects"], 1);
  assert!(!options.catalog.join(RECORD).exists());
  assert!(runner.calls.is_empty());
}

#[test]
fn warm_repeat_verifies_existing_root_without_proving() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let options = fixture.options(fixture.catalog("A", &env));
  let mut runner = fixture.runner();
  let first = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(first["status"], "certified");
  runner.calls.clear();
  let second = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(second["status"], "reused");
  assert_eq!(second["rootProof"], first["rootProof"]);
  assert_eq!(runner.calls.len(), 1);
  assert_eq!(runner.calls[0][0], "verify");
}

#[test]
fn edits_reuse_the_old_chunk_and_prove_only_changed_dependents() {
  for lanes in [0, 2] {
    let fixture = Fixture::new();
    let old = Env::new();
    let stable = insert(&old, definition(0, None));
    let a = insert(&old, definition(1, Some(stable.clone())));
    insert(&old, definition(2, Some(a)));
    let mut before = fixture.options(fixture.catalog("A", &old));
    before.lanes = lanes;
    let mut runner = fixture.runner();
    execute(&before, &fixture.store, &mut runner).unwrap();
    let old_record = read_json(&before.catalog.join(RECORD)).unwrap();

    let edited = Env::new();
    insert(&edited, definition(0, None));
    let a = insert(&edited, definition(3, Some(stable.clone())));
    let b = insert(&edited, definition(2, Some(a.clone())));
    let mut options = fixture.options(fixture.catalog("B", &edited));
    options.base = Some(before.catalog);
    options.lanes = lanes;
    runner.calls.clear();
    runner.proved_claims.clear();
    runner.reused_claims.clear();
    let report = execute(&options, &fixture.store, &mut runner).unwrap();
    assert_eq!(report["newSubjects"], 2);
    assert_eq!(report["snapshotSubjects"], 3);
    assert_eq!(report["corpusSubjects"], 5);
    assert_eq!(report["retainedClaims"], 1);
    assert_eq!(report["changedBaseClaims"], 0);
    assert_eq!(report["newClaims"], 1);
    assert_eq!(report["subjectsInNewClaims"], 2);
    assert_eq!(report["claims"][0]["retainedFromBase"], true);
    assert_eq!(report["claims"][1]["retainedFromBase"], false);
    assert_eq!(report["reusedBaseRoot"], false);
    let record = read_json(&options.catalog.join(RECORD)).unwrap();
    assert_eq!(record["leaves"][0], old_record["leaves"][0]);
    let mut added = vec![a, b];
    added.sort_unstable();
    assert_eq!(record["leaves"][1]["subjects"], addresses_json(&added));
    assert_eq!(record["leaves"][1]["frontier"], addresses_json(&[stable]));
    assert_eq!(
      runner.proved_claims,
      vec![address(string(&record["leaves"][1], "claim").unwrap()).unwrap()]
    );
    assert_eq!(
      runner.reused_claims,
      vec![address(string(&record["leaves"][0], "claim").unwrap()).unwrap()]
    );
    let operations =
      runner.calls.iter().map(|c| c[0].as_str()).collect::<Vec<_>>();
    assert_eq!(
      operations,
      if lanes == 0 {
        vec!["verify", "prove", "aggregate", "verify"]
      } else {
        vec!["verify", "prove", "verify"]
      }
    );
  }
}

#[test]
fn reverts_and_deletions_reuse_the_base_root_without_proving() {
  let fixture = Fixture::new();
  let old = Env::new();
  insert(&old, definition(0, None));
  insert(&old, definition(1, None));
  let old_options = fixture.options(fixture.catalog("A", &old));
  let mut runner = fixture.runner();
  execute(&old_options, &fixture.store, &mut runner).unwrap();
  let new = Env::new();
  insert(&new, definition(2, None));
  insert(&new, definition(1, None));
  let mut options = fixture.options(fixture.catalog("B", &new));
  options.base = Some(old_options.catalog.clone());
  let report = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(report["newSubjects"], 1);
  assert_eq!(report["retainedClaims"], 1);
  let record = read_json(&options.catalog.join(RECORD)).unwrap();
  fs::remove_dir_all(&old_options.catalog).unwrap();
  fs::remove_dir_all(fixture.store.join("cache")).unwrap();
  let mut revert = fixture.options(fixture.catalog("C", &old));
  revert.base = Some(options.catalog.clone());
  revert.plan_only = true;
  let plan = execute(&revert, &fixture.store, &mut runner).unwrap();
  assert_eq!(plan["newSubjects"], 0);
  assert_eq!(plan["newClaims"], 0);
  assert_eq!(plan["subjectsInNewClaims"], 0);
  assert!(!revert.catalog.join(RECORD).exists());
  runner.calls.clear();
  runner.proved_claims.clear();
  revert.plan_only = false;
  let reverted = execute(&revert, &fixture.store, &mut runner).unwrap();
  assert_eq!(reverted["status"], "certified");
  assert_eq!(reverted["snapshotSubjects"], 2);
  assert_eq!(reverted["corpusSubjects"], 3);
  assert_eq!(reverted["retainedClaims"], 2);
  assert_eq!(reverted["reusedBaseRoot"], true);
  assert_eq!(reverted["newProofs"], 0);
  assert_eq!(reverted["rootProof"], report["rootProof"]);
  assert_eq!(
    runner.calls.iter().map(|c| c[0].as_str()).collect::<Vec<_>>(),
    ["verify", "verify"]
  );
  assert!(runner.proved_claims.is_empty());
  let reverted_record = read_json(&revert.catalog.join(RECORD)).unwrap();
  assert_eq!(reverted_record["leaves"], record["leaves"]);
  assert_ne!(reverted_record["snapshotHash"], record["snapshotHash"]);

  fs::remove_dir_all(&options.catalog).unwrap();
  let subset = Env::new();
  insert(&subset, definition(1, None));
  let mut deletion = fixture.options(fixture.catalog("D", &subset));
  deletion.base = Some(revert.catalog);
  runner.calls.clear();
  let deleted = execute(&deletion, &fixture.store, &mut runner).unwrap();
  assert_eq!(deleted["snapshotSubjects"], 1);
  assert_eq!(deleted["corpusSubjects"], 3);
  assert_eq!(deleted["rootProof"], report["rootProof"]);
  assert_eq!(deleted["reusedBaseRoot"], true);
  assert_eq!(deleted["newProofs"], 0);
  assert!(runner.calls.iter().all(|call| call[0] == "verify"));
  assert!(runner.proved_claims.is_empty());
  deletion.base = None;
  deletion.verify_only = true;
  assert_eq!(
    execute(&deletion, &fixture.store, &mut runner).unwrap()["status"],
    "verified"
  );
}

#[test]
fn unavailable_base_leaf_is_recovered_instead_of_publishing_a_broken_reference()
{
  for corrupt in [false, true] {
    let fixture = Fixture::new();
    let env = Env::new();
    insert(&env, definition(0, None));
    insert(&env, definition(1, None));
    let mut baseline = fixture.options(fixture.catalog("A", &env));
    baseline.shards = 2;
    baseline.lanes = 2;
    let mut runner = fixture.runner();
    execute(&baseline, &fixture.store, &mut runner).unwrap();
    let record = read_json(&baseline.catalog.join(RECORD)).unwrap();
    let missing =
      address(string(&record["leaves"][0], "proof").unwrap()).unwrap();
    let path = runner.proof_path(&missing);
    if corrupt {
      fs::write(&path, b"corrupted proof").unwrap();
    } else {
      fs::remove_file(&path).unwrap();
    }
    let mut next = fixture.options(fixture.catalog("B", &env));
    next.base = Some(baseline.catalog);
    next.lanes = 2;
    runner.calls.clear();
    runner.proved_claims.clear();
    runner.reused_claims.clear();
    let report = execute(&next, &fixture.store, &mut runner).unwrap();
    assert_eq!(report["status"], "certified");
    assert_eq!(report["reusedBaseRoot"], false);
    assert_eq!(report["newClaims"], 0);
    assert_eq!(
      runner.proved_claims,
      vec![address(string(&record["leaves"][0], "claim").unwrap()).unwrap()]
    );
    assert_eq!(runner.reused_claims.len(), 1);
    assert_eq!(Address::hash(&read(&path).unwrap()), missing);
  }
}

#[test]
fn an_added_projection_requires_a_new_claim_for_its_mutual_block() {
  let fixture = Fixture::new();
  let old = Env::new();
  let ConstantInfo::Defn(defn) = definition(0, None).info else {
    unreachable!()
  };
  let block =
    insert(&old, Constant::new(ConstantInfo::Muts(vec![MutConst::Defn(defn)])));
  let before = fixture.options(fixture.catalog("A", &old));
  let mut runner = fixture.runner();
  execute(&before, &fixture.store, &mut runner).unwrap();
  let new = copy_env(&old);
  insert(
    &new,
    Constant::new(ConstantInfo::DPrj(DefinitionProj { idx: 0, block })),
  );
  let mut options = fixture.options(fixture.catalog("B", &new));
  options.base = Some(before.catalog);
  runner.proved_claims.clear();
  runner.reused_claims.clear();
  let report = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(report["newSubjects"], 1);
  assert_eq!(report["retainedClaims"], 0);
  assert_eq!(report["changedBaseClaims"], 1);
  assert_eq!(report["newClaims"], 1);
  assert_eq!(report["subjectsInNewClaims"], 2);
  assert_eq!(report["claims"][0]["retainedFromBase"], false);
  assert_eq!(report["reusedBaseRoot"], false);
  assert_eq!(runner.proved_claims.len(), 1);
  assert!(runner.reused_claims.is_empty());
}

#[test]
fn failed_aggregation_and_verification_never_publish_a_certificate() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let options = fixture.options(fixture.catalog("A", &env));
  let mut runner = fixture.runner();
  runner.fail = Some("aggregate".into());
  assert!(execute(&options, &fixture.store, &mut runner).is_err());
  assert!(!options.catalog.join(RECORD).exists());
  runner.fail = Some("verify".into());
  assert!(execute(&options, &fixture.store, &mut runner).is_err());
  assert!(!options.catalog.join(RECORD).exists());
  runner.fail = None;
  assert_eq!(
    execute(&options, &fixture.store, &mut runner).unwrap()["status"],
    "certified"
  );
}

#[test]
fn pin_tampering_and_incompatible_backend_are_rejected() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let options = fixture.options(fixture.catalog("A", &env));
  let mut runner = fixture.runner();
  execute(&options, &fixture.store, &mut runner).unwrap();
  fs::write(&fixture.executable, b"different checker").unwrap();
  assert!(
    execute(&options, &fixture.store, &mut runner)
      .err()
      .unwrap()
      .contains("incompatible proving profile")
  );
  let mut next = fixture.options(fixture.catalog("B", &env));
  next.base = Some(options.catalog.clone());
  runner.calls.clear();
  assert!(
    execute(&next, &fixture.store, &mut runner)
      .unwrap_err()
      .contains("incompatible proving profile")
  );
  assert!(runner.calls.is_empty());
  assert!(!next.catalog.join(RECORD).exists());
  fs::write(&fixture.executable, b"fixture backend identity").unwrap();
  let mut catalog = catalog::load_dir(&options.catalog).unwrap();
  catalog.members[0].source_pin = "git:fixture@forged".into();
  catalog::write_manifest(&options.catalog, &catalog).unwrap();
  assert!(
    execute(&options, &fixture.store, &mut runner)
      .err()
      .unwrap()
      .contains("does not bind")
  );
}

#[test]
fn axioms_require_explicit_policy_and_cannot_expand_in_a_delta() {
  let fixture = Fixture::new();
  let env = Env::new();
  let a = insert(
    &env,
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Expr::sort(0),
    })),
  );
  let mut options = fixture.options(fixture.catalog("A", &env));
  let mut runner = fixture.runner();
  assert!(
    execute(&options, &fixture.store, &mut runner)
      .err()
      .unwrap()
      .contains("unapproved axiom")
  );
  assert!(runner.calls.is_empty());
  let policy = fixture.dir.join("axioms.txt");
  fs::write(&policy, format!("# reviewed\n{}\n", a.hex())).unwrap();
  options.allow_axioms = Some(policy);
  execute(&options, &fixture.store, &mut runner).unwrap();
  let new = copy_env(&env);
  insert(
    &new,
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 1,
      typ: Expr::sort(0),
    })),
  );
  let mut delta = fixture.options(fixture.catalog("B", &new));
  delta.base = Some(options.catalog);
  assert!(
    execute(&delta, &fixture.store, &mut runner)
      .err()
      .unwrap()
      .contains("unapproved axiom")
  );
  assert!(!delta.catalog.join(RECORD).exists());
}

#[test]
fn record_coverage_tampering_is_rejected_before_backend_verification() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let options = fixture.options(fixture.catalog("A", &env));
  let mut runner = fixture.runner();
  execute(&options, &fixture.store, &mut runner).unwrap();
  let mut record = read_json(&options.catalog.join(RECORD)).unwrap();
  record["leaves"][0]["subjects"] = json!([]);
  write_json(&options.catalog.join(RECORD), &record).unwrap();
  runner.calls.clear();
  assert!(execute(&options, &fixture.store, &mut runner).is_err());
  assert!(runner.calls.is_empty());
}

#[test]
fn corrupted_root_and_partition_are_rejected_before_backend_verification() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let options = fixture.options(fixture.catalog("A", &env));
  let mut runner = fixture.runner();
  execute(&options, &fixture.store, &mut runner).unwrap();
  let record = read_json(&options.catalog.join(RECORD)).unwrap();
  let hex = string(&record, "rootProof").unwrap();
  let proof = fixture
    .store
    .join("store")
    .join(&hex[..2])
    .join(&hex[2..4])
    .join(&hex[4..6])
    .join(&hex[6..]);
  let original = read(&proof).unwrap();
  fs::write(&proof, b"corrupted").unwrap();
  runner.calls.clear();
  assert!(
    execute(&options, &fixture.store, &mut runner)
      .unwrap_err()
      .contains("wrong hash")
  );
  assert!(runner.calls.is_empty());
  fs::write(proof, original).unwrap();
  let manifest_path = options
    .catalog
    .join("proving")
    .join(digest_json(&record["profile"]).hex())
    .join("shards.ixes");
  let mut manifest =
    ShardManifest::from_bytes(&read(&manifest_path).unwrap()).unwrap();
  manifest.shards[0].measured_peak_bytes = 1;
  fs::write(manifest_path, manifest.to_bytes()).unwrap();
  assert!(
    execute(&options, &fixture.store, &mut runner)
      .unwrap_err()
      .contains("corpus or partition changed")
  );
  assert!(runner.calls.is_empty());
}

#[test]
fn recipient_must_supply_nonempty_axiom_policy_independently() {
  let fixture = Fixture::new();
  let env = Env::new();
  let axiom = insert(
    &env,
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Expr::sort(0),
    })),
  );
  let policy = fixture.dir.join("axioms.txt");
  fs::write(&policy, format!("{}\n", axiom.hex())).unwrap();
  let mut options = fixture.options(fixture.catalog("A", &env));
  options.allow_axioms = Some(policy.clone());
  let mut runner = fixture.runner();
  execute(&options, &fixture.store, &mut runner).unwrap();
  options.verify_only = true;
  options.allow_axioms = None;
  runner.calls.clear();
  assert!(
    execute(&options, &fixture.store, &mut runner)
      .unwrap_err()
      .contains("independently reviewed")
  );
  assert!(runner.calls.is_empty());
  options.allow_axioms = Some(policy);
  assert_eq!(
    execute(&options, &fixture.store, &mut runner).unwrap()["status"],
    "verified"
  );
}

#[test]
fn exclusive_catalog_lock_blocks_a_second_driver() {
  let fixture = Fixture::new();
  let env = Env::new();
  insert(&env, definition(0, None));
  let options = fixture.options(fixture.catalog("A", &env));
  let lock = fs::OpenOptions::new()
    .read(true)
    .write(true)
    .create(true)
    .truncate(false)
    .open(options.catalog.join(".proving.lock"))
    .unwrap();
  lock.try_lock().unwrap();
  assert!(
    execute(&options, &fixture.store, &mut fixture.runner())
      .err()
      .unwrap()
      .contains("already being processed")
  );
}

#[test]
fn address_parser_rejects_non_ascii_without_panicking() {
  assert!(address(&"é".repeat(32)).is_err());
  assert!(
    Options::from_json(
      &json!({"catalog": "C.ixc", "executable": "ix", "shards": -1})
    )
    .is_err()
  );
}
