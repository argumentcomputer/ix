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
      trace_shards: false,
      plan_only: false,
      verify_only: false,
    }
  }

  fn runner(&self) -> Backend {
    Backend { store: self.store.clone(), calls: Vec::new(), fail: None }
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
  fail: Option<String>,
}

impl Backend {
  fn save(&self, claim: ixon::Claim, marker: u8) -> Address {
    let wrapper = ixon::Proof::new(claim, vec![marker]);
    let mut bytes = Vec::new();
    wrapper.put(&mut bytes);
    let address = Address::hash(&bytes);
    let hex = address.hex();
    let path = self
      .store
      .join("store")
      .join(&hex[..2])
      .join(&hex[2..4])
      .join(&hex[4..6])
      .join(&hex[6..]);
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
        Ok(
          leaves
            .into_iter()
            .map(|leaf| {
              let (claim, _) =
                ixon::shard_claim::shard_check_env_claim(&env, &leaf.subjects)
                  .unwrap();
              self.save(claim, 1)
            })
            .collect(),
        )
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
fn subsequent_commit_preserves_history_and_revert_has_no_new_subjects() {
  let fixture = Fixture::new();
  let old = Env::new();
  let a = insert(&old, definition(0, None));
  let old_options = fixture.options(fixture.catalog("A", &old));
  let mut runner = fixture.runner();
  execute(&old_options, &fixture.store, &mut runner).unwrap();
  let new = copy_env(&old);
  insert(&new, definition(1, Some(a)));
  let mut options = fixture.options(fixture.catalog("B", &new));
  options.base = Some(old_options.catalog.clone());
  let report = execute(&options, &fixture.store, &mut runner).unwrap();
  assert_eq!(report["newSubjects"], 1);
  assert_eq!(report["retainedClaims"], 1);
  let mut revert = fixture.options(fixture.catalog("C", &old));
  revert.base = Some(options.catalog.clone());
  revert.plan_only = true;
  let report = execute(&revert, &fixture.store, &mut runner).unwrap();
  assert_eq!(report["newSubjects"], 0);
  assert_eq!(report["snapshotSubjects"], 1);
  assert_eq!(report["corpusSubjects"], 2);
  assert_eq!(report["retainedClaims"], 2);
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
