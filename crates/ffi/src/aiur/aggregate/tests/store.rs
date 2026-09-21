use std::{
  fs,
  path::PathBuf,
  sync::atomic::{AtomicUsize, Ordering},
};

use aiur::{
  G,
  bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Toplevel},
  execute::IOBuffer,
  synthesis::{AiurProof, AiurSystem},
};
use multi_stark::{
  p3_field::PrimeCharacteristicRing,
  types::{CommitmentParameters, FriParameters},
};

use super::super::{
  plan::{PlanOp, SlotSpec},
  protocol::{ChildKind, aggregate_outer_claim},
  statement::{ShardSet, Statement, SubjectTree},
  store::{load_cached, persist_cached, store_path, write_store},
};
use super::addr;

struct Fixture {
  root: PathBuf,
  store: PathBuf,
  cache: PathBuf,
  system: AiurSystem,
  spec: SlotSpec,
  proof: AiurProof,
}

impl Fixture {
  fn new() -> Self {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let root = std::env::temp_dir().join(format!(
      "ix-aggregate-cache-{}-{}",
      std::process::id(),
      NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&root).unwrap();
    let store = root.join("store");
    let cache = root.join("cache");
    let layout = FunctionLayout {
      input_size: 16,
      selectors: 1,
      auxiliaries: 1,
      lookups: 1,
    };
    let top = Toplevel {
      functions: vec![Function {
        body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) },
        layout,
        entry: true,
        constrained: true,
      }],
      circuits: vec![Circuit { members: vec![0], layout }],
      memory_sizes: vec![],
    };
    let system = AiurSystem::build(
      top,
      CommitmentParameters { log_blowup: 1, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 2,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    );
    let subjects = SubjectTree::canonical(
      vec![addr("cache-subject")],
      ShardSet::singleton(0, 1),
    )
    .unwrap();
    let statement = Statement::new(subjects, None);
    let outer_claim =
      aggregate_outer_claim(0, b"test-identity", &statement.claim_bytes);
    let spec = SlotSpec {
      op: PlanOp::Leaf(0),
      statement,
      subject_count: 1,
      structural: false,
      kind: ChildKind::Aggr,
      shape: Some(0),
      outer_claim,
      cache_key: addr("cache-key"),
      ram_bytes: 1,
    };
    let (claim, proof) = system.prove(
      0,
      &spec.outer_claim[2..],
      &mut IOBuffer { data: Default::default(), map: Default::default() },
    );
    assert_eq!(claim, spec.outer_claim);
    system.verify(&claim, &proof).unwrap();
    Self { root, store, cache, system, spec, proof }
  }

  fn load(&self) -> Option<(AiurProof, ix_common::address::Address)> {
    load_cached(&self.system, &self.store, Some(&self.cache), 0, &self.spec)
  }

  fn persist(&self) -> ix_common::address::Address {
    persist_cached(
      &self.store,
      Some(&self.cache),
      true,
      0,
      &self.spec,
      &self.proof,
    )
    .unwrap()
  }

  fn replace_wrapper(&self, wrapper: &ixon::Proof) {
    let mut bytes = Vec::new();
    wrapper.put(&mut bytes);
    let address = write_store(&self.store, &bytes).unwrap();
    fs::create_dir_all(&self.cache).unwrap();
    fs::write(self.cache.join(self.spec.cache_key.hex()), address.hex())
      .unwrap();
  }
}

impl Drop for Fixture {
  fn drop(&mut self) {
    fs::remove_dir_all(&self.root).unwrap();
  }
}

#[test]
fn verified_cache_reuse_and_atomic_index_replacement() {
  let fixture = Fixture::new();
  assert!(fixture.load().is_none());
  let address = fixture.persist();
  let (proof, loaded_address) = fixture.load().expect("verified hit");
  assert_eq!(address, loaded_address);
  fixture.system.verify(&fixture.spec.outer_claim, &proof).unwrap();
  fs::write(fixture.cache.join(fixture.spec.cache_key.hex()), "corrupt")
    .unwrap();
  assert!(fixture.load().is_none());
  assert_eq!(fixture.persist(), address);
  assert!(fixture.load().is_some());
  assert_eq!(fs::read_dir(&fixture.cache).unwrap().count(), 1);
}

#[test]
fn cache_rejects_missing_and_corrupt_content() {
  let fixture = Fixture::new();
  let address = fixture.persist();
  let path = store_path(&fixture.store, &address);
  fs::write(&path, b"wrong content address").unwrap();
  assert!(fixture.load().is_none());
  fs::remove_file(&path).unwrap();
  assert!(fixture.load().is_none());
}

#[test]
fn cache_rejects_wrong_statement_and_malformed_proof() {
  let fixture = Fixture::new();
  let subjects =
    SubjectTree::canonical(vec![addr("other")], ShardSet::singleton(0, 1))
      .unwrap();
  let other = Statement::new(subjects, None);
  fixture.replace_wrapper(&ixon::Proof::new(
    other.claim.clone(),
    fixture.proof.to_bytes().unwrap(),
  ));
  assert!(fixture.load().is_none());
  fixture.replace_wrapper(&ixon::Proof::new(
    fixture.spec.statement.claim.clone(),
    vec![0xff],
  ));
  assert!(fixture.load().is_none());
}

#[test]
fn cache_verifies_the_proof_even_when_wrapper_and_content_address_match() {
  let fixture = Fixture::new();
  let mut input = fixture.spec.outer_claim[2..].to_vec();
  input[0] += G::ONE;
  let (other_claim, other_proof) = fixture.system.prove(
    0,
    &input,
    &mut IOBuffer { data: Default::default(), map: Default::default() },
  );
  fixture.system.verify(&other_claim, &other_proof).unwrap();
  assert!(
    fixture.system.verify(&fixture.spec.outer_claim, &other_proof).is_err()
  );
  fixture.replace_wrapper(&ixon::Proof::new(
    fixture.spec.statement.claim.clone(),
    other_proof.to_bytes().unwrap(),
  ));
  assert!(fixture.load().is_none());
}

#[test]
fn no_write_and_disabled_cache_leave_no_artifacts() {
  let fixture = Fixture::new();
  assert!(
    persist_cached(
      &fixture.store,
      Some(&fixture.cache),
      false,
      0,
      &fixture.spec,
      &fixture.proof
    )
    .is_none()
  );
  assert!(
    persist_cached(
      &fixture.store,
      None,
      true,
      0,
      &fixture.spec,
      &fixture.proof
    )
    .is_none()
  );
  assert!(!fixture.store.exists());
  assert!(!fixture.cache.exists());
  fixture.persist();
  assert!(
    load_cached(&fixture.system, &fixture.store, None, 0, &fixture.spec)
      .is_none()
  );
  assert!(fixture.load().is_some());
}
