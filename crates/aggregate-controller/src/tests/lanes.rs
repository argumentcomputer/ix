//! The lane controller end to end over a fake backend: plans, resumption,
//! the cache and index switches, contention requeues, bisection and root
//! wrapping, with no prover.

use std::{
  fs,
  path::{Path, PathBuf},
  sync::{
    Arc, Mutex,
    atomic::{AtomicU64, Ordering},
  },
};

use ix_common::address::Address;
use ixon::Expr;
use ixon::shard::{AggNode, ShardManifest};
use record_pool::RecordReservation;
use rustc_hash::FxHashSet;

use super::{shard, store_axiom};
use crate::{
  Backend, BackendSlot, ExtraNode, Identity, PrepareFailure, ProvenClaim, Run,
  aggregate,
  discharge::{BindingSource, binding_claim},
  lanes::{self, Config},
  plan::PlanOp,
  protocol::ChildKind,
  statement::{ShardSet, Statement, SubjectTree},
  store::{claim_wrapper_bytes, load_cached, persist_cached},
};

static NEXT_DIR: AtomicU64 = AtomicU64::new(0);

/// A fresh directory under the system temporary directory, removed on drop.
struct TempDir(PathBuf);

impl TempDir {
  fn new() -> Self {
    let path = std::env::temp_dir().join(format!(
      "ix-lanes-test-{}-{}",
      std::process::id(),
      NEXT_DIR.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&path).unwrap();
    Self(path)
  }
}

impl Drop for TempDir {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.0);
  }
}

#[derive(Clone, Debug, PartialEq)]
struct FakeProof {
  outer: Vec<u64>,
  shards: usize,
}

enum Staged {
  Cached(FakeProof, Address),
  Executed,
}

/// Proves by naming the outer claim. Every execution is logged; a claim's
/// execution over `oversized` or more constants exceeds the record ceiling,
/// and the first execution of a claim whose first constant is in `contend`
/// loses a memory contest.
struct Fake {
  log: Mutex<Vec<String>>,
  contend: Mutex<FxHashSet<Address>>,
  oversized: usize,
  root_shards: usize,
}

impl Fake {
  fn new() -> Self {
    Self {
      log: Mutex::new(Vec::new()),
      contend: Mutex::new(FxHashSet::default()),
      oversized: usize::MAX,
      root_shards: 1,
    }
  }

  fn record(&self, entry: String) {
    self.log.lock().unwrap().push(entry);
  }

  fn entries(&self, prefix: &str) -> usize {
    self.log.lock().unwrap().iter().filter(|e| e.starts_with(prefix)).count()
  }

  fn clear(&self) {
    self.log.lock().unwrap().clear();
  }
}

impl Identity for Fake {
  type Claim = Vec<u64>;

  fn outer_claim(&self, kind: ChildKind, claim_bytes: &[u8]) -> Vec<u64> {
    let digest = blake3::hash(claim_bytes);
    let mut outer = vec![u64::from(kind.code())];
    outer.extend(
      digest
        .as_bytes()
        .as_chunks::<8>()
        .0
        .iter()
        .map(|w| u64::from_le_bytes(*w)),
    );
    outer
  }

  fn claims_bytes(&self, outer: &Vec<u64>) -> Vec<u8> {
    outer.iter().flat_map(|w| w.to_le_bytes()).collect()
  }

  fn cache_key(&self, outer: &Vec<u64>) -> Address {
    Address::hash(&self.claims_bytes(outer))
  }
}

impl Backend for Fake {
  type Lane = usize;
  type Proof = FakeProof;
  type ClaimRecord = (ixon::Claim, Vec<u8>);
  type Staged = Staged;
  type Binding = ();

  fn lanes(&self, count: usize) -> Result<Vec<usize>, String> {
    Ok((0..count).collect())
  }

  fn lane_workspace_bytes(&self, _cells: usize) -> Option<usize> {
    Some(1 << 20)
  }

  fn resident_bytes(&self) -> usize {
    1 << 20
  }

  fn bind(&self, _reservation: &RecordReservation) {}

  fn execute_claim(
    &self,
    _lane: &usize,
    _env: &ixon::Env,
    owned: &[Address],
    expected: &ixon::Claim,
    _budget: Option<usize>,
    _reservation: &RecordReservation,
  ) -> Result<Self::ClaimRecord, PrepareFailure> {
    self.record(format!("claim {}", owned.len()));
    if owned.len() >= self.oversized {
      return Err(PrepareFailure::OverRecordCap { bytes: 2, cap: 1 });
    }
    if self.contend.lock().unwrap().remove(&owned[0]) {
      return Err(PrepareFailure::MemoryContention);
    }
    let subjects =
      SubjectTree::canonical(owned.to_vec(), ShardSet::singleton(0, 1))?;
    let ctx = expected.context().ok_or("expected a CheckEnv claim")?;
    let statement = Statement::new(ctx.clone(), subjects, None);
    if &statement.claim != expected {
      return Err("the claim differs from the controller's statement".into());
    }
    Ok((statement.claim.clone(), statement.claim_bytes.clone()))
  }

  fn execute_aggregate(
    &self,
    lane: &usize,
    run: Run<'_, Vec<u64>>,
    slot: usize,
    children: &[Arc<BackendSlot<Self>>],
    _reservation: &RecordReservation,
  ) -> Result<Staged, PrepareFailure> {
    let spec = &run.specs[slot];
    let PlanOp::Join(left, right) = spec.op else {
      return Err("a leaf slot reached aggregation".into());
    };
    for (child, index) in children.iter().zip([left, right]) {
      if child.outer_claim != run.specs[index].outer_claim
        || child.proof.outer != child.outer_claim
      {
        return Err(
          format!("slot {slot}: child {index} is not its spec").into(),
        );
      }
    }
    if let Some((proof, address)) = load_cached(
      run.store_dir,
      run.cache_dir,
      slot,
      spec,
      |bytes| self.decode_proof(bytes),
      |outer, proof| self.verify_on(lane, ChildKind::Aggr, outer, proof),
    ) {
      return Ok(Staged::Cached(proof, address));
    }
    self.record(format!("aggregate {slot} shape {}", spec.shape.unwrap()));
    Ok(Staged::Executed)
  }

  fn prove_claim(
    &self,
    _lane: &usize,
    (claim, claim_bytes): Self::ClaimRecord,
  ) -> Result<ProvenClaim<FakeProof>, String> {
    let outer = self.outer_claim(ChildKind::Ixvm, &claim_bytes);
    Ok(ProvenClaim {
      claim,
      claim_bytes,
      proof: FakeProof { outer, shards: 1 },
    })
  }

  fn prove_aggregate(
    &self,
    _lane: &usize,
    run: Run<'_, Vec<u64>>,
    slot: usize,
    staged: Staged,
  ) -> Result<Arc<BackendSlot<Self>>, String> {
    let spec = &run.specs[slot];
    let (proof, proof_address) = match staged {
      Staged::Cached(proof, address) => (proof, Some(address)),
      Staged::Executed => {
        let shards =
          if slot + 1 == run.specs.len() { self.root_shards } else { 1 };
        let proof = FakeProof { outer: spec.outer_claim.clone(), shards };
        let address = persist_cached(
          run.store_dir,
          run.cache_dir,
          run.write_outputs,
          slot,
          spec,
          || self.encode_proof(&proof),
        )?;
        (proof, address)
      },
    };
    Ok(Arc::new(BackendSlot::<Self> {
      kind: ChildKind::Aggr,
      statement: spec.statement.clone(),
      outer_claim: spec.outer_claim.clone(),
      proof,
      proof_address,
      claims_bytes: self.claims_bytes(&spec.outer_claim),
    }))
  }

  fn wrap_root(
    &self,
    _lane: &usize,
    _run: Run<'_, Vec<u64>>,
    root: &BackendSlot<Self>,
    proof: &FakeProof,
    _reservation: &RecordReservation,
  ) -> Result<FakeProof, String> {
    self.record(format!("wrap {}", proof.shards));
    Ok(FakeProof { outer: root.outer_claim.clone(), shards: proof.shards / 2 })
  }

  fn prove_extra(
    &self,
    _lane: &usize,
    node: ExtraNode<'_, FakeProof>,
    _reservation: &RecordReservation,
  ) -> Result<FakeProof, String> {
    let children = match &node {
      ExtraNode::Discharge { child, binding, .. } => [child, binding],
      ExtraNode::Catalog { children, .. } => [&children[0], &children[1]],
    };
    for child in children {
      let outer = self.outer_claim(child.kind, child.claim_bytes);
      if child.proof.outer != outer {
        return Err("an extra node's child is not its claim's proof".into());
      }
    }
    self.record(format!("extra {}", node.output().len()));
    Ok(FakeProof {
      outer: self.outer_claim(ChildKind::Aggr, node.output()),
      shards: 1,
    })
  }

  fn verify(
    &self,
    _kind: ChildKind,
    outer: &Vec<u64>,
    proof: &FakeProof,
  ) -> Result<(), String> {
    if &proof.outer == outer { Ok(()) } else { Err("wrong claim".into()) }
  }

  fn verify_on(
    &self,
    _lane: &usize,
    kind: ChildKind,
    outer: &Vec<u64>,
    proof: &FakeProof,
  ) -> Result<(), String> {
    self.verify(kind, outer, proof)
  }

  fn trace_shards(&self, proof: &FakeProof) -> usize {
    proof.shards
  }

  fn encode_proof(&self, proof: &FakeProof) -> Result<Vec<u8>, String> {
    let mut bytes = (proof.shards as u64).to_le_bytes().to_vec();
    bytes.extend(proof.outer.iter().flat_map(|w| w.to_le_bytes()));
    Ok(bytes)
  }

  fn decode_proof(&self, bytes: &[u8]) -> Result<FakeProof, String> {
    let (words, rest) = bytes.as_chunks::<8>();
    if !rest.is_empty() || words.is_empty() {
      return Err("malformed fake proof".into());
    }
    let mut words = words.iter().map(|w| u64::from_le_bytes(*w));
    let shards = usize::try_from(words.next().unwrap()).unwrap();
    Ok(FakeProof { outer: words.collect(), shards })
  }
}

/// An environment of `blocks.iter().sum()` axioms, one block each, and a
/// balanced manifest whose shard `i` owns `blocks[i]` of them.
fn environment(blocks: &[usize], dir: &Path) -> (ixon::Env, PathBuf) {
  let mut env = ixon::Env::new();
  let binding: Arc<[u8]> = b"test role binding".as_slice().into();
  env.role_binding = Some(ixon::env::RoleBinding {
    address: Address::hash(&binding),
    bytes: binding,
  });
  let mut next = 0u64;
  let shards: Vec<_> = blocks
    .iter()
    .enumerate()
    .map(|(id, &count)| {
      let mut info = shard(u32::try_from(id).unwrap(), Address::hash(b"none"));
      info.blocks = (0..count)
        .map(|_| {
          next += 1;
          store_axiom(&env, Expr::sort(next), vec![])
        })
        .collect();
      info
    })
    .collect();
  fn balanced(ids: &[u32]) -> AggNode {
    if ids.len() == 1 {
      return AggNode::Leaf(ids[0]);
    }
    let (left, right) = ids.split_at(ids.len() / 2);
    AggNode::Internal(Box::new(balanced(left)), Box::new(balanced(right)))
  }
  let ids: Vec<u32> = shards.iter().map(|s| s.id).collect();
  let manifest = ShardManifest {
    num_shards: u32::try_from(shards.len()).unwrap(),
    shards,
    total_cross_ingress: 0,
    tree: Some(balanced(&ids)),
  };
  let path = dir.join("env.ixes");
  fs::write(&path, manifest.to_bytes()).unwrap();
  (env, path)
}

fn config(dir: &Path) -> Config {
  Config {
    store_dir: Some(dir.join("store")),
    cache_root: Some(dir.join("cache")),
    ..Config::new(1, 1 << 30, 2, 0)
  }
}

#[test]
fn direct_plan_proves_resumes_and_honours_the_switches() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1, 1, 1], &dir.0);
  let mut backend = Fake::new();
  backend.root_shards = 4;
  let cfg = config(&dir.0);
  let root = lanes::run(&cfg, &backend, &env, &manifest).unwrap();
  // Four claims, two structural joins of raw claims (shape 6), and the
  // root over two aggregates (shape 9), wrapped from four shards to one.
  assert_eq!(backend.entries("claim"), 4);
  let log = backend.log.lock().unwrap().clone();
  let shapes: Vec<&str> = log
    .iter()
    .filter_map(|e| e.strip_prefix("aggregate "))
    .map(|e| e.rsplit(' ').next().unwrap())
    .collect();
  assert_eq!(shapes, ["6", "6", "9"]);
  assert_eq!(backend.entries("wrap"), 2);

  // A rerun reuses the indexed claims, the cached joins and the cached
  // unwrapped root; only the root wraps run again, to the same root.
  backend.clear();
  assert_eq!(lanes::run(&cfg, &backend, &env, &manifest).unwrap(), root);
  assert_eq!(backend.entries("claim"), 0);
  assert_eq!(backend.entries("aggregate"), 0);
  assert_eq!(backend.entries("wrap"), 2);

  // Without the index and the cache everything executes again.
  backend.clear();
  let cold = Config { use_cache: false, use_index: false, ..config(&dir.0) };
  assert_eq!(lanes::run(&cold, &backend, &env, &manifest).unwrap(), root);
  assert_eq!(backend.entries("claim"), 4);
  assert_eq!(backend.entries("aggregate"), 3);
}

#[test]
fn switches_off_write_no_index_or_cache_entries() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1, 1], &dir.0);
  let backend = Fake::new();
  let cold = Config { use_cache: false, use_index: false, ..config(&dir.0) };
  lanes::run(&cold, &backend, &env, &manifest).unwrap();
  assert!(!dir.0.join("cache").join("aggregate").exists());
  assert!(!dir.0.join("cache").join("formal-shard-proofs").exists());
  backend.clear();
  lanes::run(&cold, &backend, &env, &manifest).unwrap();
  assert_eq!(backend.entries("claim"), 3);
}

#[test]
fn a_contended_claim_is_requeued() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1, 1], &dir.0);
  let backend = Fake::new();
  let parsed =
    ShardManifest::from_bytes(&fs::read(&manifest).unwrap()).unwrap();
  backend.contend.lock().unwrap().insert(parsed.shards[1].blocks[0].clone());
  lanes::run(&config(&dir.0), &backend, &env, &manifest).unwrap();
  assert_eq!(backend.entries("claim"), 4);
  assert!(backend.contend.lock().unwrap().is_empty());
}

#[test]
fn an_oversized_claim_is_bisected_and_checkpointed() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 2, 1], &dir.0);
  let mut backend = Fake::new();
  backend.oversized = 2;
  let out = dir.0.join("proven.ixes");
  let cfg = Config { out_manifest: Some(out.clone()), ..config(&dir.0) };
  lanes::run(&cfg, &backend, &env, &manifest).unwrap();
  let proven = ShardManifest::from_bytes(&fs::read(&out).unwrap()).unwrap();
  assert_eq!(proven.shards.len(), 4);
  assert!(proven.shards.iter().all(|s| s.blocks.len() == 1));
  let checkpoints = fs::read_dir(dir.0.join("cache").join("refined-manifests"))
    .unwrap()
    .count();
  assert_eq!(checkpoints, 1);
  // A single-block claim over the ceiling cannot be split.
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1], &dir.0);
  let mut backend = Fake::new();
  backend.oversized = 1;
  let error =
    lanes::run(&config(&dir.0), &backend, &env, &manifest).unwrap_err();
  assert!(error.contains("cannot be split further"), "{error}");
}

#[test]
fn wrap_first_folds_are_rejected() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1], &dir.0);
  let mut cfg = config(&dir.0);
  cfg.fold.direct_joins = false;
  let error = lanes::run(&cfg, &Fake::new(), &env, &manifest).unwrap_err();
  assert!(error.contains("wrap-first"), "{error}");
}

#[test]
fn claims_only_runs_prove_the_selection_and_its_parts() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 2, 1], &dir.0);
  let mut backend = Fake::new();
  backend.oversized = 2;
  let parsed =
    ShardManifest::from_bytes(&fs::read(&manifest).unwrap()).unwrap();
  let wide = parsed.shards.iter().find(|s| s.blocks.len() == 2).unwrap().id;
  let cfg =
    Config { claims_only: true, select: Some(vec![wide]), ..config(&dir.0) };
  let lines = lanes::run(&cfg, &backend, &env, &manifest).unwrap();
  // The oversized claim was split; both parts, and nothing else, proved.
  assert_eq!(lines.lines().count(), 2);
  assert_eq!(backend.entries("aggregate"), 0);
  assert_eq!(backend.entries("claim 1"), 2);
  assert_eq!(backend.entries("claim 2"), 1);
  // Resuming from the refined checkpoint keeps both parts selected, now
  // served from the index.
  backend.clear();
  let resumed = lanes::run(&cfg, &backend, &env, &manifest).unwrap();
  assert_eq!(resumed, lines);
  assert_eq!(backend.entries("claim"), 0);
  // Every claim of a one-claim manifest, with nothing to join.
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1], &dir.0);
  let cfg = Config { claims_only: true, ..config(&dir.0) };
  let lines = lanes::run(&cfg, &Fake::new(), &env, &manifest).unwrap();
  assert_eq!(lines.lines().count(), 1);
}

fn aggregate_config(dir: &Path) -> aggregate::Config {
  aggregate::Config {
    lanes: 1,
    exec_ahead: 0,
    structural_above: 0,
    reprove_slot: None,
    subtree: None,
    plan_only: false,
    use_cache: true,
    write_outputs: false,
    wrap_root: false,
    assume_binding: false,
    binding_proof: None,
    store_dir: Some(dir.join("store")),
    cache_dir: Some(dir.join("cache").join("aggregate")),
  }
}

/// The aggregate cache's entries: cache key file and the proof it names.
fn cache_entries(dir: &Path) -> Vec<(PathBuf, String)> {
  fs::read_dir(dir.join("cache").join("aggregate"))
    .unwrap()
    .map(|entry| {
      let path = entry.unwrap().path();
      let address = fs::read_to_string(&path).unwrap().trim().to_string();
      (path, address)
    })
    .collect()
}

#[test]
fn standalone_aggregation_needs_claim_proofs_only_below_known_joins() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1, 1, 1], &dir.0);
  let backend = Fake::new();
  let root = lanes::run(&config(&dir.0), &backend, &env, &manifest).unwrap();
  let cfg = aggregate_config(&dir.0);

  // A cached root needs no claim proofs and proves nothing.
  backend.clear();
  let output =
    aggregate::run(&cfg, &backend, &env, &manifest, "").unwrap().unwrap();
  assert_eq!(output.address.hex(), root);
  assert_eq!(backend.entries("aggregate"), 0);

  // Supplied aggregate proofs stand in for the cache.
  let entries = cache_entries(&dir.0);
  assert_eq!(entries.len(), 3);
  let supplied: Vec<&str> = entries.iter().map(|(_, a)| a.as_str()).collect();
  let cold = aggregate::Config { use_cache: false, ..aggregate_config(&dir.0) };
  let output =
    aggregate::run(&cold, &backend, &env, &manifest, &supplied.join("\n"))
      .unwrap()
      .unwrap();
  assert_eq!(output.address.hex(), root);
  assert_eq!(backend.entries("aggregate"), 0);

  // Without the root entry, its two cached children are joined again.
  let (root_entry, _) =
    entries.iter().find(|(_, address)| *address == root).unwrap();
  fs::remove_file(root_entry).unwrap();
  let output =
    aggregate::run(&cfg, &backend, &env, &manifest, "").unwrap().unwrap();
  assert_eq!(output.address.hex(), root);
  assert_eq!(backend.entries("aggregate"), 1);

  // With nothing cached, every claim proof is required.
  let error =
    aggregate::run(&cold, &backend, &env, &manifest, "").err().unwrap();
  assert!(error.contains("requires 4 shard proofs"), "{error}");
}

/// Every file under `dir`, recursively.
fn files_under(dir: &Path) -> Vec<PathBuf> {
  let mut out = Vec::new();
  let mut stack = vec![dir.to_path_buf()];
  while let Some(dir) = stack.pop() {
    let Ok(entries) = fs::read_dir(&dir) else { continue };
    for entry in entries {
      let path = entry.unwrap().path();
      if path.is_dir() {
        stack.push(path);
      } else {
        out.push(path);
      }
    }
  }
  out.sort();
  out
}

#[test]
fn a_binding_proof_in_memory_discharges_without_writing() {
  let dir = TempDir::new();
  let (env, manifest) = environment(&[1, 1], &dir.0);
  let backend = Fake::new();
  let assumed = Config { assume_binding: true, ..config(&dir.0) };
  lanes::run(&assumed, &backend, &env, &manifest).unwrap();
  let claim = binding_claim(&env).unwrap();
  let mut claim_bytes = Vec::new();
  claim.put(&mut claim_bytes);
  let proof = FakeProof {
    outer: backend.outer_claim(ChildKind::Ixvm, &claim_bytes),
    shards: 1,
  };
  let wrapper =
    claim_wrapper_bytes(&claim, backend.encode_proof(&proof)).unwrap();
  let before = files_under(&dir.0);
  backend.clear();
  let cfg = aggregate::Config {
    binding_proof: Some(BindingSource::Bytes(wrapper.clone())),
    ..aggregate_config(&dir.0)
  };
  let output =
    aggregate::run(&cfg, &backend, &env, &manifest, "").unwrap().unwrap();
  assert_eq!(backend.entries("extra"), 1);
  assert!(output.wrapper.is_some());
  assert_eq!(files_under(&dir.0), before);
  // The same proof by address needs it in the store.
  let stored = aggregate::Config {
    binding_proof: Some(BindingSource::Stored(Address::hash(&wrapper))),
    ..aggregate_config(&dir.0)
  };
  let error =
    aggregate::run(&stored, &backend, &env, &manifest, "").err().unwrap();
  assert!(error.contains("read"), "{error}");
}
