//! Shared CPU preparation feeding one resident prover per GPU.
//!
//! Claims and ready joins execute through one bounded queue. Prepared
//! records go to the next available GPU, with joins taking priority.
//! Record reservations follow their storage through both proving rounds.
//! Under memory pressure executions wait for capacity; mutual blocking
//! cancels the youngest waiter so the selected execution can finish.

mod checkpoint;
mod limits;
mod queue;
use limits::{HostBudget, cgroup_memory_limit};
use queue::WorkQueue;

pub use limits::{cell_workspace, detected_ram_budget};

use std::collections::{BTreeSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Instant;

use ix_common::address::Address;
use ixon::Proof as IxonProof;
use ixon::shard::{ShardManifest, static_block_profile};
use rayon::prelude::*;
use record_pool::{PoolStats, ProverBudget, RecordPool, RecordReservation};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::backend::{Backend, BackendSlot, PrepareFailure, ProvenClaim, Run};
use crate::discharge::{BindingProof, BindingSource, discharge, load_binding};
use crate::plan::{FoldPolicy, PlanOp, SlotSpec, build_specs};
use crate::prepare::{PreparedRun, prepare_run, validate_root_statement};
use crate::protocol::ChildKind;
use crate::store::{
  decode_wrapper, index_claim, load_cached, persist_wrapper, read_store,
  write_store,
};
use crate::{format_gib, panic_text};

pub struct Config {
  pub lanes: usize,
  /// Per-GPU host budget in bytes, multiplied by `lanes`; 0 detects one
  /// process-wide allowance.
  pub max_ram_bytes: usize,
  /// Preparation threads per GPU, combined into one process-wide pool.
  pub exec_jobs: usize,
  pub fold: FoldPolicy,
  /// Reuse and publish verified aggregate proofs in the aggregate cache.
  pub use_cache: bool,
  /// Reuse and publish claim proofs in the shard-proof index.
  pub use_index: bool,
  pub out_manifest: Option<PathBuf>,
  /// The content-addressed store; `None` is `~/.ix/store`.
  pub store_dir: Option<PathBuf>,
  /// The aggregate cache, shard-proof index and refined manifests; `None`
  /// is `AIUR_LANES_CACHE_DIR`, or `~/.ix/cache`.
  pub cache_root: Option<PathBuf>,
  /// Prove claims only: no joins and no root; the run ends when every
  /// selected claim is proven, and returns one `id address` line per claim.
  pub claims_only: bool,
  /// The manifest claims to prove, by shard id, with `claims_only`; the
  /// parts of a selected claim that is bisected stay selected. `None`
  /// selects every claim.
  pub select: Option<Vec<u32>>,
  /// Claims assume their role binding meets the specifications instead of
  /// validating it.
  pub assume_binding: bool,
  /// The store address of a proof of the environment's `Binding` claim.
  /// The claims then assume their binding (as with `assume_binding`), and
  /// the root discharges that assumption before it is wrapped.
  pub binding_proof: Option<Address>,
}

impl Config {
  /// Legacy's GPU pipeline: direct joins, both caches, default paths.
  pub fn new(
    lanes: usize,
    max_ram_bytes: usize,
    exec_jobs: usize,
    structural_above: usize,
  ) -> Self {
    Self {
      lanes,
      max_ram_bytes,
      exec_jobs,
      fold: FoldPolicy { structural_above, direct_joins: true },
      use_cache: true,
      use_index: true,
      out_manifest: None,
      store_dir: None,
      cache_root: None,
      claims_only: false,
      select: None,
      assume_binding: false,
      binding_proof: None,
    }
  }

  fn store_dir(&self) -> Result<PathBuf, String> {
    match &self.store_dir {
      Some(dir) => Ok(dir.clone()),
      None => {
        let home =
          std::env::var_os("HOME").ok_or("no HOME environment variable")?;
        Ok(PathBuf::from(home).join(".ix").join("store"))
      },
    }
  }

  fn cache_root(&self) -> Result<PathBuf, String> {
    if let Some(dir) = &self.cache_root {
      return Ok(dir.clone());
    }
    if let Some(dir) = std::env::var_os("AIUR_LANES_CACHE_DIR") {
      return Ok(PathBuf::from(dir));
    }
    let home =
      std::env::var_os("HOME").ok_or("no HOME environment variable")?;
    Ok(PathBuf::from(home).join(".ix").join("cache"))
  }
}

/// The default ceiling on one execution record's counted bytes: large
/// enough that any single constant of the environments proven so far
/// executes as one claim, small enough that one record cannot take most
/// of a four-lane pool. A claim over it is bisected rather than executed.
/// `AIUR_RECORD_MAX_BYTES` overrides it.
const DEFAULT_RECORD_MAX_BYTES: usize = 128 << 30;

enum PassOutcome {
  Complete { root: String, unproven: usize },
  Refine(Vec<u32>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Work {
  Claim(usize),
  Join(usize),
  Root,
}

struct Prep<B: Backend> {
  work: Work,
  children: Vec<Arc<BackendSlot<B>>>,
  reservation: RecordReservation,
}

/// A prepared host record consumed by whichever GPU becomes available.
enum Item<B: Backend> {
  Claim { shard: usize, record: B::ClaimRecord },
  Join { slot: usize, staged: Box<B::Staged> },
  Root { slot: usize, staged: Box<B::Staged> },
}

impl<B: Backend> Item<B> {
  fn work(&self) -> Work {
    match self {
      Self::Claim { shard, .. } => Work::Claim(*shard),
      Self::Join { slot, .. } => Work::Join(*slot),
      Self::Root { .. } => Work::Root,
    }
  }
}

enum Event<S> {
  ExecutionStarted { executor: usize, work: Work },
  Prepared { executor: usize, work: Work, record_bytes: usize, secs: f64 },
  PrepAvailable,
  PrepFailed { executor: usize, work: Work, failure: PrepareFailure },
  Proving { worker: usize, work: Work },
  Proven { worker: usize, work: Work, result: Result<Arc<S>, String> },
  RootProven { worker: usize, result: Result<String, String> },
}

type BackendEvent<B> = Event<BackendSlot<B>>;

struct ShutdownRun<'a, B: Backend> {
  pool: &'a RecordPool,
  prep: &'a WorkQueue<Prep<B>>,
  items: &'a WorkQueue<Item<B>>,
}

impl<B: Backend> Drop for ShutdownRun<'_, B> {
  fn drop(&mut self) {
    self.pool.shutdown();
    self.prep.close();
    self.items.close();
  }
}

/// A claim's proof from the shard-proof index, verified natively against
/// the claim this run expects, as a raw leaf slot; `None` when absent or
/// not acceptable, never an error.
fn resume_leaf<B: Backend>(
  backend: &B,
  lane: &B::Lane,
  run: Run<'_, B::Claim>,
  index_dir: &Path,
  slot_index: usize,
  shard: usize,
) -> Option<BackendSlot<B>> {
  let spec = &run.specs[slot_index];
  let statement = &run.prepared[shard].statement;
  let digest = Address::hash(&statement.claim_bytes);
  let raw = fs::read_to_string(index_dir.join(digest.hex())).ok()?;
  let address = Address::from_hex(raw.trim())?;
  let bytes = read_store(run.store_dir, &address).ok()?;
  if Address::hash(&bytes) != address {
    return None;
  }
  let wrapper = decode_wrapper(&bytes).ok()?;
  if wrapper.claim != statement.claim {
    return None;
  }
  let proof = backend.decode_proof(&wrapper.proof).ok()?;
  let inner = backend.outer_claim(ChildKind::Ixvm, &statement.claim_bytes);
  backend.verify_on(lane, ChildKind::Ixvm, &inner, &proof).ok()?;
  let claims_bytes = backend.claims_bytes(&inner);
  Some(BackendSlot::<B> {
    kind: ChildKind::Ixvm,
    statement: spec.statement.clone(),
    outer_claim: inner,
    proof,
    proof_address: Some(address),
    claims_bytes,
  })
}

/// Executes queued work on one executor thread, against the first lane's
/// prover.
fn prepare_loop<B: Backend>(
  backend: &B,
  lane: &B::Lane,
  run: Run<'_, B::Claim>,
  executor: usize,
  env: &ixon::Env,
  owned: &[Vec<Address>],
  prep: &WorkQueue<Prep<B>>,
  items: &WorkQueue<Item<B>>,
  events: &mpsc::Sender<BackendEvent<B>>,
) {
  while let Some(task) = prep.pop() {
    let Prep { work, children, reservation } = task;
    let began = Instant::now();
    let _ = events.send(Event::ExecutionStarted { executor, work });
    let binding = backend.bind(&reservation);
    let outcome = (|| -> Result<Item<B>, PrepareFailure> {
      match work {
        Work::Claim(shard) => {
          let record = backend.execute_claim(
            lane,
            env,
            &owned[shard],
            &run.prepared[shard].statement.claim,
            run.wrap_budget,
            &reservation,
          )?;
          Ok(Item::Claim { shard, record })
        },
        Work::Join(slot) => {
          let staged = backend.execute_aggregate(
            lane,
            run,
            slot,
            &children,
            &reservation,
          )?;
          Ok(Item::Join { slot, staged: Box::new(staged) })
        },
        Work::Root => {
          let slot = run.specs.len() - 1;
          let staged = backend.execute_aggregate(
            lane,
            run,
            slot,
            &children,
            &reservation,
          )?;
          Ok(Item::Root { slot, staged: Box::new(staged) })
        },
      }
    })();
    reservation.finish_execution();
    let measured = reservation.bytes();
    drop(binding);
    drop(reservation);
    match outcome {
      Ok(item) => {
        // Publish preparation before handing ownership to a prover.
        let _ = events.send(Event::Prepared {
          executor,
          work,
          record_bytes: measured,
          secs: began.elapsed().as_secs_f64(),
        });
        if items.push(item, !matches!(work, Work::Claim(_))).is_err() {
          return;
        }
        // A producer waiting on a full prepared queue still occupies its
        // execution slot and retains the record's memory charge.
        let _ = events.send(Event::PrepAvailable);
      },
      Err(failure) => {
        let _ = events.send(Event::PrepFailed { executor, work, failure });
      },
    }
  }
}

/// Each job's proving rounds stay on this device; completed proofs
/// release records and make dependent joins ready.
fn prove_loop<B: Backend>(
  backend: &B,
  lane: &B::Lane,
  run: Run<'_, B::Claim>,
  worker: usize,
  prepared_run: &PreparedRun,
  leaf_slot: &[usize],
  index_dir: Option<&Path>,
  binding: Option<&BindingProof<B>>,
  items: &WorkQueue<Item<B>>,
  pool: &RecordPool,
  events: &mpsc::Sender<BackendEvent<B>>,
) {
  while let Some(item) = items.pop() {
    let _ = events.send(Event::Proving { worker, work: item.work() });
    match item {
      Item::Claim { shard, record } => {
        let result = (|| -> Result<Arc<BackendSlot<B>>, String> {
          let ProvenClaim { claim, claim_bytes, proof } =
            backend.prove_claim(lane, record)?;
          let proof_bytes = backend
            .encode_proof(&proof)
            .map_err(|e| format!("proof serialization: {e}"))?;
          let wrapper = IxonProof::new(claim, proof_bytes);
          let mut wrapper_bytes = Vec::new();
          wrapper.put(&mut wrapper_bytes);
          write_store(run.store_dir, &claim_bytes)?;
          let address = write_store(run.store_dir, &wrapper_bytes)?;
          if let Some(index_dir) = index_dir {
            index_claim(index_dir, &claim_bytes, &address)?;
          }
          let inner = backend.outer_claim(ChildKind::Ixvm, &claim_bytes);
          let claims_bytes = backend.claims_bytes(&inner);
          Ok(Arc::new(BackendSlot::<B> {
            kind: ChildKind::Ixvm,
            statement: run.specs[leaf_slot[shard]].statement.clone(),
            outer_claim: inner,
            proof,
            proof_address: Some(address),
            claims_bytes,
          }))
        })();
        let _ = events.send(Event::Proven {
          worker,
          work: Work::Claim(shard),
          result,
        });
      },
      Item::Join { slot, staged } => {
        let result = backend.prove_aggregate(lane, run, slot, *staged);
        let _ =
          events.send(Event::Proven { worker, work: Work::Join(slot), result });
      },
      Item::Root { slot, staged } => {
        let result = (|| -> Result<String, String> {
          let root = backend.prove_aggregate(lane, run, slot, *staged)?;
          validate_root_statement(prepared_run, &root.statement)?;
          let root = match binding {
            Some(binding) => {
              let reservation = pool
                .try_admit()
                .map_err(|error| {
                  format!("binding discharge admission: {error:?}")
                })?
                .ok_or("binding discharge cannot acquire record capacity")?;
              let bound = backend.bind(&reservation);
              let discharged =
                discharge(backend, lane, run, &root, binding, &reservation)?;
              drop(bound);
              drop(reservation);
              discharged
            },
            None => root,
          };
          // Wrap until the final proof is a single trace shard.
          let mut wrapped: Option<B::Proof> = None;
          loop {
            let current = wrapped.as_ref().unwrap_or(&root.proof);
            let shards = backend.trace_shards(current);
            if shards <= 1 {
              break;
            }
            let reservation = pool
              .try_admit()
              .map_err(|error| format!("root wrap admission: {error:?}"))?
              .ok_or("root wrap cannot acquire record capacity")?;
            let binding = backend.bind(&reservation);
            let next =
              backend.wrap_root(lane, run, &root, current, &reservation)?;
            drop(binding);
            drop(reservation);
            if backend.trace_shards(&next) >= shards {
              break;
            }
            wrapped = Some(next);
          }
          let proof = wrapped.as_ref().unwrap_or(&root.proof);
          backend
            .verify_on(lane, ChildKind::Aggr, &root.outer_claim, proof)
            .map_err(|error| {
              format!("aggregate root proof failed verification: {error}")
            })?;
          let address = match (&wrapped, &root.proof_address) {
            (None, Some(address)) => address.clone(),
            _ => persist_wrapper(
              run.store_dir,
              &root.statement,
              backend.encode_proof(proof),
            )?,
          };
          Ok(address.hex())
        })();
        let _ = events.send(Event::RootProven { worker, result });
      },
    }
  }
}

/// The composed verdict: every claim proof the run holds, proved or
/// reused, verified natively against its claim, in parallel. Returns the
/// failures and the number of claims without a proof to verify: claims
/// retired under a cached join whose proof the index no longer holds,
/// which rest on that join's own native verification when it was loaded.
fn composed_verdict<B: Backend>(
  backend: &B,
  prepared: &PreparedRun,
  leaves: &[Option<Arc<BackendSlot<B>>>],
) -> (Vec<String>, usize) {
  let failures = leaves
    .par_iter()
    .enumerate()
    .filter_map(|(shard, slot)| {
      let slot = slot.as_ref()?;
      let inner = backend.outer_claim(
        ChildKind::Ixvm,
        &prepared.shards[shard].statement.claim_bytes,
      );
      backend.verify(ChildKind::Ixvm, &inner, &slot.proof).err().map(|error| {
        format!(
          "claim {}: proof fails verification: {error}",
          prepared.shards[shard].original_id
        )
      })
    })
    .collect();
  (failures, leaves.iter().filter(|slot| slot.is_none()).count())
}

/// A claims-only pass's result: every selected claim's proof verified,
/// and one `id address` line per claim, in manifest order.
fn claims_outcome<B: Backend>(
  backend: &B,
  pass: &Pass<B>,
  selected: Option<&BTreeSet<u32>>,
  leaves: &[Option<Arc<BackendSlot<B>>>],
) -> Result<PassOutcome, String> {
  let wanted = |shard: usize| {
    selected
      .is_none_or(|ids| ids.contains(&pass.prepared.shards[shard].original_id))
  };
  let leaves: Vec<_> = leaves
    .iter()
    .enumerate()
    .map(|(shard, slot)| slot.clone().filter(|_| wanted(shard)))
    .collect();
  let (failures, _) = composed_verdict(backend, &pass.prepared, &leaves);
  if !failures.is_empty() {
    return Err(failures.join("; "));
  }
  let mut lines = Vec::new();
  for (shard, slot) in leaves.iter().enumerate() {
    if !wanted(shard) {
      continue;
    }
    let id = pass.prepared.shards[shard].original_id;
    let address = slot
      .as_ref()
      .and_then(|slot| slot.proof_address.as_ref())
      .ok_or_else(|| format!("claim {id} has no persisted proof"))?;
    lines.push(format!("{id} {}", address.hex()));
  }
  Ok(PassOutcome::Complete { root: lines.join("\n"), unproven: 0 })
}

/// The whole run. Prints progress on stderr and returns the verified
/// root address.
pub fn run<B: Backend>(
  cfg: &Config,
  backend: &B,
  env: &ixon::Env,
  manifest_path: &Path,
) -> Result<String, String> {
  let started = Instant::now();
  let manifest_bytes = fs::read(manifest_path).map_err(|error| {
    format!("read manifest {}: {error}", manifest_path.display())
  })?;
  let source = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))?;
  let cache_root = cfg.cache_root()?;
  let checkpoint_path = cache_root
    .join("refined-manifests")
    .join(format!("{}.ixes", Address::hash(&manifest_bytes).hex()));
  let resumed = match fs::read(&checkpoint_path) {
    Ok(bytes) => {
      let refined = ShardManifest::from_bytes(&bytes).map_err(|error| {
        format!("refined manifest {}: {error}", checkpoint_path.display())
      })?;
      say(&format!(
        "resuming refined partition with {} claims from {}",
        refined.num_shards,
        checkpoint_path.display()
      ));
      Some(refined)
    },
    Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
    Err(error) => {
      return Err(format!("read {}: {error}", checkpoint_path.display()));
    },
  };
  let record_max_bytes = match std::env::var("AIUR_RECORD_MAX_BYTES") {
    Ok(value) => value
      .parse::<usize>()
      .ok()
      .filter(|&n| n > 0)
      .ok_or("AIUR_RECORD_MAX_BYTES must be a positive integer")?,
    Err(std::env::VarError::NotPresent) => DEFAULT_RECORD_MAX_BYTES,
    Err(error) => return Err(format!("AIUR_RECORD_MAX_BYTES: {error}")),
  };
  if cfg.select.is_some() && !cfg.claims_only {
    return Err("a claim selection proves claims only".into());
  }
  let mut selected: Option<BTreeSet<u32>> =
    cfg.select.as_ref().map(|ids| ids.iter().copied().collect());
  let mut manifest = match resumed {
    Some(refined) => {
      if let Some(selected) = selected.as_mut() {
        *selected = descendants(&source, &refined, selected)?;
      }
      refined
    },
    None => source,
  };
  let binding = match &cfg.binding_proof {
    Some(address) if !cfg.claims_only => {
      let source = BindingSource::Stored(address.clone());
      Some(load_binding(backend, &cfg.store_dir()?, &source, env)?)
    },
    _ => None,
  };
  let mut profile = None;
  let mut pool_stats = PoolStats::default();
  loop {
    match run_manifest(
      cfg,
      backend,
      env,
      &manifest,
      selected.as_ref(),
      &cache_root,
      record_max_bytes,
      binding.as_ref(),
      started,
      &mut pool_stats,
    )? {
      PassOutcome::Complete { root, unproven } => {
        if let Some(path) = &cfg.out_manifest {
          checkpoint::write_atomic(path, &manifest.to_bytes())?;
          say(&format!("final partition: {}", path.display()));
        }
        say(&format!(
          "record pool: peak granted {} GiB, {} growth waits ({:.1}s summed across executions), {} contention retries",
          format_gib(pool_stats.peak_reserved),
          pool_stats.waits,
          pool_stats.wait_time.as_secs_f64(),
          pool_stats.retries,
        ));
        let coverage = if unproven == 0 {
          String::new()
        } else {
          format!(
            " ({unproven} claims retired under verified cached joins have no indexed proof)"
          )
        };
        if cfg.claims_only {
          say(&format!(
            "{} claim proofs verified; end to end {}s",
            root.lines().count(),
            started.elapsed().as_secs()
          ));
        } else {
          say(&format!(
            "root {root} verified; composed verdict OK{coverage}; end to end {}s",
            started.elapsed().as_secs()
          ));
        }
        return Ok(root);
      },
      PassOutcome::Refine(ids) => {
        let profile = profile.get_or_insert_with(|| static_block_profile(env));
        let (refined, parts) = manifest.bisect_leaves(profile, &ids)?;
        checkpoint::write_atomic(&checkpoint_path, &refined.to_bytes())?;
        for (&id, parts) in ids.iter().zip(parts) {
          say(&format!("split claim {id} into claims {parts:?}"));
          if let Some(selected) = selected.as_mut()
            && selected.remove(&id)
          {
            selected.extend(parts);
          }
        }
        say(&format!(
          "refined partition: {} claims, saved to {}; continuing with completed proofs",
          refined.num_shards,
          checkpoint_path.display()
        ));
        manifest = refined;
      },
    }
  }
}

/// The claims of `refined` that descend from the `selected` claims of
/// `source`. Refinement only cuts leaves into parts, so every refined claim's
/// blocks lie within exactly one source claim; this is the closure of the
/// part ids each split reports, recovered from a checkpoint alone.
fn descendants(
  source: &ShardManifest,
  refined: &ShardManifest,
  selected: &BTreeSet<u32>,
) -> Result<BTreeSet<u32>, String> {
  let mut origin: FxHashMap<&Address, u32> = FxHashMap::default();
  for shard in &source.shards {
    for block in &shard.blocks {
      origin.insert(block, shard.id);
    }
  }
  let mut out = BTreeSet::new();
  for shard in &refined.shards {
    let parent = shard.blocks.first().and_then(|block| origin.get(block));
    let Some(&parent) = parent else {
      return Err(format!(
        "refined claim {} has no block of the source manifest",
        shard.id
      ));
    };
    if selected.contains(&parent) {
      out.insert(shard.id);
    }
  }
  Ok(out)
}

/// One pass over a manifest: the plan, the host budget it runs under, and
/// a resident prover pair per device.
struct Pass<B: Backend> {
  prepared: PreparedRun,
  specs: Vec<SlotSpec<B::Claim>>,
  root_slot: usize,
  root_left: usize,
  root_right: usize,
  /// The plan slot holding each manifest shard's claim.
  leaf_slot: Vec<usize>,
  /// The sorted leaves of each shard's statement.
  owned: Vec<Vec<Address>>,
  store_dir: PathBuf,
  cache_dir: Option<PathBuf>,
  index_dir: Option<PathBuf>,
  /// CPU execution threads shared by every lane.
  executions: usize,
  /// The process-wide host limit, the prover budget of every slot.
  wrap_budget: Option<usize>,
  claims_only: bool,
  pool: RecordPool,
  lanes: Vec<B::Lane>,
}

impl<B: Backend> Pass<B> {
  fn shards(&self) -> usize {
    self.prepared.shards.len()
  }

  /// The run state every lane proves against.
  fn run(&self) -> Run<'_, B::Claim> {
    Run {
      specs: &self.specs,
      prepared: &self.prepared.shards,
      owner_by_address: &self.prepared.owner_by_address,
      store_dir: &self.store_dir,
      cache_dir: self.cache_dir.as_deref(),
      write_outputs: true,
      wrap_budget: self.wrap_budget,
      reprove_slot: None,
    }
  }
}

fn say(message: &str) {
  eprintln!("[lanes] {message}");
}

fn plan_pass<B: Backend>(
  cfg: &Config,
  backend: &B,
  env: &ixon::Env,
  manifest: &ShardManifest,
  cache_root: &Path,
  record_max_bytes: usize,
) -> Result<Pass<B>, String> {
  let ctx = crate::claim_context(
    env,
    cfg.assume_binding || cfg.binding_proof.is_some(),
  )?;
  let prepared = prepare_run(&ctx, env, manifest)?;
  if !cfg.fold.direct_joins {
    return Err(
      "the lane controller proves claims and joins directly; wrap-first leaves are not supported"
        .into(),
    );
  }
  let specs = build_specs(&prepared, backend, cfg.fold)?;
  let root_slot = specs.len().checked_sub(1).ok_or("empty plan")?;
  let (root_left, root_right) = match specs[root_slot].op {
    PlanOp::Join(left, right) => (left, right),
    PlanOp::Leaf(_) if cfg.claims_only => (usize::MAX, usize::MAX),
    PlanOp::Leaf(_) => {
      return Err(
        "the manifest has one shard; there is nothing to join".into(),
      );
    },
  };
  let mut leaf_slot = vec![usize::MAX; prepared.shards.len()];
  for (index, spec) in specs.iter().enumerate() {
    if let PlanOp::Leaf(shard) = spec.op {
      leaf_slot[shard] = index;
    }
  }
  let owned: Vec<Vec<Address>> = prepared
    .shards
    .iter()
    .map(|shard| {
      let mut leaves = Vec::new();
      shard.statement.subjects.collect_leaves(&mut leaves);
      leaves.sort_unstable();
      leaves
    })
    .collect();

  let store_dir = cfg.store_dir()?;
  let cache_dir = cfg.use_cache.then(|| cache_root.join("aggregate"));
  let index_dir = cfg.use_index.then(|| cache_root.join("formal-shard-proofs"));
  if let Some(cache_dir) = &cache_dir {
    fs::create_dir_all(cache_dir)
      .map_err(|error| format!("create {}: {error}", cache_dir.display()))?;
  }

  if cfg.lanes == 0 {
    return Err("at least one lane is required".into());
  }
  let exec_jobs = if cfg.exec_jobs == 0 {
    let cores = thread::available_parallelism().map_or(1, usize::from);
    (cores / cfg.lanes).max(1)
  } else {
    cfg.exec_jobs
  };
  let executions = exec_jobs
    .checked_mul(cfg.lanes)
    .ok_or("execution thread count overflow")?;
  let cells = match std::env::var("AIUR_TRACE_SHARD_MAX_CELLS") {
    Ok(value) => value
      .parse::<usize>()
      .ok()
      .filter(|&n| n > 0)
      .ok_or("AIUR_TRACE_SHARD_MAX_CELLS must be a positive integer")?,
    Err(std::env::VarError::NotPresent) => 1_500_000_000,
    Err(error) => return Err(format!("AIUR_TRACE_SHARD_MAX_CELLS: {error}")),
  };
  // The verifying keys must not depend on the device: every cache key and
  // claim binding is derived from them. Built before the budget, so the
  // backend's resident memory includes them.
  say(&format!("building {} resident workers", cfg.lanes));
  let lanes = backend.lanes(cfg.lanes)?;
  let workspace = backend
    .lane_workspace_bytes(cells)
    .ok_or("prover workspace budget overflow")?;
  let cgroup_limit = cgroup_memory_limit();
  let host = HostBudget::new(
    cfg.lanes,
    executions,
    cfg.max_ram_bytes,
    detected_ram_budget(),
    cgroup_limit,
    workspace,
    backend.resident_bytes(),
  )?;
  let pool = RecordPool::for_provers(
    host.records,
    host.initial,
    ProverBudget { trace_cells: cells, host_workspace: host.workspace },
  )
  .with_record_limit(record_max_bytes);
  say(&format!(
    "host budget {} GiB process-wide (requested {} GiB per GPU, visible cgroup limit {}): {} GiB shared records, {} GiB workspace per GPU, {} GiB headroom{}; {executions} CPU executions, {} prepared queue slots; {} GiB initial reservation, growth waits for shared capacity; {cells} trace cells",
    format_gib(host.limit),
    format_gib(cfg.max_ram_bytes),
    cgroup_limit.map_or_else(
      || "unlimited or unavailable".into(),
      |bytes| format!("{} GiB", format_gib(bytes))
    ),
    format_gib(host.records),
    format_gib(host.workspace),
    format_gib(host.headroom),
    if host.resident == 0 {
      String::new()
    } else {
      format!(", {} GiB resident", format_gib(host.resident))
    },
    cfg.lanes,
    format_gib(host.initial.min(pool.record_limit())),
  ));
  say(&format!(
    "per-record ceiling {} GiB; oversized environment claims are bisected automatically",
    format_gib(pool.record_limit())
  ));

  Ok(Pass {
    prepared,
    specs,
    root_slot,
    root_left,
    root_right,
    leaf_slot,
    owned,
    store_dir,
    cache_dir,
    index_dir,
    executions,
    wrap_budget: Some(host.limit),
    claims_only: cfg.claims_only,
    pool,
    lanes,
  })
}

/// What persisted state fills before a pass dispatches anything: cached
/// joins with the subtrees they retire, and claims the index still proves.
struct Resumed<S> {
  slots: Vec<Option<Arc<S>>>,
  retired: Vec<bool>,
  claim_done: Vec<bool>,
}

fn resume_pass<B: Backend>(
  backend: &B,
  pass: &Pass<B>,
) -> Resumed<BackendSlot<B>> {
  let count = pass.specs.len();
  let shards = pass.shards();
  let run = pass.run();
  let lane = &pass.lanes[0];
  // Cached joins from the root down retire their subtrees.
  let mut slots: Vec<Option<Arc<BackendSlot<B>>>> = vec![None; count];
  let mut retired = vec![false; count];
  let joins = if pass.claims_only { 0 } else { pass.root_slot };
  for index in (0..joins).rev() {
    let spec = &pass.specs[index];
    if retired[index] || spec.kind != ChildKind::Aggr {
      continue;
    }
    let Some((proof, address)) = load_cached(
      run.store_dir,
      run.cache_dir,
      index,
      spec,
      |bytes| backend.decode_proof(bytes),
      |outer, proof| backend.verify_on(lane, ChildKind::Aggr, outer, proof),
    ) else {
      continue;
    };
    slots[index] = Some(Arc::new(BackendSlot::<B> {
      kind: ChildKind::Aggr,
      statement: spec.statement.clone(),
      outer_claim: spec.outer_claim.clone(),
      proof,
      proof_address: Some(address),
      claims_bytes: backend.claims_bytes(&spec.outer_claim),
    }));
    let mut stack = match spec.op {
      PlanOp::Join(l, r) => vec![l, r],
      PlanOp::Leaf(_) => Vec::new(),
    };
    while let Some(slot) = stack.pop() {
      if retired[slot] {
        continue;
      }
      retired[slot] = true;
      if let PlanOp::Join(l, r) = pass.specs[slot].op {
        stack.push(l);
        stack.push(r);
      }
    }
  }
  // Indexed claim proofs stand in for their claims. A claim retired under
  // a cached join is still loaded when the index holds its proof, so the
  // composed verdict can verify it independently.
  let mut claim_done = vec![false; shards];
  let resumed: Vec<Option<BackendSlot<B>>> = (0..shards)
    .into_par_iter()
    .map(|shard| {
      let index_dir = pass.index_dir.as_deref()?;
      resume_leaf(backend, lane, run, index_dir, pass.leaf_slot[shard], shard)
    })
    .collect();
  let mut reused = 0usize;
  for (shard, slot) in resumed.into_iter().enumerate() {
    if let Some(slot) = slot {
      slots[pass.leaf_slot[shard]] = Some(Arc::new(slot));
      claim_done[shard] = true;
      reused += 1;
    } else if retired[pass.leaf_slot[shard]] {
      claim_done[shard] = true;
    }
  }
  let cached_joins = slots
    .iter()
    .enumerate()
    .filter(|(i, s)| {
      s.is_some()
        && *i != pass.root_slot
        && !matches!(pass.specs[*i].op, PlanOp::Leaf(_))
    })
    .count();
  say(&format!(
    "{shards} claims ({reused} reused from the index, {} retired under cached joins without an indexed proof), {} joins ({cached_joins} cached)",
    claim_done.iter().filter(|d| **d).count() - reused,
    count - shards
  ));
  Resumed { slots, retired, claim_done }
}

/// The dispatch state of a running pass: which plan slots are proven,
/// queued, or executing, and how the pass ended.
struct Scheduler<'a, B: Backend> {
  pass: &'a Pass<B>,
  manifest: &'a ShardManifest,
  started: Instant,
  slots: Vec<Option<Arc<BackendSlot<B>>>>,
  retired: Vec<bool>,
  claim_done: Vec<bool>,
  claim_queue: VecDeque<usize>,
  /// Joins queued or executing.
  dispatched: FxHashSet<usize>,
  root_dispatched: bool,
  free_executors: usize,
  in_flight: usize,
  /// Claims whose records exceed the per-record ceiling, split once the
  /// active work drains.
  to_split: BTreeSet<u32>,
  root_address: Option<String>,
  failure: Option<String>,
}

impl<'a, B: Backend> Scheduler<'a, B> {
  fn new(
    pass: &'a Pass<B>,
    manifest: &'a ShardManifest,
    selected: Option<&BTreeSet<u32>>,
    started: Instant,
    resumed: Resumed<BackendSlot<B>>,
  ) -> Self {
    let Resumed { slots, retired, mut claim_done } = resumed;
    if let Some(selected) = selected {
      for (shard, done) in claim_done.iter_mut().enumerate() {
        if !selected.contains(&pass.prepared.shards[shard].original_id) {
          *done = true;
        }
      }
    }
    let claim_queue = (0..pass.shards()).filter(|&s| !claim_done[s]).collect();
    Self {
      pass,
      manifest,
      started,
      slots,
      retired,
      claim_done,
      claim_queue,
      dispatched: FxHashSet::default(),
      root_dispatched: false,
      free_executors: pass.executions,
      in_flight: 0,
      to_split: BTreeSet::new(),
      root_address: None,
      failure: None,
    }
  }

  fn work_name(&self, work: Work) -> String {
    match work {
      Work::Claim(shard) => {
        format!("claim {}", self.pass.prepared.shards[shard].original_id)
      },
      Work::Join(slot) => format!("join {slot}"),
      Work::Root => "root".to_string(),
    }
  }

  fn elapsed(&self) -> u64 {
    self.started.elapsed().as_secs()
  }

  fn idle(&self) -> bool {
    self.in_flight == 0 && self.free_executors == self.pass.executions
  }

  fn finished(&self) -> bool {
    self.failure.is_some() || self.root_address.is_some()
  }

  /// The next unit an executor can take: a join whose inputs are proven,
  /// then the root once every claim is done, then the oldest claim.
  fn next_work(&self) -> Option<Work> {
    let pass = self.pass;
    if pass.claims_only {
      return self.claim_queue.front().map(|&shard| Work::Claim(shard));
    }
    let ready_join = (0..pass.root_slot).find(|&index| {
      !self.retired[index]
        && self.slots[index].is_none()
        && !self.dispatched.contains(&index)
        && match pass.specs[index].op {
          PlanOp::Join(l, r) => {
            self.slots[l].is_some() && self.slots[r].is_some()
          },
          PlanOp::Leaf(_) => false,
        }
    });
    if let Some(slot) = ready_join {
      Some(Work::Join(slot))
    } else if !self.root_dispatched
      && self.claim_done.iter().all(|d| *d)
      && self.slots[pass.root_left].is_some()
      && self.slots[pass.root_right].is_some()
    {
      Some(Work::Root)
    } else {
      self.claim_queue.front().map(|&shard| Work::Claim(shard))
    }
  }

  /// The proven inputs `work` joins.
  fn children(&self, work: Work) -> Vec<Arc<BackendSlot<B>>> {
    let (l, r) = match work {
      Work::Claim(_) => return Vec::new(),
      Work::Join(slot) => {
        let PlanOp::Join(l, r) = self.pass.specs[slot].op else {
          unreachable!()
        };
        (l, r)
      },
      Work::Root => (self.pass.root_left, self.pass.root_right),
    };
    vec![self.slots[l].clone().unwrap(), self.slots[r].clone().unwrap()]
  }

  /// Accounts for `work` having left for an executor.
  fn queued(&mut self, work: Work) {
    self.free_executors -= 1;
    self.in_flight += 1;
    say(&format!(
      "{} dispatched at +{}s",
      self.work_name(work),
      self.elapsed()
    ));
    match work {
      Work::Claim(_) => {
        self.claim_queue.pop_front();
      },
      Work::Join(slot) => {
        self.dispatched.insert(slot);
      },
      Work::Root => self.root_dispatched = true,
    }
  }

  /// Every claim's slot, in manifest shard order.
  fn leaves(&self) -> Vec<Option<Arc<BackendSlot<B>>>> {
    self.pass.leaf_slot.iter().map(|&slot| self.slots[slot].clone()).collect()
  }

  fn handle(&mut self, event: BackendEvent<B>) {
    match event {
      Event::ExecutionStarted { executor, work } => say(&format!(
        "executor {executor}: {} execution started at +{}s",
        self.work_name(work),
        self.elapsed(),
      )),
      Event::Prepared { executor, work, record_bytes, secs } => say(&format!(
        "executor {executor}: {} executed in {secs:.1}s, record {record_bytes} B ({} GiB) at +{}s",
        self.work_name(work),
        format_gib(record_bytes),
        self.elapsed(),
      )),
      Event::PrepAvailable => {
        self.free_executors += 1;
      },
      Event::PrepFailed { executor, work, failure } => {
        self.free_executors += 1;
        self.in_flight -= 1;
        self.prep_failed(executor, work, failure);
      },
      Event::Proving { worker, work } => say(&format!(
        "worker {worker}: {} proving started at +{}s",
        self.work_name(work),
        self.elapsed(),
      )),
      Event::Proven { worker, work, result } => {
        self.in_flight -= 1;
        match (work, result) {
          (Work::Claim(shard), Ok(slot)) => {
            self.slots[self.pass.leaf_slot[shard]] = Some(slot);
            self.claim_done[shard] = true;
            say(&format!(
              "worker {worker}: claim {} proven at +{}s ({} left)",
              self.pass.prepared.shards[shard].original_id,
              self.elapsed(),
              self.claim_done.iter().filter(|d| !**d).count()
            ));
          },
          (Work::Join(slot), Ok(proof)) => {
            self.slots[slot] = Some(proof);
            say(&format!(
              "worker {worker}: join {slot} published at +{}s",
              self.elapsed()
            ));
          },
          (_, Err(error)) => {
            self.failure = Some(format!("{}: {error}", self.work_name(work)));
          },
          (Work::Root, Ok(_)) => {
            unreachable!("root reports through RootProven")
          },
        }
      },
      Event::RootProven { worker, result } => match result {
        Ok(address) => {
          say(&format!("worker {worker}: root proven at +{}s", self.elapsed()));
          self.root_address = Some(address);
        },
        Err(error) => self.failure = Some(format!("root: {error}")),
      },
    }
  }

  /// A contended execution is requeued; one over the record ceiling marks
  /// its claim for splitting, and anything else ends the pass.
  fn prep_failed(
    &mut self,
    executor: usize,
    work: Work,
    failure: PrepareFailure,
  ) {
    match failure {
      PrepareFailure::MemoryContention => {
        say(&format!(
          "executor {executor}: {} released for memory contention; requeued",
          self.work_name(work)
        ));
        match work {
          Work::Claim(shard) => self.claim_queue.push_back(shard),
          Work::Join(slot) => {
            self.dispatched.remove(&slot);
          },
          Work::Root => self.root_dispatched = false,
        }
      },
      PrepareFailure::OverRecordCap { bytes, cap } => {
        let Work::Claim(shard) = work else {
          self.failure = Some(format!(
            "{}: aggregation record needs {bytes} B, above the {cap} B per-record ceiling; an aggregation execution cannot be split as an environment claim",
            self.work_name(work)
          ));
          return;
        };
        let id = self.pass.prepared.shards[shard].original_id;
        let source = self
          .manifest
          .shards
          .iter()
          .find(|s| s.id == id)
          .expect("prepared claim belongs to the manifest");
        if source.blocks.len() > 1 {
          self.to_split.insert(id);
          say(&format!(
            "claim {id}: record needs {bytes} B, above the {cap} B per-record ceiling; draining active work before splitting this claim"
          ));
        } else {
          self.failure = Some(format!(
            "claim {id}: record needs {bytes} B, above the {cap} B per-record ceiling; its single atomic block cannot be split further"
          ));
        }
      },
      PrepareFailure::Other(error) => {
        self.failure = Some(format!("{}: {error}", self.work_name(work)));
      },
    }
  }
}

fn run_manifest<B: Backend>(
  cfg: &Config,
  backend: &B,
  env: &ixon::Env,
  manifest: &ShardManifest,
  selected: Option<&BTreeSet<u32>>,
  cache_root: &Path,
  record_max_bytes: usize,
  binding: Option<&BindingProof<B>>,
  started: Instant,
  pool_stats: &mut PoolStats,
) -> Result<PassOutcome, String> {
  let pass =
    plan_pass(cfg, backend, env, manifest, cache_root, record_max_bytes)?;
  let resumed = resume_pass(backend, &pass);
  let run = pass.run();

  let (events_tx, events_rx) = mpsc::channel::<BackendEvent<B>>();
  let prep_queue = WorkQueue::<Prep<B>>::new(pass.executions);
  let item_queue = WorkQueue::<Item<B>>::new(cfg.lanes);
  let outcome = thread::scope(|scope| -> Result<PassOutcome, String> {
    let _shutdown =
      ShutdownRun { pool: &pass.pool, prep: &prep_queue, items: &item_queue };
    for executor in 0..pass.executions {
      let events = events_tx.clone();
      let (pass, prep, items) = (&pass, &prep_queue, &item_queue);
      scope.spawn(move || {
        prepare_loop(
          backend,
          &pass.lanes[0],
          run,
          executor,
          env,
          &pass.owned,
          prep,
          items,
          &events,
        )
      });
    }
    for (worker, lane) in pass.lanes.iter().enumerate() {
      let events = events_tx.clone();
      let (pass, items) = (&pass, &item_queue);
      scope.spawn(move || {
        prove_loop(
          backend,
          lane,
          run,
          worker,
          &pass.prepared,
          &pass.leaf_slot,
          pass.index_dir.as_deref(),
          binding,
          items,
          &pass.pool,
          &events,
        )
      });
    }
    drop(events_tx);

    let mut scheduler =
      Scheduler::new(&pass, manifest, selected, started, resumed);
    let mut verdict: Option<
      thread::ScopedJoinHandle<'_, (Vec<String>, usize)>,
    > = None;
    loop {
      while scheduler.free_executors > 0 && scheduler.to_split.is_empty() {
        let Some(work) = scheduler.next_work() else {
          break;
        };
        let Some(reservation) = pass
          .pool
          .try_admit()
          .map_err(|e| format!("record admission: {e:?}"))?
        else {
          break;
        };
        let children = scheduler.children(work);
        prep_queue
          .push(
            Prep { work, children, reservation },
            !matches!(work, Work::Claim(_)),
          )
          .map_err(|Prep { work, .. }| {
            let kind =
              if matches!(work, Work::Claim(_)) { "claim" } else { "join" };
            format!("execution queue closed before a {kind} was queued")
          })?;
        scheduler.queued(work);
        if work == Work::Root && verdict.is_none() {
          let (leaves, pass) = (scheduler.leaves(), &pass);
          verdict =
            Some(scope.spawn(move || {
              composed_verdict(backend, &pass.prepared, &leaves)
            }));
        }
      }
      if scheduler.idle() {
        let claims_proven = pass.claims_only
          && scheduler.claim_queue.is_empty()
          && scheduler.claim_done.iter().all(|done| *done);
        if scheduler.to_split.is_empty() && !claims_proven {
          scheduler.failure = Some(
            "scheduler stalled: nothing runs and nothing can be admitted"
              .to_string(),
          );
        }
        break;
      }
      let event =
        events_rx.recv().map_err(|e| format!("worker channel closed: {e}"))?;
      scheduler.handle(event);
      if scheduler.finished() {
        break;
      }
    }
    drop(_shutdown);
    if let Some(error) = scheduler.failure {
      return Err(format!(
        "{error}; rerun the same command to resume from what was persisted"
      ));
    }
    if !scheduler.to_split.is_empty() {
      return Ok(PassOutcome::Refine(scheduler.to_split.into_iter().collect()));
    }
    if pass.claims_only {
      return claims_outcome(backend, &pass, selected, &scheduler.leaves());
    }
    let root = scheduler.root_address.ok_or("no root proof")?;
    let (failures, unproven) = verdict
      .ok_or("root proven before composed verdict started")?
      .join()
      .map_err(|payload| {
        format!("composed verdict thread panicked: {}", panic_text(&payload))
      })?;
    if failures.is_empty() {
      Ok(PassOutcome::Complete { root, unproven })
    } else {
      Err(failures.join("; "))
    }
  });
  let stats = pass.pool.stats();
  pool_stats.peak_reserved = pool_stats.peak_reserved.max(stats.peak_reserved);
  pool_stats.waits += stats.waits;
  pool_stats.wait_time += stats.wait_time;
  pool_stats.retries += stats.retries;
  outcome
}
