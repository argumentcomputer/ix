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

use std::collections::{BTreeSet, VecDeque};
use std::sync::mpsc;
use std::time::Instant;

use aiur::execute::bind_record_reservation;
use aiur::record_pool::{
  PoolStats, ProverBudget, RecordPool, RecordReservation,
};
use aiur::synthesis::ShardRetention as Retention;
use ixvm_codegen::aiur_ixvm_runner::execute_ixvm;
use ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness;

use super::prepare::PreparedRun;
use super::protocol::serialize_claims;
use super::prove::{
  PrepareFailure, Slot, StagedSlot, finish_slot, prepare_slot,
};
use super::store::{decode_wrapper, load_cached, read_store};
use super::*;
use crate::aiur::lean_unbox_nat_as_usize;
use aiur::synthesis::{GatedProve, PreparedProve};
use ix_common::address::Address;
use ixon::{Claim, Proof as IxonProof};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanExcept, LeanExternal, LeanNat, LeanOwned,
  LeanString,
};
use rustc_hash::FxHashSet;
use std::thread;

pub struct Config {
  pub lanes: usize,
  /// Per-GPU host budget in bytes, multiplied by `lanes`; 0 detects one
  /// process-wide allowance.
  pub max_ram_bytes: usize,
  /// Preparation threads per GPU, combined into one process-wide pool.
  pub exec_jobs: usize,
  pub structural_above: usize,
  pub cache_fri_bytes: Vec<u8>,
  pub out_manifest: Option<PathBuf>,
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

struct Prep {
  work: Work,
  children: Vec<Arc<Slot>>,
  reservation: RecordReservation,
}

/// A prepared host record consumed by whichever GPU becomes available.
enum Item {
  Claim {
    shard: usize,
    claim: Claim,
    claim_bytes: Vec<u8>,
    prepared: Box<PreparedProve>,
  },
  Join {
    slot: usize,
    staged: Box<StagedSlot>,
  },
  Root {
    slot: usize,
    staged: Box<StagedSlot>,
  },
}

impl Item {
  fn work(&self) -> Work {
    match self {
      Self::Claim { shard, .. } => Work::Claim(*shard),
      Self::Join { slot, .. } => Work::Join(*slot),
      Self::Root { .. } => Work::Root,
    }
  }
}

enum Event {
  ExecutionStarted { executor: usize, work: Work },
  Prepared { executor: usize, work: Work, record_bytes: usize, secs: f64 },
  PrepAvailable,
  PrepFailed { executor: usize, work: Work, failure: PrepareFailure },
  Proving { worker: usize, work: Work },
  Proven { worker: usize, work: Work, result: Result<Arc<Slot>, String> },
  RootProven { worker: usize, result: Result<String, String> },
}

struct ShutdownRun<'a> {
  pool: &'a RecordPool,
  prep: &'a WorkQueue<Prep>,
  items: &'a WorkQueue<Item>,
}

impl Drop for ShutdownRun<'_> {
  fn drop(&mut self) {
    self.pool.shutdown();
    self.prep.close();
    self.items.close();
  }
}

/// The shard-proof index entry of a claim, written like Stage 1 writes it.
fn index_claim(
  index_dir: &Path,
  claim_bytes: &[u8],
  address: &Address,
) -> Result<(), String> {
  fs::create_dir_all(index_dir)
    .map_err(|error| format!("create {}: {error}", index_dir.display()))?;
  let digest = Address::hash(claim_bytes);
  let temporary =
    index_dir.join(format!("{}.tmp.{}", digest.hex(), std::process::id()));
  fs::write(&temporary, format!("{}\n", address.hex()))
    .and_then(|()| fs::rename(&temporary, index_dir.join(digest.hex())))
    .map_err(|error| format!("shard-proof index: {error}"))
}

/// A claim's proof from the shard-proof index, verified natively against
/// the claim this run expects, as a raw leaf slot; `None` when absent or
/// not acceptable, never an error.
fn resume_leaf(
  ctx: ProveContext<'_>,
  index_dir: &Path,
  slot_index: usize,
  shard: usize,
) -> Option<Slot> {
  let spec = &ctx.specs[slot_index];
  let statement = &ctx.prepared[shard].statement;
  let digest = Address::hash(&statement.claim_bytes);
  let raw = fs::read_to_string(index_dir.join(digest.hex())).ok()?;
  let address = Address::from_hex(raw.trim())?;
  let bytes = read_store(ctx.store_dir, &address).ok()?;
  if Address::hash(&bytes) != address {
    return None;
  }
  let wrapper = decode_wrapper(&bytes).ok()?;
  if wrapper.claim != statement.claim {
    return None;
  }
  let proof = AiurProof::from_bytes(&wrapper.proof).ok()?;
  let inner = inner_claim(ctx.verify_idx, &statement.claim_bytes);
  ctx.ixvm_system.verify(&inner, &proof).ok()?;
  Some(Slot {
    kind: ChildKind::Ixvm,
    statement: spec.statement.clone(),
    outer_claim: inner.clone(),
    proof,
    proof_address: Some(address),
    claims_bytes: serialize_claims(&[&inner]),
  })
}

fn prepare_loop(
  ctx: ProveContext<'_>,
  executor: usize,
  env: &ixon::Env,
  owned: &[Vec<Address>],
  max_ram_bytes: Option<usize>,
  prep: &WorkQueue<Prep>,
  items: &WorkQueue<Item>,
  events: &mpsc::Sender<Event>,
) {
  while let Some(task) = prep.pop() {
    let Prep { work, children, reservation } = task;
    let began = Instant::now();
    let _ = events.send(Event::ExecutionStarted { executor, work });
    let binding = bind_record_reservation(&reservation);
    let outcome = (|| -> Result<Item, PrepareFailure> {
      match work {
        Work::Claim(shard) => {
          let (claim, input, mut io) =
            build_shard_check_env_witness(env, &owned[shard])
              .map_err(|e| format!("witness build: {e}"))?;
          let prepared = match ctx.ixvm_system.prepare_ixvm_within_budget(
            ctx.verify_idx, &input, &mut io, execute_ixvm,
            max_ram_bytes, true, Some(Retention::Regenerate),
          ) {
            Ok(prepared) => prepared,
            Err(GatedProve::Failed(aiur::execute::ExecError::RecordBudgetExceeded { bytes, cap })) => {
              return Err(PrepareFailure::OverRecordCap { bytes, cap });
            },
            Err(GatedProve::Failed(aiur::execute::ExecError::RecordMemoryContention)) => {
              return Err(PrepareFailure::MemoryContention);
            },
            Err(GatedProve::Failed(error)) => return Err(format!("execution failed: {error}").into()),
            Err(GatedProve::Split { peak, .. }) => return Err(format!(
              "no trace-shard count fits the process budget (whole-execution peak {peak} B)"
            ).into()),
            Err(_) => return Err("execution did not prepare a proof".into()),
          };
          let mut claim_bytes = Vec::new();
          claim.put(&mut claim_bytes);
          Ok(Item::Claim {
            shard,
            claim,
            claim_bytes,
            prepared: Box::new(prepared),
          })
        },
        Work::Join(slot) => {
          let staged = prepare_slot(ctx, slot, &children)?;
          Ok(Item::Join { slot, staged: Box::new(staged) })
        },
        Work::Root => {
          let slot = ctx.specs.len() - 1;
          let staged = prepare_slot(ctx, slot, &children)?;
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
fn prove_loop(
  ctx: ProveContext<'_>,
  worker: usize,
  prepared_run: &PreparedRun,
  leaf_slot: &[usize],
  index_dir: &Path,
  items: &WorkQueue<Item>,
  pool: &RecordPool,
  events: &mpsc::Sender<Event>,
) {
  while let Some(item) = items.pop() {
    let _ = events.send(Event::Proving { worker, work: item.work() });
    match item {
      Item::Claim { shard, claim, claim_bytes, prepared } => {
        let result = (|| -> Result<Arc<Slot>, String> {
          let (_, proof, _) = ctx.ixvm_system.prove_prepared(*prepared);
          let proof_bytes = proof
            .to_bytes()
            .map_err(|e| format!("proof serialization: {e}"))?;
          let wrapper = IxonProof::new(claim, proof_bytes);
          let mut wrapper_bytes = Vec::new();
          wrapper.put(&mut wrapper_bytes);
          write_store(ctx.store_dir, &claim_bytes)?;
          let address = write_store(ctx.store_dir, &wrapper_bytes)?;
          index_claim(index_dir, &claim_bytes, &address)?;
          let inner = inner_claim(ctx.verify_idx, &claim_bytes);
          Ok(Arc::new(Slot {
            kind: ChildKind::Ixvm,
            statement: ctx.specs[leaf_slot[shard]].statement.clone(),
            outer_claim: inner.clone(),
            proof,
            proof_address: Some(address),
            claims_bytes: serialize_claims(&[&inner]),
          }))
        })();
        let _ = events.send(Event::Proven {
          worker,
          work: Work::Claim(shard),
          result,
        });
      },
      Item::Join { slot, staged } => {
        let result = finish_slot(ctx, slot, *staged);
        let _ =
          events.send(Event::Proven { worker, work: Work::Join(slot), result });
      },
      Item::Root { slot, staged } => {
        let result = (|| -> Result<String, String> {
          let root = finish_slot(ctx, slot, *staged)?;
          validate_root_statement(prepared_run, &root.statement)?;
          // Wrap until the final proof is a single trace shard.
          let mut wrapped: Option<AiurProof> = None;
          loop {
            let current = wrapped.as_ref().unwrap_or(&root.proof);
            let shards = current.preamble.headers.len();
            if shards <= 1 {
              break;
            }
            let reservation = pool
              .try_admit()
              .map_err(|error| format!("root wrap admission: {error:?}"))?
              .ok_or("root wrap cannot acquire record capacity")?;
            let binding = bind_record_reservation(&reservation);
            let next = wrap_root(ctx, &root, current)?;
            drop(binding);
            drop(reservation);
            if next.preamble.headers.len() >= shards {
              break;
            }
            wrapped = Some(next);
          }
          let proof = wrapped.as_ref().unwrap_or(&root.proof);
          ctx.aggr_system.verify(&root.outer_claim, proof).map_err(
            |error| {
              format!("aggregate root proof failed verification: {error:?}")
            },
          )?;
          let address = match (&wrapped, &root.proof_address) {
            (None, Some(address)) => address.clone(),
            _ => persist_wrapper(ctx.store_dir, &root.statement, proof)?,
          };
          Ok(address.hex())
        })();
        let _ = events.send(Event::RootProven { worker, result });
      },
    }
  }
}

/// The whole run. Prints progress on stderr and returns the verified
/// root address.
/// The composed verdict: every claim proof the run holds, proved or
/// reused, verified natively against its claim, in parallel. Returns the
/// failures and the number of claims without a proof to verify: claims
/// retired under a cached join whose proof the index no longer holds,
/// which rest on that join's own native verification when it was loaded.
fn composed_verdict(
  ixvm: &AiurSystem,
  verify_idx: usize,
  prepared: &PreparedRun,
  leaves: &[Option<Arc<Slot>>],
) -> (Vec<String>, usize) {
  let failures = leaves
    .par_iter()
    .enumerate()
    .filter_map(|(shard, slot)| {
      let slot = slot.as_ref()?;
      let inner =
        inner_claim(verify_idx, &prepared.shards[shard].statement.claim_bytes);
      ixvm.verify(&inner, &slot.proof).err().map(|error| {
        format!(
          "claim {}: proof fails verification: {error:?}",
          prepared.shards[shard].original_id
        )
      })
    })
    .collect();
  (failures, leaves.iter().filter(|slot| slot.is_none()).count())
}

pub fn run(
  cfg: &Config,
  ixvm: &AiurSystem,
  aggr: &AiurSystem,
  env: &ixon::Env,
  manifest_path: &Path,
  verify_idx: usize,
  aggr_idx: usize,
) -> Result<String, String> {
  if cfg.cache_fri_bytes.len() != 40 {
    return Err("aggregate cache FRI serialization must be 40 bytes".into());
  }
  let started = Instant::now();
  let manifest_bytes = fs::read(manifest_path).map_err(|error| {
    format!("read manifest {}: {error}", manifest_path.display())
  })?;
  let source = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))?;
  let home = std::env::var_os("HOME").ok_or("no HOME environment variable")?;
  let cache_root = std::env::var_os("AIUR_LANES_CACHE_DIR")
    .map_or_else(|| PathBuf::from(home).join(".ix/cache"), PathBuf::from);
  let checkpoint_path = cache_root
    .join("refined-manifests")
    .join(format!("{}.ixes", Address::hash(&manifest_bytes).hex()));
  let mut manifest = match fs::read(&checkpoint_path) {
    Ok(bytes) => {
      let refined = ShardManifest::from_bytes(&bytes).map_err(|error| {
        format!("refined manifest {}: {error}", checkpoint_path.display())
      })?;
      say(&format!(
        "resuming refined partition with {} claims from {}",
        refined.num_shards,
        checkpoint_path.display()
      ));
      refined
    },
    Err(error) if error.kind() == std::io::ErrorKind::NotFound => source,
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
  let mut profile = None;
  let mut pool_stats = PoolStats::default();
  loop {
    match run_manifest(
      cfg,
      ixvm,
      aggr,
      env,
      &manifest,
      verify_idx,
      aggr_idx,
      &cache_root,
      record_max_bytes,
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
        say(&format!(
          "root {root} verified; composed verdict OK{coverage}; end to end {}s",
          started.elapsed().as_secs()
        ));
        return Ok(root);
      },
      PassOutcome::Refine(ids) => {
        let profile = profile
          .get_or_insert_with(|| crate::kernel::static_block_profile(env));
        let (refined, parts) = manifest.bisect_leaves(profile, &ids)?;
        checkpoint::write_atomic(&checkpoint_path, &refined.to_bytes())?;
        for (&id, parts) in ids.iter().zip(parts) {
          say(&format!("split claim {id} into claims {parts:?}"));
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

/// One pass over a manifest: the plan, the host budget it runs under, and
/// a resident prover pair per device.
struct Pass {
  prepared: PreparedRun,
  specs: Vec<SlotSpec>,
  ixvm_vk: Vec<u8>,
  aggr_vk: Vec<u8>,
  allowed: Vec<u8>,
  verify_idx: usize,
  aggr_idx: usize,
  root_slot: usize,
  root_left: usize,
  root_right: usize,
  /// The plan slot holding each manifest shard's claim.
  leaf_slot: Vec<usize>,
  /// The sorted leaves of each shard's statement.
  owned: Vec<Vec<Address>>,
  store_dir: PathBuf,
  cache_dir: PathBuf,
  index_dir: PathBuf,
  /// CPU execution threads shared by every lane.
  executions: usize,
  /// The process-wide host limit, the prover budget of every slot.
  wrap_budget: Option<usize>,
  pool: RecordPool,
  systems: Vec<(AiurSystem, AiurSystem)>,
}

impl Pass {
  fn shards(&self) -> usize {
    self.prepared.shards.len()
  }

  /// One proving context per device, all over the same plan and keys.
  fn contexts(&self) -> Vec<ProveContext<'_>> {
    self
      .systems
      .iter()
      .map(|(ixvm_system, aggr_system)| ProveContext {
        specs: &self.specs,
        prepared: &self.prepared.shards,
        proofs: None,
        owner_by_address: &self.prepared.owner_by_address,
        ixvm_system,
        aggr_system,
        ixvm_vk: &self.ixvm_vk,
        aggr_vk: &self.aggr_vk,
        allowed: &self.allowed,
        verify_idx: self.verify_idx,
        aggr_idx: self.aggr_idx,
        store_dir: &self.store_dir,
        cache_dir: Some(&self.cache_dir),
        reprove_slot: None,
        write_outputs: true,
        wrap_budget: self.wrap_budget,
        range_width: 0,
        range_jobs: 1,
      })
      .collect()
  }
}

fn say(message: &str) {
  eprintln!("[lanes] {message}");
}

fn plan_pass(
  cfg: &Config,
  ixvm: &AiurSystem,
  aggr: &AiurSystem,
  env: &ixon::Env,
  manifest: &ShardManifest,
  verify_idx: usize,
  aggr_idx: usize,
  cache_root: &Path,
  record_max_bytes: usize,
) -> Result<Pass, String> {
  let prepared = prepare_run(env, manifest)?;
  let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(ixvm)
    .map_err(|error| format!("IxVM VK serialization failed: {error}"))?;
  let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(aggr)
    .map_err(|error| format!("ixAggr VK serialization failed: {error}"))?;
  let allowed = allowed_blob(&ixvm_vk, verify_idx, &aggr_vk, aggr_idx);
  let specs = build_specs(
    &prepared,
    PlanIdentity {
      verify_idx,
      aggr_idx,
      aggr_vk: &aggr_vk,
      allowed: &allowed,
      cache_fri_bytes: &cfg.cache_fri_bytes,
    },
    FoldPolicy { structural_above: cfg.structural_above, direct_joins: true },
  )?;
  let root_slot = specs.len().checked_sub(1).ok_or("empty plan")?;
  let PlanOp::Join(root_left, root_right) = specs[root_slot].op else {
    return Err("the manifest has one shard; there is nothing to join".into());
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

  let home = std::env::var_os("HOME").ok_or("no HOME environment variable")?;
  let ix_root = PathBuf::from(home).join(".ix");
  let store_dir = ix_root.join("store");
  let cache_dir = cache_root.join("aggregate");
  let index_dir = cache_root.join("shard-proofs");
  fs::create_dir_all(&cache_dir)
    .map_err(|error| format!("create {}: {error}", cache_dir.display()))?;

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
  let cgroup_limit = cgroup_memory_limit();
  let host = HostBudget::new(
    cfg.lanes,
    executions,
    cfg.max_ram_bytes,
    super::super::protocol::detected_ram_budget(),
    cgroup_limit,
    cells,
  )?;
  let pool = RecordPool::for_provers(
    host.records,
    host.initial,
    ProverBudget { trace_cells: cells, host_workspace: host.workspace },
  )
  .with_record_limit(record_max_bytes);
  say(&format!(
    "host budget {} GiB process-wide (requested {} GiB per GPU, visible cgroup limit {}): {} GiB shared records, {} GiB workspace per GPU, {} GiB headroom; {executions} CPU executions, {} prepared queue slots; {} GiB initial reservation, growth waits for shared capacity; {cells} trace cells",
    format_gib(host.limit),
    format_gib(cfg.max_ram_bytes),
    cgroup_limit.map_or_else(
      || "unlimited or unavailable".into(),
      |bytes| format!("{} GiB", format_gib(bytes))
    ),
    format_gib(host.records),
    format_gib(host.workspace),
    format_gib(host.headroom),
    cfg.lanes,
    format_gib(host.initial.min(pool.record_limit())),
  ));
  say(&format!(
    "per-record ceiling {} GiB; oversized environment claims are bisected automatically",
    format_gib(pool.record_limit())
  ));

  // A prover pair per device, sharing the bytecode of the systems the
  // CLI built. The verifying keys must not depend on the device: every
  // cache key and claim binding is derived from them.
  say(&format!("building {} resident workers", cfg.lanes));
  let systems: Vec<(AiurSystem, AiurSystem)> = (0..cfg.lanes)
    .map(|g| {
      let device =
        i32::try_from(g).map_err(|error| format!("lane {g}: {error}"))?;
      Ok((ixvm.on_device(device), aggr.on_device(device)))
    })
    .collect::<Result<_, String>>()?;
  for (g, (worker_ixvm, worker_aggr)) in systems.iter().enumerate() {
    let same =
      aiur::vk_codec::aiur_system_to_bytes(worker_ixvm).ok().as_deref()
        == Some(ixvm_vk.as_slice())
        && aiur::vk_codec::aiur_system_to_bytes(worker_aggr).ok().as_deref()
          == Some(aggr_vk.as_slice());
    if !same {
      return Err(format!(
        "the verifying key of the prover on device {g} differs from device 0's"
      ));
    }
  }

  Ok(Pass {
    prepared,
    specs,
    ixvm_vk,
    aggr_vk,
    allowed,
    verify_idx,
    aggr_idx,
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
    pool,
    systems,
  })
}

/// What persisted state fills before a pass dispatches anything: cached
/// joins with the subtrees they retire, and claims the index still proves.
struct Resumed {
  slots: Vec<Option<Arc<Slot>>>,
  retired: Vec<bool>,
  claim_done: Vec<bool>,
}

fn resume_pass(pass: &Pass, ctx: ProveContext<'_>) -> Resumed {
  let count = pass.specs.len();
  let shards = pass.shards();
  // Cached joins from the root down retire their subtrees.
  let mut slots: Vec<Option<Arc<Slot>>> = vec![None; count];
  let mut retired = vec![false; count];
  for index in (0..pass.root_slot).rev() {
    let spec = &pass.specs[index];
    if retired[index] || spec.kind != ChildKind::Aggr {
      continue;
    }
    let Some((proof, address)) =
      load_cached(ctx.aggr_system, ctx.store_dir, ctx.cache_dir, index, spec)
    else {
      continue;
    };
    slots[index] = Some(Arc::new(Slot {
      kind: ChildKind::Aggr,
      statement: spec.statement.clone(),
      outer_claim: spec.outer_claim.clone(),
      proof,
      proof_address: Some(address),
      claims_bytes: serialize_claims(&[&spec.outer_claim]),
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
  let resumed: Vec<Option<Slot>> = (0..shards)
    .into_par_iter()
    .map(|shard| {
      resume_leaf(ctx, &pass.index_dir, pass.leaf_slot[shard], shard)
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
struct Scheduler<'a> {
  pass: &'a Pass,
  manifest: &'a ShardManifest,
  started: Instant,
  slots: Vec<Option<Arc<Slot>>>,
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

impl<'a> Scheduler<'a> {
  fn new(
    pass: &'a Pass,
    manifest: &'a ShardManifest,
    started: Instant,
    resumed: Resumed,
  ) -> Self {
    let Resumed { slots, retired, claim_done } = resumed;
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
  fn children(&self, work: Work) -> Vec<Arc<Slot>> {
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
  fn leaves(&self) -> Vec<Option<Arc<Slot>>> {
    self.pass.leaf_slot.iter().map(|&slot| self.slots[slot].clone()).collect()
  }

  fn handle(&mut self, event: Event) {
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

fn run_manifest(
  cfg: &Config,
  ixvm: &AiurSystem,
  aggr: &AiurSystem,
  env: &ixon::Env,
  manifest: &ShardManifest,
  verify_idx: usize,
  aggr_idx: usize,
  cache_root: &Path,
  record_max_bytes: usize,
  started: Instant,
  pool_stats: &mut PoolStats,
) -> Result<PassOutcome, String> {
  let pass = plan_pass(
    cfg,
    ixvm,
    aggr,
    env,
    manifest,
    verify_idx,
    aggr_idx,
    cache_root,
    record_max_bytes,
  )?;
  let contexts = pass.contexts();
  let resumed = resume_pass(&pass, contexts[0]);

  let (events_tx, events_rx) = mpsc::channel::<Event>();
  let prep_queue = WorkQueue::<Prep>::new(pass.executions);
  let item_queue = WorkQueue::<Item>::new(cfg.lanes);
  let outcome = thread::scope(|scope| -> Result<PassOutcome, String> {
    let _shutdown =
      ShutdownRun { pool: &pass.pool, prep: &prep_queue, items: &item_queue };
    for executor in 0..pass.executions {
      let events = events_tx.clone();
      let (ctx, pass, prep, items) =
        (contexts[0], &pass, &prep_queue, &item_queue);
      scope.spawn(move || {
        prepare_loop(
          ctx,
          executor,
          env,
          &pass.owned,
          pass.wrap_budget,
          prep,
          items,
          &events,
        )
      });
    }
    for (worker, &ctx) in contexts.iter().enumerate() {
      let events = events_tx.clone();
      let (pass, items) = (&pass, &item_queue);
      scope.spawn(move || {
        prove_loop(
          ctx,
          worker,
          &pass.prepared,
          &pass.leaf_slot,
          &pass.index_dir,
          items,
          &pass.pool,
          &events,
        )
      });
    }
    drop(events_tx);

    let mut scheduler = Scheduler::new(&pass, manifest, started, resumed);
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
          verdict = Some(scope.spawn(move || {
            composed_verdict(ixvm, verify_idx, &pass.prepared, &leaves)
          }));
        }
      }
      if scheduler.idle() {
        if scheduler.to_split.is_empty() {
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

/// `AiurSystem.proveLanes`: the whole multi-device run.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_prove_lanes(
  ixvm_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  lanes: LeanNat<LeanBorrowed<'_>>,
  max_ram_bytes: LeanNat<LeanBorrowed<'_>>,
  exec_jobs: LeanNat<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
  cache_fri_bytes: LeanByteArray<LeanBorrowed<'_>>,
  out_manifest: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let cfg = Config {
    lanes: lean_unbox_nat_as_usize(lanes.inner()),
    max_ram_bytes: lean_unbox_nat_as_usize(max_ram_bytes.inner()),
    exec_jobs: lean_unbox_nat_as_usize(exec_jobs.inner()),
    structural_above: lean_unbox_nat_as_usize(structural_above.inner()),
    cache_fri_bytes: cache_fri_bytes.as_bytes().to_vec(),
    out_manifest: (!out_manifest.as_str().is_empty())
      .then(|| PathBuf::from(out_manifest.as_str())),
  };
  if cfg.lanes == 0 {
    return LeanExcept::error_string("at least one lane is required");
  }
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    run(
      &cfg,
      ixvm_system.get(),
      aggr_system.get(),
      &env_handle.get().env,
      Path::new(manifest_path.as_str()),
      lean_unbox_nat_as_usize(verify_idx.inner()),
      lean_unbox_nat_as_usize(aggr_idx.inner()),
    )
  }));
  match result {
    Ok(Ok(root)) => LeanExcept::ok(LeanString::new(&root)),
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "lane scheduler panicked: {}",
      panic_text(&payload)
    )),
  }
}
