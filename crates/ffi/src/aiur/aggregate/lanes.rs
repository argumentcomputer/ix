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

use std::collections::VecDeque;
use std::sync::mpsc;
use std::time::Instant;

use aiur::execute::bind_record_reservation;
use aiur::record_pool::{
  PoolStats, ProverBudget, RecordPool, RecordReservation,
};
use aiur::synthesis::ShardRetention as Retention;
use ixvm_codegen::aiur_ixvm_runner::execute_ixvm;
use ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness;

use super::*;

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

/// The default ceiling on one execution record's counted bytes. 128 GiB
/// holds every Anthropic FLT constant as one claim: the two largest of its
/// single-constant shards are 89.5 and 71.4 GiB, executed to completion
/// without any sign of the query map thrashing (bench/mathlib-seed-2026-09-15
/// and ~/benchdata/flt/probe). `AIUR_RECORD_MAX_BYTES` overrides it.
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
    let _metrics =
      tracing::info_span!(target: "prover_metrics", "aiur/metrics_unit",
      work = ?item.work(), worker)
      .entered();
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

/// Percentile `p` (0–100) of `sorted`, nearest rank; 0 when empty.
fn percentile(sorted: &[usize], p: usize) -> usize {
  if sorted.is_empty() {
    return 0;
  }
  let rank = (sorted.len() * p).div_ceil(100).max(1);
  sorted[rank - 1]
}

/// Observed record sizes and execution times, with a p90-based candidate
/// cut under inverse scaling. The initial reservation is admission credit,
/// not a per-record size limit.
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
#[allow(clippy::cast_sign_loss)]
fn record_summary(
  say: &dyn Fn(&str),
  shards: usize,
  share: Option<usize>,
  record_budget: Option<usize>,
  contention_retries: usize,
  claims: &[(usize, usize, f64)],
  joins: &[(usize, usize, f64)],
) {
  let stats = |units: &[(usize, usize, f64)]| -> Option<String> {
    if units.is_empty() {
      return None;
    }
    let mut bytes: Vec<usize> = units.iter().map(|u| u.1).collect();
    bytes.sort_unstable();
    let total: usize = bytes.iter().sum();
    let (largest_id, largest, _) =
      units.iter().max_by_key(|u| u.1).copied().expect("nonempty");
    let secs: Vec<f64> = units.iter().map(|u| u.2).collect();
    let mean_secs = secs.iter().sum::<f64>() / secs.len() as f64;
    let max_secs = secs.iter().copied().fold(0.0_f64, f64::max);
    Some(format!(
      "{} executed: record mean {} GiB, p50 {} GiB, p90 {} GiB, max {} GiB (unit {largest_id}); execution mean {mean_secs:.1}s, max {max_secs:.1}s",
      units.len(),
      format_gib(total / units.len()),
      format_gib(percentile(&bytes, 50)),
      format_gib(percentile(&bytes, 90)),
      format_gib(largest),
    ))
  };
  if let Some(line) = stats(claims) {
    say(&format!("calibration: claims {line}"));
  }
  if let Some(line) = stats(joins) {
    say(&format!("calibration: joins {line}"));
  }
  let (Some(share), Some(budget)) = (share, record_budget) else {
    say("calibration: no --max-ram, so no share to calibrate against");
    return;
  };
  if claims.len() != shards {
    say(&format!(
      "calibration: shard-count candidate unavailable; measured {} of {shards} claim records in the current partition",
      claims.len()
    ));
    return;
  }
  let largest_claim = claims.iter().map(|u| u.1).max().unwrap_or(0);
  let largest_join = joins.iter().map(|u| u.1).max().unwrap_or(0);
  let mut claim_sizes: Vec<_> = claims.iter().map(|u| u.1).collect();
  claim_sizes.sort_unstable();
  let reanchored = ((shards as f64) * (percentile(&claim_sizes, 90) as f64)
    / (share as f64))
    .ceil() as usize;
  say(&format!(
    "calibration: {shards} shards at a {} GiB initial reservation ({} GiB shared record budget): largest claim record {}% of the initial reservation, largest join record {}%, {contention_retries} contention retry/retries; p90-scaled candidate {reanchored} shard(s) at this initial reservation (claims measured this run only; a resumed run measures fewer)",
    format_gib(share),
    format_gib(budget),
    largest_claim * 100 / share.max(1),
    largest_join * 100 / share.max(1),
  ));
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
  crate::profile::init();
  let say = |m: &str| eprintln!("[lanes] {m}");
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
  let say = |m: &str| eprintln!("[lanes] {m}");
  let prepared = prepare_run(env, manifest)?;
  let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(ixvm)
    .map_err(|error| format!("IxVM VK serialization failed: {error}"))?;
  let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(aggr)
    .map_err(|error| format!("ixAggr VK serialization failed: {error}"))?;
  let allowed = allowed_blob(&ixvm_vk, verify_idx, &aggr_vk, aggr_idx);
  let specs = build_specs(
    &prepared,
    verify_idx,
    aggr_idx,
    cfg.structural_above,
    true,
    &aggr_vk,
    &allowed,
    &cfg.cache_fri_bytes,
  )?;
  let count = specs.len();
  let root_slot = count.checked_sub(1).ok_or("empty plan")?;
  let PlanOp::Join(root_left, root_right) = specs[root_slot].op else {
    return Err("the manifest has one shard; there is nothing to join".into());
  };
  let shards = prepared.shards.len();
  let mut leaf_slot = vec![usize::MAX; shards];
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
  let max_ram_bytes = Some(host.limit);
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

  let contexts: Vec<ProveContext<'_>> = systems
    .iter()
    .map(|(worker_ixvm, worker_aggr)| ProveContext {
      specs: &specs,
      prepared: &prepared.shards,
      proofs: None,
      owner_by_address: &prepared.owner_by_address,
      ixvm_system: worker_ixvm,
      aggr_system: worker_aggr,
      ixvm_vk: &ixvm_vk,
      aggr_vk: &aggr_vk,
      allowed: &allowed,
      verify_idx,
      aggr_idx,
      store_dir: &store_dir,
      cache_dir: Some(&cache_dir),
      reprove_slot: None,
      write_outputs: true,
      wrap_budget: max_ram_bytes,
      range_width: 0,
      range_jobs: 1,
    })
    .collect();

  // Resume: cached joins from the root down retire their subtrees;
  // indexed claim proofs stand in for their claims.
  let mut slots: Vec<Option<Arc<Slot>>> = vec![None; count];
  let mut retired = vec![false; count];
  for index in (0..root_slot).rev() {
    let spec = &specs[index];
    if retired[index] || spec.kind != ChildKind::Aggr {
      continue;
    }
    let Some((proof, address)) = load_cached(contexts[0], index, spec) else {
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
      if let PlanOp::Join(l, r) = specs[slot].op {
        stack.push(l);
        stack.push(r);
      }
    }
  }
  let mut claim_done = vec![false; shards];
  let resumed: Vec<Option<Slot>> = (0..shards)
    .into_par_iter()
    // A claim retired under a cached join is still loaded when the index
    // holds its proof, so the composed verdict can verify it independently.
    .map(|shard| resume_leaf(contexts[0], &index_dir, leaf_slot[shard], shard))
    .collect();
  let mut reused = 0usize;
  for (shard, slot) in resumed.into_iter().enumerate() {
    if let Some(slot) = slot {
      slots[leaf_slot[shard]] = Some(Arc::new(slot));
      claim_done[shard] = true;
      reused += 1;
    } else if retired[leaf_slot[shard]] {
      claim_done[shard] = true;
    }
  }
  let cached_joins = slots
    .iter()
    .enumerate()
    .filter(|(i, s)| {
      s.is_some() && *i != root_slot && !matches!(specs[*i].op, PlanOp::Leaf(_))
    })
    .count();
  say(&format!(
    "{shards} claims ({reused} reused from the index, {} retired under cached joins without an indexed proof), {} joins ({cached_joins} cached)",
    claim_done.iter().filter(|d| **d).count() - reused,
    count - shards
  ));

  let (events_tx, events_rx) = mpsc::channel::<Event>();
  let prep_queue = WorkQueue::<Prep>::new(executions);
  let item_queue = WorkQueue::<Item>::new(cfg.lanes);
  let outcome = thread::scope(|scope| -> Result<PassOutcome, String> {
    let _shutdown =
      ShutdownRun { pool: &pool, prep: &prep_queue, items: &item_queue };
    for executor in 0..executions {
      let events = events_tx.clone();
      let (ctx, owned, prep, items) =
        (contexts[0], &owned, &prep_queue, &item_queue);
      scope.spawn(move || {
        prepare_loop(
          ctx,
          executor,
          env,
          owned,
          max_ram_bytes,
          prep,
          items,
          &events,
        )
      });
    }
    for (worker, &ctx) in contexts.iter().enumerate() {
      let events = events_tx.clone();
      let (prepared_run, leaf_slot, index_dir, items, pool) =
        (&prepared, &leaf_slot, &index_dir, &item_queue, &pool);
      scope.spawn(move || {
        prove_loop(
          ctx,
          worker,
          prepared_run,
          leaf_slot,
          index_dir,
          items,
          pool,
          &events,
        )
      });
    }
    drop(events_tx);

    let mut claim_queue: VecDeque<usize> =
      (0..shards).filter(|&s| !claim_done[s]).collect();
    let work_name = |work: Work| match work {
      Work::Claim(shard) => {
        format!("claim {}", prepared.shards[shard].original_id)
      },
      Work::Join(slot) => format!("join {slot}"),
      Work::Root => "root".to_string(),
    };
    let mut dispatched: FxHashSet<usize> = FxHashSet::default();
    let mut claim_records = Vec::new();
    let mut join_records = Vec::new();
    let mut contention_retries = 0usize;
    let mut root_dispatched = false;
    let mut root_address = None;
    let mut failure = None;
    let mut to_split = std::collections::BTreeSet::new();
    let mut free_executors = executions;
    let mut in_flight = 0usize;
    let mut verdict: Option<
      thread::ScopedJoinHandle<'_, (Vec<String>, usize)>,
    > = None;
    let ready_join = |slots: &[Option<Arc<Slot>>],
                      dispatched: &FxHashSet<usize>| {
      (0..root_slot).find(|&index| {
        !retired[index]
          && slots[index].is_none()
          && !dispatched.contains(&index)
          && match specs[index].op {
            PlanOp::Join(l, r) => slots[l].is_some() && slots[r].is_some(),
            PlanOp::Leaf(_) => false,
          }
      })
    };
    loop {
      while free_executors > 0 && to_split.is_empty() {
        let work = if let Some(slot) = ready_join(&slots, &dispatched) {
          Work::Join(slot)
        } else if !root_dispatched
          && claim_done.iter().all(|d| *d)
          && slots[root_left].is_some()
          && slots[root_right].is_some()
        {
          Work::Root
        } else if let Some(&shard) = claim_queue.front() {
          Work::Claim(shard)
        } else {
          break;
        };
        let Some(reservation) =
          pool.try_admit().map_err(|e| format!("record admission: {e:?}"))?
        else {
          break;
        };
        let children = match work {
          Work::Claim(_) => Vec::new(),
          Work::Join(slot) => {
            let PlanOp::Join(l, r) = specs[slot].op else { unreachable!() };
            vec![slots[l].clone().unwrap(), slots[r].clone().unwrap()]
          },
          Work::Root => vec![
            slots[root_left].clone().unwrap(),
            slots[root_right].clone().unwrap(),
          ],
        };
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
        free_executors -= 1;
        in_flight += 1;
        say(&format!(
          "{} dispatched at +{}s",
          work_name(work),
          started.elapsed().as_secs()
        ));
        match work {
          Work::Claim(_) => {
            claim_queue.pop_front();
          },
          Work::Join(slot) => {
            dispatched.insert(slot);
          },
          Work::Root => {
            root_dispatched = true;
            if verdict.is_none() {
              let leaves: Vec<_> =
                (0..shards).map(|s| slots[leaf_slot[s]].clone()).collect();
              let prepared_run = &prepared;
              verdict = Some(scope.spawn(move || {
                composed_verdict(ixvm, verify_idx, prepared_run, &leaves)
              }));
            }
          },
        }
      }
      if in_flight == 0 && free_executors == executions {
        if !to_split.is_empty() {
          break;
        }
        failure = Some(
          "scheduler stalled: nothing runs and nothing can be admitted"
            .to_string(),
        );
        break;
      }
      let event =
        events_rx.recv().map_err(|e| format!("worker channel closed: {e}"))?;
      match event {
        Event::ExecutionStarted { executor, work } => say(&format!(
          "executor {executor}: {} execution started at +{}s",
          work_name(work),
          started.elapsed().as_secs(),
        )),
        Event::Prepared { executor, work, record_bytes, secs } => {
          say(&format!(
            "executor {executor}: {} executed in {secs:.1}s, record {record_bytes} B ({} GiB) at +{}s",
            work_name(work),
            format_gib(record_bytes),
            started.elapsed().as_secs(),
          ));
          match work {
            Work::Claim(shard) => claim_records.push((
              usize::try_from(prepared.shards[shard].original_id)
                .unwrap_or(usize::MAX),
              record_bytes,
              secs,
            )),
            Work::Join(slot) => join_records.push((slot, record_bytes, secs)),
            Work::Root => join_records.push((root_slot, record_bytes, secs)),
          }
        },
        Event::PrepAvailable => {
          free_executors += 1;
        },
        Event::PrepFailed { executor, work, failure: error } => {
          free_executors += 1;
          in_flight -= 1;
          match error {
            PrepareFailure::MemoryContention => {
              contention_retries += 1;
              say(&format!(
                "executor {executor}: {} released for memory contention; requeued",
                work_name(work)
              ));
              match work {
                Work::Claim(shard) => claim_queue.push_back(shard),
                Work::Join(slot) => {
                  dispatched.remove(&slot);
                },
                Work::Root => {
                  root_dispatched = false;
                },
              }
            },
            PrepareFailure::OverRecordCap { bytes, cap } => {
              if let Work::Claim(shard) = work {
                let id = prepared.shards[shard].original_id;
                let source = manifest
                  .shards
                  .iter()
                  .find(|s| s.id == id)
                  .expect("prepared claim belongs to the manifest");
                if source.blocks.len() > 1 {
                  to_split.insert(id);
                  say(&format!(
                    "claim {id}: record needs {bytes} B, above the {cap} B per-record ceiling; draining active work before splitting this claim"
                  ));
                } else {
                  failure = Some(format!(
                    "claim {id}: record needs {bytes} B, above the {cap} B per-record ceiling; its single atomic block cannot be split further"
                  ));
                }
              } else {
                failure = Some(format!(
                  "{}: aggregation record needs {bytes} B, above the {cap} B per-record ceiling; an aggregation execution cannot be split as an environment claim",
                  work_name(work)
                ));
              }
            },
            PrepareFailure::Other(error) => {
              failure = Some(format!("{}: {error}", work_name(work)))
            },
          }
        },
        Event::Proving { worker, work } => say(&format!(
          "worker {worker}: {} proving started at +{}s",
          work_name(work),
          started.elapsed().as_secs(),
        )),
        Event::Proven { worker, work, result } => {
          in_flight -= 1;
          match (work, result) {
            (Work::Claim(shard), Ok(slot)) => {
              slots[leaf_slot[shard]] = Some(slot);
              claim_done[shard] = true;
              say(&format!(
                "worker {worker}: claim {} proven at +{}s ({} left)",
                prepared.shards[shard].original_id,
                started.elapsed().as_secs(),
                claim_done.iter().filter(|d| !**d).count()
              ));
            },
            (Work::Join(slot), Ok(proof)) => {
              slots[slot] = Some(proof);
              say(&format!(
                "worker {worker}: join {slot} published at +{}s",
                started.elapsed().as_secs()
              ));
            },
            (_, Err(error)) => {
              failure = Some(format!("{}: {error}", work_name(work)))
            },
            (Work::Root, Ok(_)) => {
              unreachable!("root reports through RootProven")
            },
          }
        },
        Event::RootProven { worker, result } => match result {
          Ok(address) => {
            say(&format!(
              "worker {worker}: root proven at +{}s",
              started.elapsed().as_secs()
            ));
            root_address = Some(address);
          },
          Err(error) => failure = Some(format!("root: {error}")),
        },
      }
      if failure.is_some() || root_address.is_some() {
        break;
      }
    }
    drop(_shutdown);
    if let Some(error) = failure {
      return Err(format!(
        "{error}; rerun the same command to resume from what was persisted"
      ));
    }
    if !to_split.is_empty() {
      return Ok(PassOutcome::Refine(to_split.into_iter().collect()));
    }
    let root = root_address.ok_or("no root proof")?;
    record_summary(
      &say,
      shards,
      Some(host.initial.min(pool.record_limit())),
      Some(host.records),
      contention_retries,
      &claim_records,
      &join_records,
    );
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
  let stats = pool.stats();
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
