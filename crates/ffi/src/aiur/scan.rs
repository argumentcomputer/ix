//! Whole-env execution as a SPAN-FLEET: single-writer records, inline
//! multiplicity accumulation, and direct span proving.
//!
//! [`execute_env`] runs the env's whole check schedule through the
//! codegen'd circuit kernel: each worker owns a PRIVATE record and
//! WARM-executes one `verify_block` per schedule block into it —
//! per-block checking keyed by address alone — counting every
//! consumption inline through the record's atomic cells, exactly as
//! the interpreter does. One writer per record means the counts are
//! exact at execution: there is NO seal-time derivation pass. When a
//! record crosses the measured cut the worker seals the span ITSELF —
//! it runs the span's ONE seal claim, its canonical `CheckEnv` claim
//! (owned-set root + thin-frontier assumption root), whose per-node
//! checks memo-hit (and consume) the warm work, then debumps the
//! harness's own per-block calls and retracts any dead warm subgraphs
//! ([`aiur::trace::cancel_dead_roots`]), landing on exactly the counts
//! a from-scratch derivation would produce. Sealing on the worker is
//! what overlaps seal work with execution: the other workers keep
//! executing while one seals, so there is no post-execution seal tail
//! (measured 26s of a 72s init wall under a handoff pipeline). The
//! schedule is a min-cut linearization of the env's reference graph;
//! workers claim contiguous GRANULES of it, which keeps each record
//! cone-cohesive and confines cross-worker duplication to granule
//! boundaries — the same duplication spans already accept at their own
//! boundaries. When the schedule runs dry, idle workers STEAL by
//! bisecting the largest range still in progress, so the endgame
//! rebalances the schedule's heavy cone clusters instead of idling
//! behind them.
//!
//! Two prove entrypoints share the engine, and neither adapts in-run:
//!
//! - [`execute_shards`] is the CLUSTER path: each `.ixes` shard of the
//!   static min-cut planner (`ix shard`) is an immutable work unit a
//!   box runs whole — execute the shard's owned blocks warm (one
//!   thread, one record), seal ONE CheckEnv claim, debump/cancel,
//!   measure the witness EXACTLY, and prove behind the measured gate.
//!   A shard that measures over the box's budget fails with the stable
//!   code `AIUR_SHARD_OVER_BUDGET` so a scheduler can re-partition it
//!   statically (claim composition makes any re-split sound); the box
//!   itself never splits, probes, or heals.
//! - Whole-env mode cuts execution spans on the record's retained
//!   bytes — a smooth, small quantity — sized conservatively so each
//!   span is ONE proof, sealed and gated exactly the same way.
//!
//! Nothing is predicted and nothing is stateful across spans or
//! shards: every prove decision is a measurement of the sealed record
//! at hand, and nothing over-budget ever reaches a STARK.
//!
//! Witness bytes are served lazily through the run-wide [`SharedIO`]
//! layer (`EnvFaultSource`): claim wires are seeded up front in
//! schedule order, constant/hint/blob bytes materialize into
//! env-canonical preassigned slots on first fault.
//!
//! What crosses a span boundary: only re-derivation of the thin
//! long-range shared tail (the span's claims are a contiguous
//! schedule range). Constants are order-independent obligations;
//! cross-span soundness is per-claim, exactly as executed.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;

use aiur::G;
use aiur::{
  bytecode::Toplevel,
  execute::{
    IOBuffer, QueryRecord, f64_from_usize, record_fft_cost,
    record_retained_bytes,
  },
  synthesis::AiurSystem,
};

use ix_common::address::Address;
use ix_kernel::profile::{OpCounts, ProfileBuilder};
use ix_kernel::shard::{Hypergraph, ShardManifest};
use ixon::env::Env as IxonEnv;
use ixvm_codegen::aiur_ixvm_runner::execute_ixvm_with_record;
use ixvm_codegen::aiur_ixvm_witness::{EnvFaultSource, addr_key};
use lean_ffi::object::{
  LeanBorrowed, LeanExcept, LeanExternal, LeanNat, LeanOwned, LeanString,
};
use multi_stark::p3_field::PrimeCharacteristicRing;

/// Bytes per GiB.
const GIB: f64 = 1_073_741_824.0;

/// Prove-mode execution-span cut, as a fraction of the budget on the
/// record's RETAINED bytes. In whole-env prove mode every span is one
/// proof: the span's witness must fit the budget, and
/// witness-to-retained ratios measured 18-28x across the
/// init/FLT/Mathlib campaigns (with the racing cut overshooting the
/// retained line by up to ~30%), so 0.02 bounds the worst measured
/// combination under the budget with margin. Conservative fill is the
/// price of a stateless in-run design; sizing work to a box precisely
/// is the cluster pipeline's job (`ix shard` + `ix prove --shards`).
/// Efficiency-only — the exact measured gate enforces the budget.
const EXEC_RETAINED_FRAC: f64 = 0.02;

/// The RAM model's measured residual: real STARK proves at campaign
/// scale ran +1.6% (FLT shard 12) and +1.7% (Mathlib shard 153) over
/// `peak_prove_bytes` — allocator and process overhead the analytic
/// model does not carry. The budget absorbs it so `peak <= budget`
/// stays sufficient on the real box.
const MODEL_RESIDUAL: f64 = 0.02;

/// The run's RAM budget, measured at call time: `MemAvailable` — the
/// kernel's own estimate of what this process can take without
/// swapping, which already excludes the kernel, other processes, and
/// unreclaimable cache — less the model residual. `IX_SCAN_RAM_GIB`
/// overrides the budget directly (tests, emulating a smaller box).
/// Nothing here is guessed: the one constant is measured
/// ([`MODEL_RESIDUAL`]).
fn measured_budget_gib() -> Result<f64, String> {
  if let Ok(v) = std::env::var("IX_SCAN_RAM_GIB") {
    return v.parse::<f64>().map_err(|e| format!("IX_SCAN_RAM_GIB: {e}"));
  }
  let s = std::fs::read_to_string("/proc/meminfo")
    .map_err(|e| format!("/proc/meminfo: {e}"))?;
  let kib: f64 = s
    .lines()
    .find_map(|l| l.strip_prefix("MemAvailable:"))
    .and_then(|r| r.trim().trim_end_matches("kB").trim().parse().ok())
    .ok_or("no MemAvailable in /proc/meminfo")?;
  Ok(kib / 1024.0 / 1024.0 * (1.0 - MODEL_RESIDUAL))
}

/// Current process resident set in GiB (`/proc/self/status` VmRSS);
/// 0 where unreadable (non-Linux). Reported in span logs.
fn process_rss_gib() -> f64 {
  let Ok(s) = std::fs::read_to_string("/proc/self/status") else {
    return 0.0;
  };
  let Some(rest) = s.lines().find_map(|l| l.strip_prefix("VmRSS:")) else {
    return 0.0;
  };
  let kib: f64 =
    rest.trim().trim_end_matches("kB").trim().parse().unwrap_or(0.0);
  kib / 1024.0 / 1024.0
}

/// One block of the static schedule: home address, member constants,
/// serialized size.
struct SchedBlock {
  addr: Address,
  members: Vec<Address>,
  size: u64,
}

/// Fold the env's constants into home blocks (projections and mutual
/// members attribute to their block), with member lists, sizes, and the
/// block-level reference adjacency — all static structure, no execution.
fn schedule_blocks(env: &IxonEnv) -> (Vec<SchedBlock>, Vec<Vec<u32>>) {
  // Pass 1: home address per constant. A projection folds into its
  // declared block ONLY when its coordinates are valid there (see
  // `crate::kernel::canonical_prj_fold`): a projection's serialized
  // content is exactly those coordinates, so validity makes it THE
  // canonical wrapper the block's own check covers. Anything else
  // keeps its own schedule block, so its `verify_block` claim runs and
  // the kernel rejects it — folding on the declared block address
  // alone would count a counterfeit wrapper as covered without any
  // claim ever loading it.
  let mut home: FxHashMap<Address, Address> = FxHashMap::default();
  for entry in env.consts.iter() {
    let (addr, lazy) = (entry.key(), entry.value());
    let Ok(c) = lazy.get() else { continue };
    let h = crate::kernel::canonical_prj_fold(env, &c.info)
      .unwrap_or_else(|| addr.clone());
    home.insert(addr.clone(), h);
  }
  // Pass 2: block table (sorted for determinism) + members + sizes.
  let mut blocks: FxHashMap<Address, SchedBlock> = FxHashMap::default();
  for entry in env.consts.iter() {
    let (addr, _lazy) = (entry.key(), entry.value());
    let h = home[addr].clone();
    let size = env.get_const_bytes(&h).map_or(0, |b| b.len() as u64);
    let b = blocks.entry(h.clone()).or_insert_with(|| SchedBlock {
      addr: h.clone(),
      members: Vec::new(),
      size,
    });
    b.members.push(addr.clone());
  }
  let mut list: Vec<SchedBlock> = blocks.into_values().collect();
  list.sort_by(|a, b| a.addr.cmp(&b.addr));
  for b in &mut list {
    b.members.sort();
  }
  let id_of: FxHashMap<&Address, u32> = list
    .iter()
    .enumerate()
    .map(|(i, b)| (&b.addr, u32::try_from(i).expect("block count exceeds u32")))
    .collect();
  // Pass 3: block-level ref adjacency (constant refs folded to home blocks).
  let mut adj: Vec<Vec<u32>> = vec![Vec::new(); list.len()];
  for entry in env.consts.iter() {
    let (addr, lazy) = (entry.key(), entry.value());
    let Ok(c) = lazy.get() else { continue };
    let Some(&hid) = id_of.get(&home[addr]) else { continue };
    for r in &c.refs {
      if let Some(rh) = home.get(r)
        && let Some(&rid) = id_of.get(rh)
        && rid != hid
      {
        adj[hid as usize].push(rid);
      }
    }
  }
  for row in &mut adj {
    row.sort_unstable();
    row.dedup();
  }
  (list, adj)
}

/// A min-cut linearization of the block graph: hypergraph-partition the
/// blocks (weights = serialized bytes riding the `intern` counter slot,
/// nets = the ref edges) into `pieces`, then concatenate pieces in id
/// order with address order inside each. The partition minimizes
/// cross-piece closure overlap, so concatenation keeps
/// closure-overlapping blocks adjacent — the memoization-locality
/// property the schedule exists to provide.
fn static_order(
  blocks: &[SchedBlock],
  adj: &[Vec<u32>],
  pieces: usize,
) -> Vec<u32> {
  let mut b = ProfileBuilder::new();
  for blk in blocks {
    let ops = OpCounts { intern_nodes: blk.size, ..OpCounts::default() };
    b.block(
      blk.addr.clone(),
      0,
      u32::try_from(blk.size).expect("block size exceeds u32"),
      u32::try_from(blk.members.len()).expect("member count exceeds u32"),
      ops,
    );
  }
  for (i, row) in adj.iter().enumerate() {
    for &r in row {
      b.delta_edge(blocks[i].addr.clone(), blocks[r as usize].addr.clone());
    }
  }
  let profile = b.finish();
  // ProfileBuilder sorts by address and `blocks` is address-sorted, so ids
  // coincide; assert the invariant the whole mapping rests on.
  assert_eq!(profile.num_blocks(), blocks.len());
  let shard_of = Hypergraph::from_profile(&profile).partition(pieces, 0.05);
  let mut order: Vec<u32> = (0..u32::try_from(blocks.len())
    .expect("block count exceeds u32"))
    .collect();
  order.sort_by_key(|&i| (shard_of[i as usize], i));
  order
}

/// The min-cut schedule order, windowed by the `IX_SCAN_SKIP_BLOCKS` /
/// `IX_SCAN_LIMIT_BLOCKS` debug knobs (a full-pipeline reproducer over a
/// slice of a huge env, without extracting one; the result then does NOT
/// cover the env). Skip drops the order's head, limit truncates what
/// remains — composed, they select any window.
fn ordered_schedule(
  blocks: &[SchedBlock],
  adj: &[Vec<u32>],
  n_chunks: usize,
) -> Vec<u32> {
  let mut order = static_order(blocks, adj, n_chunks.max(16));
  if let Some(skip) = std::env::var("IX_SCAN_SKIP_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .filter(|&n| n > 0)
  {
    let skip = skip.min(order.len());
    eprintln!(
      "[scan] IX_SCAN_SKIP_BLOCKS={skip}: executing a schedule SUFFIX — \
       the result will not cover the env"
    );
    order.drain(..skip);
  }
  if let Some(limit) = std::env::var("IX_SCAN_LIMIT_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    && limit < order.len()
  {
    eprintln!(
      "[scan] IX_SCAN_LIMIT_BLOCKS={limit}: executing a schedule PREFIX — \
       the result will not cover the env"
    );
    order.truncate(limit);
  }
  order
}

/// Publish the canonical env-derived io layout into `shared_io`:
/// constant (ch 2), hint (ch 3), and blob (ch 4) slots preassigned in
/// address order — labels are independent of fault interleaving, and
/// bytes fault into their fixed slots on first use.
fn preassign_canonical_io(env: &IxonEnv, shared_io: &aiur::execute::SharedIO) {
  let key = |a: &Address| -> Vec<G> {
    a.as_bytes().iter().map(|b| G::from_u8(*b)).collect()
  };
  let mut consts: Vec<(Address, usize)> = env
    .consts
    .iter()
    .map(|e| (e.key().clone(), e.value().raw_bytes().len()))
    .collect();
  consts.sort_by(|a, b| a.0.cmp(&b.0));
  for (a, len) in &consts {
    shared_io.preassign(G::from_u8(2), key(a), *len);
  }
  let mut hints: Vec<Address> =
    env.anon_hints.iter().map(|e| e.key().clone()).collect();
  hints.sort();
  for a in &hints {
    shared_io.preassign(G::from_u8(3), key(a), 1);
  }
  let mut blobs: Vec<(Address, usize)> =
    env.blobs.iter().map(|e| (e.key().clone(), e.value().len())).collect();
  blobs.sort_by(|a, b| a.0.cmp(&b.0));
  for (a, len) in &blobs {
    shared_io.preassign(G::from_u8(4), key(a), *len);
  }
}

/// The seal claim: the span's canonical `CheckEnv` claim — owned-set
/// tree root plus thin-frontier assumption root, the same claim shape
/// (and digest) `ix verify` binds shard proofs to — executed through
/// `verify_claim` into the warm `record`. Its per-node checks memo-hit
/// the `verify_block` warm-up; the env walk and assumption-tree
/// recomputation are the claim's own in-circuit work. `owned` is the
/// member-constant set of the span's blocks; the frontier closure walk
/// runs host-side in parallel Rust. Returns the canonical claim and its
/// input (the claim digest key) on success.
fn run_check_env_claim(
  toplevel: &Toplevel,
  fun_idx: usize,
  shared_io: &Arc<aiur::execute::SharedIO>,
  record: &QueryRecord,
  env: &Arc<IxonEnv>,
  owned: &[Address],
) -> Result<(ixon::proof::Claim, Vec<G>), String> {
  let mut io = IOBuffer::with_shared(shared_io.clone());
  let (claim, input) =
    ixvm_codegen::aiur_ixvm_witness::seed_shard_check_env_claim(
      env, owned, &mut io,
    )?;
  execute_ixvm_with_record(toplevel, fun_idx, &input, &mut io, record)
    .map(|_| (claim, input))
    .map_err(|e| e.to_string())
}

/// Persist a proven unit as an `Ixon.Proof` wrapper (its canonical
/// CheckEnv claim plus the opaque proof bytes) in the content-addressed
/// store, returning the wrapper's address — the hex `ix verify` takes,
/// and the artifact a box ships for aggregation. Takes the ALREADY-ENCODED
/// proof: `AiurProof::to_bytes` is a full re-encode into a fresh buffer, and
/// at multi-MiB proof sizes it runs at the peak-RSS moment of the run, so the
/// caller encodes once and reuses those bytes for its own size reporting.
fn store_proof(
  claim: &ixon::proof::Claim,
  proof_bytes: Vec<u8>,
) -> Result<Address, String> {
  let mut buf: Vec<u8> = Vec::with_capacity(proof_bytes.len() + 128);
  let wrapper = ixon::proof::Proof { claim: claim.clone(), proof: proof_bytes };
  wrapper.put(&mut buf);
  ix_compile::store::Store::write(&buf)
    .map_err(|e| format!("store write: {e:?}"))
}

/// Share of the RAM budget, in permille, that the execution pipeline
/// may hold in live span records. This is a CAP, and since the local
/// walk made derivation cheap it is no longer the binding constraint:
/// records drain faster than the controller dispatches them, so peak
/// RSS levels off around 80 GiB whatever the cap is. Measured on init
/// at a 400 GiB budget, wall against peak RSS: depth 1 87.0s/47.8 GiB,
/// 2 74.1s/58.1, 3 71.9s/67.5, 4 71.3s/79.4, 6 67.8s/79.3, 8
/// 68.5s/83.6, 12 68.8s/84.3.
///
/// Depth 6 is where init's wall stops improving and it costs init
/// nothing, but init is the env where the cap stops binding. The
/// bigger envs still bind, and there the same step is a bad trade:
/// initstd 120.3s/79.9 GiB at depth 4 against 119.4s/100.1 GiB at
/// depth 6, lean 160.7s/82.3 against 154.5s/103.7. So this sits at
/// depth 4 — 200 permille — which holds every env near 80 GiB for a
/// wall difference at the edge of run-to-run noise.
const PIPELINE_BUDGET_PERMILLE: usize = 200;

/// How many SEALED, MEASURED span records may queue for the prove
/// thread at once (prove mode only — dry-run has no queue: workers
/// seal, measure and drop their own records). Records are the queue's
/// memory, each bounded by `cut_bytes`, on top of the `workers`
/// records in execution — the six-record allowance absorbs the ones
/// in handoff and the arenas not yet unmapped. `IX_PIPELINE_DEPTH`
/// overrides.
fn pipeline_depth(budget_bytes: usize, cut_bytes: usize) -> usize {
  if let Some(d) = std::env::var("IX_PIPELINE_DEPTH")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
  {
    return d.max(1);
  }
  // Records first, share second: dividing the budget by the permille
  // before the record size truncates away the boundary (at 400 GiB the
  // rounding alone cost a whole level of depth).
  let live = budget_bytes / cut_bytes.max(1) * PIPELINE_BUDGET_PERMILLE / 1000;
  live.saturating_sub(6).clamp(1, 16)
}

/// One SEALED span in flight from its execution worker to the prove
/// thread (prove mode only): the PRIVATE record the worker filled and
/// sealed (inline-accumulated counts, single writer throughout its
/// life — the prove thread becomes the sole owner on receive), the
/// span's canonical claim and its input key, how many schedule blocks
/// it owns, and its exact measured witness peak.
struct ProvableSpan {
  gi: usize,
  record: QueryRecord,
  ixon_claim: ixon::proof::Claim,
  input: Vec<G>,
  owned_len: usize,
  exact: usize,
}

/// Default worker width when `--jobs` is unset: all logical CPUs less
/// one (the watcher).
///
/// A 16-worker cap once shipped here, because the shared record was
/// L3-capacity-bound and extra workers evicted each other's hot sets
/// (init measured 159s at 16 vs 203s at 63). That inversion is GONE
/// under the per-block warmup + single-CheckEnv-claim engine: measured
/// on this box (32 physical cores, SMT, 480 MiB L3), init runs 238s at
/// 8, 209s at 16 and 188s at 63, and initstd 408s / 358s / 327s — both
/// monotone in width, so the cap is not reinstated. Scaling is still
/// far from linear (init is only 3.2x over one worker); the remaining
/// ceiling is the shared record itself, not worker count, so it wants
/// a structural fix rather than a width limit.
///
/// The width is also the aggregate the per-thread probe caches are
/// sized against, and what the executor spawns; nothing else derives
/// from it.
fn default_worker_width() -> usize {
  std::thread::available_parallelism()
    .map_or(4, usize::from)
    .saturating_sub(1)
    .max(1)
}

/// Whole-env check schedule through the codegen'd kernel in parallel.
/// `fun_idx` is `verify_claim` (the single per-span seal claim run at
/// seal), `block_fun_idx` is `verify_block` (the per-block entry the
/// workers warm-execute). Spans are cut at the retained-bytes
/// threshold and each sealed record proceeds straight to a verified
/// multi-claim STARK — or, under `dry_run`, stops at witness
/// generation and reports that span's EXACT measured peak.
#[allow(clippy::too_many_arguments)]
pub fn execute_env(
  toplevel: &Toplevel,
  fun_idx: usize,
  block_fun_idx: usize,
  env: &Arc<IxonEnv>,
  workers: usize,
  fail_fast: bool,
  dry_run: bool,
  system: &AiurSystem,
) -> Result<String, String> {
  // Span-fleet: parallelism comes from workers each filling a PRIVATE
  // record over their own contiguous slice of the schedule. Worker
  // width defaults to the machine, and the env decode cache exists
  // once behind the shared io layer.
  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  // Default: the L3 knee, not the core count. The shared record is
  // L3-capacity-bound — past the knee workers evict each other's hot
  // sets and the wall INVERTS (measured on this env: 159s at 16 vs
  // 203s at 63). An explicit --jobs is always honored.
  let workers = if workers == 0 { default_worker_width() } else { workers };
  // The schedule granularity is fixed by the core count so worker sizing
  // cannot change the block ordering.
  let sched_pieces =
    (std::thread::available_parallelism().map_or(4, usize::from) * 2)
      .min(blocks.len())
      .max(16);
  let order = ordered_schedule(&blocks, &adj, sched_pieces);
  let covered = order.len();
  // The budget feeds ONLY the cut thresholds and the plan/prove sizing
  // below; there is no RSS enforcement here — running under a watchdog
  // or cgroup is the caller's job.
  let budget_gib = measured_budget_gib()?;
  eprintln!(
    "[exec] {covered} blocks, {workers} single-writer span workers, \
     budget {budget_gib:.0} GiB"
  );
  // One shared io state for the whole run: the record memo-couples to
  // io (idx, len) coordinates, so all claims must resolve them against
  // the same arenas (a record never outlives its io). The ingress
  // channels get a canonical env-derived layout (address-sorted
  // preassignment; bytes fault into their fixed slots on first use);
  // claim channels seed on demand through the shared insert-if-absent
  // maps as workers build claims.
  let shared_io =
    Arc::new(aiur::execute::SharedIO::new(EnvFaultSource::new(env.clone())));
  {
    let t = std::time::Instant::now();
    preassign_canonical_io(env, &shared_io);
    eprintln!(
      "[exec] canonical io layout preassigned in {:.1}s",
      t.elapsed().as_secs_f64()
    );
  }
  // SPAN-FLEET execution: every worker owns a PRIVATE record — one
  // writer, ever — and executes contiguous granules of the schedule
  // into it, counting every consumption inline through the record's
  // atomic cells exactly as the interpreter does. When the record
  // crosses the cut the worker seals it off as a span (a self-contained
  // proof unit under its own CheckEnv claim) and starts fresh. There is
  // no shared record, no cross-thread memo, and NO seal-time
  // derivation: counts are exact at execution, modulo the harness's own
  // per-block gauntlet calls, which the seal debumps and — for roots
  // the claim never consumes — retracts via `cancel_dead_roots`.
  //
  // Cross-worker cone sharing is traded away deliberately: two workers
  // whose granules share a dependency cone each execute it into their
  // own record, exactly as two SPANS already re-execute cones shared
  // across their boundary. Granule contiguity in min-cut schedule order
  // is what keeps that duplication span-boundary-sized rather than
  // shard-ingress-sized.
  //
  // Cut points are timing-dependent and machine-local by design: the
  // same machine executes and proves, so spans only need to be sized
  // for its prover, not canonical across machines. The threshold is on
  // retained bytes, capped so all workers' live records together stay
  // inside half the budget.
  let cut_bytes: usize =
    usize::try_from(gib_to_bytes_u64(budget_gib * EXEC_RETAINED_FRAC))
      .unwrap_or(usize::MAX)
      .min(
        usize::try_from(gib_to_bytes_u64(budget_gib / 2.0))
          .unwrap_or(usize::MAX)
          / workers.max(1),
      );
  let budget_bytes: usize =
    usize::try_from(gib_to_bytes_u64(budget_gib)).unwrap_or(usize::MAX);
  let cursor = AtomicUsize::new(0);
  let done = AtomicUsize::new(0);
  let abort = std::sync::atomic::AtomicBool::new(false);
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let fatal: Mutex<Option<String>> = Mutex::new(None);
  let t0 = std::time::Instant::now();
  // Prove-queue depth (prove mode only): how many sealed records may
  // wait for the single prove thread before sealing workers block.
  let depth = pipeline_depth(budget_bytes, cut_bytes);
  // What a span's STARK may measure. Execution never stops for a seal,
  // so while a span proves (workers paused), every worker still holds a
  // partial record bounded by the cut. The gate subtracts them all,
  // because "nothing over-budget reaches a STARK" has to stay exactly
  // true.
  let prove_budget_bytes = if dry_run {
    budget_bytes
  } else {
    budget_bytes.saturating_sub(cut_bytes.saturating_mul(workers))
  };
  let active_workers = AtomicUsize::new(workers);
  // Workers currently inside a block. Only prove mode reads it: there
  // the STARK needs a quiescent RAM baseline, so the post worker sets
  // `pause` and waits for this to drain before measuring and proving.
  let busy = AtomicUsize::new(0);
  let pause = std::sync::atomic::AtomicBool::new(false);
  // Per-worker in-flight block (usize::MAX = idle): lets the stall
  // detector NAME the stuck block(s) — the identity a runaway
  // diagnosis needs.
  let in_flight: Vec<AtomicUsize> =
    (0..workers).map(|_| AtomicUsize::new(usize::MAX)).collect();
  // How many contiguous schedule blocks a worker claims at a time.
  // Contiguity in min-cut order is what keeps a worker's record
  // cone-cohesive (adjacent blocks share dependency cones): swept on
  // init at 63 workers, g=64 duplicates 61% of the FFT work across
  // workers (1636 vs 1015 BFFT) while g=1024 duplicates 9%. Balance is
  // NOT the granule's job — block cost varies enough that one granule
  // can hold a minute of serial work (the min-cut order deliberately
  // clusters heavy cones) — it belongs to range STEALING below, which
  // adds boundaries only where the schedule actually runs dry.
  let granule: usize = std::env::var("IX_SCAN_GRANULE")
    .ok()
    .and_then(|v| v.parse().ok())
    .filter(|&g: &usize| g > 0)
    .unwrap_or(1024);
  // Per-worker in-progress range over `order`, packed (next:32, hi:32)
  // in ONE atomic so the owner's per-block claim and a thief's suffix
  // split serialize through the same CAS — no block is ever executed
  // twice and none is skipped. `next` only rises and `hi` only falls,
  // so the CAS has no ABA. Block indices fit u32 by construction
  // (`order` ids are u32).
  let pack = |n: usize, h: usize| ((n as u64) << 32) | h as u64;
  let unpack = |v: u64| ((v >> 32) as usize, (v & 0xffff_ffff) as usize);
  let ranges: Vec<std::sync::atomic::AtomicU64> =
    (0..workers).map(|_| std::sync::atomic::AtomicU64::new(0)).collect();
  let spans_list: Mutex<Vec<(usize, usize, usize, f64, usize)>> =
    Mutex::new(Vec::new());
  let spans_proven = AtomicUsize::new(0);
  let unproven = AtomicUsize::new(0);
  let span_seq = AtomicUsize::new(0);
  let census: Mutex<String> = Mutex::new(String::new());
  // SEAL runs ON the execution worker that filled the record — it is
  // the record's owner and the machine's other workers keep executing
  // through its seal, so seal work overlaps execution instead of
  // queueing behind it (a handoff pipeline measured a 26s post-only
  // tail on init's 72s wall: nearly every worker's retained sits under
  // the cut, so every span sealed AFTER the schedule drained). The
  // whole span lifecycle short of the STARK happens here: seal claim
  // -> debump/cancel -> exact measure -> and, in dry-run, the drop.
  // Prove mode sends the sealed, measured record to the ONE prove
  // thread, so STARKs serialize behind the pause gate and the measured
  // budget stays exact.
  let seal_span = |prove_tx: Option<
    &std::sync::mpsc::SyncSender<ProvableSpan>,
  >,
                   record: QueryRecord,
                   owned: Vec<u32>,
                   rejects: usize,
                   exec_s: f64| {
    let gi = span_seq.fetch_add(1, Ordering::Relaxed);
    let owned_addrs: Vec<Address> = owned
      .iter()
      .flat_map(|&b| blocks[b as usize].members.iter().cloned())
      .collect();
    let retained = record_retained_bytes(&record);
    let entries: usize = record
      .function_queries
      .iter()
      .map(|m| m.len())
      .sum::<usize>()
      + record.memory_queries.iter().map(|(_, m)| m.len()).sum::<usize>();
    let fft = record_fft_cost(toplevel, &record);
    spans_list.lock().unwrap().push((0, owned.len(), entries, fft, retained));
    if rejects > 0 {
      eprintln!(
        "[prove span {gi}] SKIPPED: {rejects} rejected block(s) — \
         partial records are not proven"
      );
      if !dry_run {
        unproven.fetch_add(1, Ordering::Relaxed);
      }
      return;
    }
    // Seal: the span's canonical CheckEnv claim executes into the warm
    // record (this worker is still its sole writer), consuming the
    // warm work through the same inline counters.
    let t_seal = std::time::Instant::now();
    let sealed = run_check_env_claim(
      toplevel,
      fun_idx,
      &shared_io,
      &record,
      env,
      &owned_addrs,
    );
    let seal_s = t_seal.elapsed().as_secs_f64();
    let (ixon_claim, input) = match sealed {
      Ok(pair) => pair,
      Err(e) => {
        eprintln!("[prove span {gi}] SKIPPED: seal claim failed: {e}");
        if !dry_run {
          unproven.fetch_add(1, Ordering::Relaxed);
        }
        return;
      },
    };
    // Debump the harness's own per-block gauntlet calls (a consumption
    // with no circuit row behind it), then retract the consumption
    // subgraphs of any root the claim itself never consumed — landing
    // on exactly the counts a from-scratch derivation would produce.
    let t_fix = std::time::Instant::now();
    let mut dead_roots: Vec<(usize, Vec<G>)> = Vec::new();
    for &b in &owned {
      let key = addr_key(&blocks[b as usize].addr);
      if record.function_queries[block_fun_idx].debump(&key) == 0 {
        dead_roots.push((block_fun_idx, key));
      }
    }
    let dio = IOBuffer::with_shared(shared_io.clone());
    aiur::trace::cancel_dead_roots(toplevel, &record, &dio, &dead_roots);
    let fix_s = t_fix.elapsed().as_secs_f64();
    let exact = system.peak_prove_bytes(&record).peak;
    eprintln!(
      "[span {gi}] {} blocks, {entries} unique queries, \
       {:.1} BFFT, {:.1} GiB record [exec {exec_s:.1}s, seal \
       {seal_s:.1}s, fix {fix_s:.1}s ({} dead roots)], witness \
       peak {:.1} GiB, {:.0}s",
      owned.len(),
      fft / 1e9,
      f64_from_usize(retained) / GIB,
      dead_roots.len(),
      f64_from_usize(exact) / GIB,
      t0.elapsed().as_secs_f64(),
    );
    if let Ok(path) = std::env::var("IX_EXEC_DUMP_COUNTS") {
      let mut out = format!("span {gi}\n");
      for (i, m) in record.function_queries.iter().enumerate() {
        if !m.is_empty() {
          out.push_str(&format!("fn {i} {}\n", m.len()));
        }
      }
      for (w, m) in &record.memory_queries {
        out.push_str(&format!("mem {w} {}\n", m.len()));
      }
      let mut c = census.lock().unwrap();
      c.push_str(&out);
      let _ = std::fs::write(&path, c.as_str());
    }
    if dry_run {
      eprintln!(
        "[prove span {gi}] DRY: measured witness peak {:.1} GiB — \
         STARK skipped",
        f64_from_usize(exact) / GIB,
      );
      spans_proven.fetch_add(1, Ordering::Relaxed);
      return;
    }
    // Blocking on a full prove queue IS the back-pressure.
    if let Some(tx) = prove_tx {
      let _ = tx.send(ProvableSpan {
        gi,
        record,
        ixon_claim,
        input,
        owned_len: owned.len(),
        exact,
      });
    }
  };
  // Sealed, measured spans ride a BOUNDED channel to the prove thread
  // (prove mode only); a worker that blocks here is the back-pressure
  // that keeps total live records at `workers` in-execution plus
  // `depth` awaiting proof.
  let (sealed_tx, sealed_rx) =
    std::sync::mpsc::sync_channel::<ProvableSpan>(depth);
  std::thread::scope(|sc| {
    // ── stall watcher ────────────────────────────────────────────────
    {
      let (abort, done) = (&abort, &done);
      let active_workers = &active_workers;
      let (in_flight, blocks, order) = (&in_flight, &blocks, &order);
      sc.spawn(move || {
        let mut stall = (usize::MAX, 0u32);
        loop {
          if abort.load(Ordering::Acquire)
            || active_workers.load(Ordering::Acquire) == 0
          {
            break;
          }
          let d = done.load(Ordering::Acquire);
          if d != stall.0 {
            stall = (d, 0);
          } else {
            stall.1 += 1;
            if stall.1.is_multiple_of(120) {
              let stuck: Vec<String> = in_flight
                .iter()
                .filter_map(|a| {
                  let lo = a.load(Ordering::Relaxed);
                  (lo != usize::MAX).then(|| {
                    format!("{}@{lo}", blocks[order[lo] as usize].addr.hex())
                  })
                })
                .collect();
              eprintln!(
                "[watch] STALL: no block completed in {}s; in-flight: {}",
                stall.1 / 2,
                stuck.join(" ")
              );
            }
          }
          std::thread::sleep(std::time::Duration::from_millis(500));
        }
      });
    }
    // ── prove thread (prove mode only): serialized STARKs ───────────
    if !dry_run {
      let sealed_rx = sealed_rx;
      let (abort, pause, busy) = (&abort, &pause, &busy);
      let (spans_proven, unproven, fatal) = (&spans_proven, &unproven, &fatal);
      let shared_io = &shared_io;
      sc.spawn(move || {
        // Recv until the channel CLOSES (all workers done). On abort
        // keep draining and discarding — a worker parked in a full
        // channel's send must never deadlock against an exited prove
        // thread.
        while let Ok(span) = sealed_rx.recv() {
          if abort.load(Ordering::Acquire) {
            continue;
          }
          let ProvableSpan { gi, record, ixon_claim, input, owned_len, exact } =
            span;
          // Stop the box, so the exact measured gate is against a
          // quiescent RAM baseline.
          pause.store(true, Ordering::Release);
          while busy.load(Ordering::Acquire) > 0
            && !abort.load(Ordering::Acquire)
          {
            std::thread::sleep(std::time::Duration::from_millis(1));
          }
          let claims = record.function_queries[fun_idx]
            .get(&input)
            .map(|q| {
              vec![aiur::synthesis::function_claim(fun_idx, &input, q.output)]
            });
          match claims {
            None => {
              eprintln!(
                "[prove span {gi}] SKIPPED: seal claim entry missing \
                 from record"
              );
              unproven.fetch_add(1, Ordering::Relaxed);
            },
            Some(claims) => {
              if exact > prove_budget_bytes {
                eprintln!(
                  "[prove span {gi}] REFUSED: AIUR_SPAN_OVER_BUDGET \
                   span={gi} blocks={owned_len} peak_bytes={exact} \
                   budget_bytes={prove_budget_bytes}",
                );
                unproven.fetch_add(1, Ordering::Relaxed);
              } else {
                let io = IOBuffer::with_shared(shared_io.clone());
                let st = std::time::Instant::now();
                let proof = system.prove_sealed(record, &io, &claims);
                let prove_s = st.elapsed().as_secs_f64();
                let vt = std::time::Instant::now();
                let verified = system.verify_sealed(&claims, &proof);
                let verify_s = vt.elapsed().as_secs_f64();
                match verified {
                  Err(e) => {
                    let mut f = fatal.lock().unwrap();
                    if f.is_none() {
                      *f =
                        Some(format!("span proof failed verification: {e:?}"));
                    }
                    abort.store(true, Ordering::Release);
                  },
                  Ok(()) => match proof
                    .to_bytes()
                    .map_err(|e| format!("proof encode: {e:?}"))
                    .and_then(|bytes| {
                      let n = bytes.len();
                      store_proof(&ixon_claim, bytes).map(|a| (a, n))
                    }) {
                    Err(e) => {
                      let mut f = fatal.lock().unwrap();
                      if f.is_none() {
                        *f = Some(e);
                      }
                      abort.store(true, Ordering::Release);
                    },
                    Ok((stored, proof_len)) => {
                      eprintln!(
                        "[prove span {gi}] prove {prove_s:.0}s, verify \
                         {verify_s:.1}s, proof {:.1} MiB, rss {:.0}G, \
                         stored {}",
                        f64_from_usize(proof_len) / (1024.0 * 1024.0),
                        process_rss_gib(),
                        stored.hex(),
                      );
                      spans_proven.fetch_add(1, Ordering::Relaxed);
                    },
                  },
                }
              }
            },
          }
          pause.store(false, Ordering::Release);
        }
      });
    }
    // ── execution workers: private records, granule cursor ──────────
    for w in 0..workers {
      let in_flight = &in_flight;
      let (cursor, done, abort) = (&cursor, &done, &abort);
      let (failed, fatal, active_workers) = (&failed, &fatal, &active_workers);
      let (busy, pause) = (&busy, &pause);
      let sealed_tx = sealed_tx.clone();
      let (blocks, order, shared_io) = (&blocks, &order, &shared_io);
      let (seal_span, ranges) = (&seal_span, &ranges);
      sc.spawn(move || {
        let mut record = QueryRecord::new(toplevel);
        let mut owned: Vec<u32> = Vec::new();
        let mut rejects = 0usize;
        let mut t_exec = std::time::Instant::now();
        loop {
          while pause.load(Ordering::Acquire) && !abort.load(Ordering::Acquire)
          {
            std::thread::sleep(std::time::Duration::from_millis(1));
          }
          if abort.load(Ordering::Acquire) {
            break;
          }
          let cur = ranges[w].load(Ordering::Acquire);
          let (n, h) = unpack(cur);
          if n >= h {
            // Own range drained: refill from the cursor while granules
            // remain; once IT drains, STEAL — bisect the largest range
            // still in progress anywhere on the box. Block cost
            // variance is real (the min-cut order clusters heavy
            // cones: one granule of init holds a minute of serial
            // work), so the endgame must rebalance or the box idles
            // behind stragglers — measured as a 40s tail on init's
            // 74s wall with no stealing. Each steal adds ONE span
            // boundary's worth of cone duplication, and only where
            // the schedule ran dry.
            let lo = cursor.fetch_add(granule, Ordering::Relaxed);
            if lo < covered {
              ranges[w].store(
                pack(lo, (lo + granule).min(covered)),
                Ordering::Release,
              );
              continue;
            }
            let mut stole = false;
            loop {
              let mut best: Option<(usize, u64, usize, usize)> = None;
              for (v, r) in ranges.iter().enumerate() {
                if v == w {
                  continue;
                }
                let cur = r.load(Ordering::Acquire);
                let (n, h) = unpack(cur);
                // No steal-size floor: swept on init, a 64-block floor
                // left one worker grinding the sub-floor heavy suffix
                // for ~25s of idle-box wall while buying back almost
                // none of the steal duplication (1194 vs 1232 BFFT) —
                // the dup lives in the heavy region's steal boundaries
                // themselves, not in endgame shreds.
                if h.saturating_sub(n) >= 2
                  && best.is_none_or(|(_, _, bn, bh)| h - n > bh - bn)
                {
                  best = Some((v, cur, n, h));
                }
              }
              let Some((v, cur, n, h)) = best else { break };
              let mid = n + (h - n + 1) / 2;
              if ranges[v]
                .compare_exchange(
                  cur,
                  pack(n, mid),
                  Ordering::AcqRel,
                  Ordering::Acquire,
                )
                .is_ok()
              {
                ranges[w].store(pack(mid, h), Ordering::Release);
                stole = true;
                break;
              }
            }
            if !stole {
              break;
            }
            continue;
          }
          // Claim ONE block from the front of the own range. The CAS
          // races only against a thief shrinking `hi`; on loss, rescan.
          if ranges[w]
            .compare_exchange(
              cur,
              pack(n + 1, h),
              Ordering::AcqRel,
              Ordering::Acquire,
            )
            .is_err()
          {
            continue;
          }
          let i = n;
          {
            let b = order[i];
            in_flight[w].store(i, Ordering::Relaxed);
            busy.fetch_add(1, Ordering::AcqRel);
            let run = {
              let mut io = IOBuffer::with_shared(shared_io.clone());
              let input = addr_key(&blocks[b as usize].addr);
              execute_ixvm_with_record(
                toplevel,
                block_fun_idx,
                &input,
                &mut io,
                &record,
              )
            };
            busy.fetch_sub(1, Ordering::AcqRel);
            in_flight[w].store(usize::MAX, Ordering::Relaxed);
            match run {
              Ok(_) => {
                owned.push(b);
                let d = done.fetch_add(1, Ordering::AcqRel) + 1;
                if d.is_multiple_of(8192) {
                  eprintln!(
                    "[exec] {d}/{covered} blocks, rss {:.0}G, {:.0}s",
                    process_rss_gib(),
                    t0.elapsed().as_secs_f64()
                  );
                }
              },
              Err(e) => {
                let e = e.to_string();
                if fail_fast {
                  let mut f = fatal.lock().unwrap();
                  if f.is_none() {
                    *f = Some(format!(
                      "CheckEnv of block {} failed: {e}",
                      blocks[b as usize].addr.hex()
                    ));
                  }
                  abort.store(true, Ordering::Release);
                } else {
                  eprintln!(
                    "[exec] SKIPPING block {}: {e}",
                    blocks[b as usize].addr.hex()
                  );
                  failed
                    .lock()
                    .unwrap()
                    .push((blocks[b as usize].addr.clone(), e));
                  // The failed block still poisons THIS span: it was
                  // meant to be owned here, and a claim over a set
                  // missing it would misstate coverage.
                  owned.push(b);
                  rejects += 1;
                }
              },
            }
            if record_retained_bytes(&record) >= cut_bytes {
              // Seal HERE, on the worker: the other workers keep
              // draining the cursor through this seal.
              seal_span(
                (!dry_run).then_some(&sealed_tx),
                std::mem::replace(&mut record, QueryRecord::new(toplevel)),
                std::mem::take(&mut owned),
                std::mem::take(&mut rejects),
                t_exec.elapsed().as_secs_f64(),
              );
              t_exec = std::time::Instant::now();
            }
          }
        }
        if !owned.is_empty() {
          seal_span(
            (!dry_run).then_some(&sealed_tx),
            record,
            owned,
            rejects,
            t_exec.elapsed().as_secs_f64(),
          );
        }
        active_workers.fetch_sub(1, Ordering::AcqRel);
      });
    }
    // The scope's own sender must go, or the prove thread's recv never
    // sees the channel close.
    drop(sealed_tx);
  });
  let spans_proven = spans_proven.into_inner();
  let unproven_spans = unproven.into_inner();
  let spans = spans_list.into_inner().unwrap();
  if let Some(e) = fatal.into_inner().unwrap() {
    return Err(e);
  }
  let failed = failed.into_inner().unwrap();
  let checked = done.load(Ordering::Acquire);
  let entries: usize = spans.iter().map(|s| s.2).sum();
  let total_fft: f64 = spans.iter().map(|s| s.3).sum();
  let mut report = if spans.len() <= 1 {
    format!(
      "execute: {checked}/{covered} blocks checked into one shared record \
       ({workers} threads), total measured {:.1} BFFT\n{entries} unique \
       queries, record {:.1} GiB retained, {:.0}s",
      total_fft / 1e9,
      f64_from_usize(spans.last().map_or(0, |s| s.4)) / GIB,
      t0.elapsed().as_secs_f64()
    )
  } else {
    // Cut mode: entries sum per-span uniques, so cross-span
    // re-derivation is counted per span — that duplication against
    // the whole-env count IS the price of cutting; report it honestly.
    let max_retained = spans.iter().map(|s| s.4).max().unwrap_or(0);
    format!(
      "execute: {checked}/{covered} blocks checked into {} record \
       spans ({workers} threads), total measured {:.1} BFFT\n\
       {entries} unique queries (per-span sum), largest span \
       {:.1} GiB, {:.0}s",
      spans.len(),
      total_fft / 1e9,
      f64_from_usize(max_retained) / GIB,
      t0.elapsed().as_secs_f64()
    )
  };
  report
    .push_str(&format!("\n  [{spans_proven} span proof(s), one claim each]"));
  if !failed.is_empty() {
    report.push_str(&format!(
      "\n  [{} kernel-rejected block(s) SKIPPED]",
      failed.len()
    ));
    for (a, e) in &failed {
      report.push_str(&format!("\n    {} — {e}", a.hex()));
    }
  }
  // A checker's exit status is its verdict: any kernel reject or
  // unproven span fails the run, keep-going or not. The report
  // (with the full reject inventory) rides in the error.
  if !failed.is_empty() || unproven_spans > 0 {
    return Err(format!(
      "{report}\nFAILED: {} kernel-rejected block(s), {unproven_spans} \
       span(s) not proven",
      failed.len()
    ));
  }
  Ok(report)
}

/// GiB → whole bytes via the decimal round-trip (no `as` cast); caps are
/// small positive magnitudes.
fn gib_to_bytes_u64(gib: f64) -> u64 {
  format!("{:.0}", (gib * GIB).max(0.0)).parse().unwrap_or(u64::MAX)
}

/// Cluster-shard execution: run selected shards of a `.ixes` manifest
/// (the static min-cut plan) as immutable work units. Per shard: its
/// owned blocks execute warm into a fresh record (fixed list, no
/// cutting), the shard's canonical CheckEnv claim seals it,
/// multiplicities derive, the witness peak is measured EXACTLY against
/// this box's budget, and the shard proves behind that gate. Dry mode
/// reports every measurement and skips the STARKs. A shard measuring
/// over budget is left unchanged and fails the run with the stable
/// code `AIUR_SHARD_OVER_BUDGET shard= blocks= peak_bytes=
/// budget_bytes=` — re-partitioning is the scheduler's job (`ix
/// shard` on the offending subgraph; claim composition makes any
/// re-split sound). An all-shards run first checks exact cover of the
/// env schedule; a single-shard run is inherently partial and says so.
#[allow(clippy::too_many_arguments)]
pub fn execute_shards(
  toplevel: &Toplevel,
  fun_idx: usize,
  block_fun_idx: usize,
  env: &Arc<IxonEnv>,
  workers: usize,
  manifest_path: &str,
  shard_sel: Option<usize>,
  dry_run: bool,
  prove_system: Option<&AiurSystem>,
) -> Result<String, String> {
  let system = prove_system.ok_or("shard mode requires a prove system")?;
  let (blocks, _adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  let id_of: FxHashMap<&Address, u32> = blocks
    .iter()
    .enumerate()
    .map(|(i, b)| (&b.addr, u32::try_from(i).expect("block ids fit u32")))
    .collect();
  let manifest_bytes = std::fs::read(manifest_path)
    .map_err(|e| format!("{manifest_path}: {e}"))?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)?;
  if manifest.shards.is_empty() {
    return Err("manifest has no shards".to_string());
  }
  let workers = if workers == 0 { default_worker_width() } else { workers };
  let budget_gib = measured_budget_gib()?;
  let budget_bytes: usize =
    usize::try_from(gib_to_bytes_u64(budget_gib)).unwrap_or(usize::MAX);
  let selected: Vec<usize> = match shard_sel {
    Some(k) => {
      if k >= manifest.shards.len() {
        return Err(format!(
          "--shard {k} out of range ({} shards)",
          manifest.shards.len()
        ));
      }
      vec![k]
    },
    None => (0..manifest.shards.len()).collect(),
  };
  let work: Vec<(usize, Vec<u32>)> = selected
    .iter()
    .map(|&si| {
      let ids: Vec<u32> = manifest.shards[si]
        .blocks
        .iter()
        .map(|a| {
          id_of.get(a).copied().ok_or_else(|| {
            format!("manifest block {} not in env schedule", a.hex())
          })
        })
        .collect::<Result<_, _>>()?;
      Ok((si, ids))
    })
    .collect::<Result<_, String>>()?;
  eprintln!(
    "[shards] {} of {}, single-writer records (--jobs governs \
     shard-level parallelism only), budget {budget_gib:.0} GiB",
    work.len(),
    manifest.shards.len(),
  );
  let _ = workers;
  // Whole-env soundness gate: an all-shards run claims "every env
  // constant checked", so the manifest must own every schedule block
  // exactly once — missing and duplicated blocks both void the claim.
  match shard_sel {
    None => {
      let mut owners = vec![0u32; blocks.len()];
      for (_, ids) in &work {
        for &b in ids {
          owners[b as usize] += 1;
        }
      }
      let missing = owners.iter().filter(|&&c| c == 0).count();
      let dup = owners.iter().filter(|&&c| c > 1).count();
      if missing != 0 || dup != 0 {
        return Err(format!(
          "manifest does not exactly cover the env schedule: {missing} \
           block(s) unowned, {dup} owned more than once (of {} total)",
          blocks.len()
        ));
      }
      eprintln!(
        "[shards] exact cover: {} schedule blocks owned exactly once",
        blocks.len()
      );
    },
    Some(k) => {
      eprintln!("[shards] PARTIAL: shard {k} only — no coverage claim");
    },
  }
  // One shared io for the whole run, exactly as in whole-env mode.
  let shared_io =
    Arc::new(aiur::execute::SharedIO::new(EnvFaultSource::new(env.clone())));
  preassign_canonical_io(env, &shared_io);
  let mut report = String::new();
  let mut failures = 0usize;
  for (si, ids) in work {
    // SINGLE-WRITER execution: the record accumulates every consumption
    // inline (the same semantics the interpreter and the whole-env
    // span-fleet use), so exactness requires exactly one thread. A
    // shard is one proof unit either way; parallelism across a box
    // comes from running SHARDS concurrently (one process each, or the
    // whole-env span-fleet), never from sharing a record.
    let record = QueryRecord::new(toplevel);
    let mut rejects: Vec<(Address, String)> = Vec::new();
    let ts = std::time::Instant::now();
    for &b in &ids {
      let mut io = IOBuffer::with_shared(shared_io.clone());
      let input = addr_key(&blocks[b as usize].addr);
      if let Err(e) = execute_ixvm_with_record(
        toplevel,
        block_fun_idx,
        &input,
        &mut io,
        &record,
      ) {
        eprintln!(
          "[shard {si}] SKIPPING block {}: {e}",
          blocks[b as usize].addr.hex()
        );
        rejects.push((blocks[b as usize].addr.clone(), e.to_string()));
      }
    }
    // Seal: the shard's canonical CheckEnv claim over its owned
    // constants — the claim the shard's proof commits to.
    let mut span_claim: Option<(ixon::proof::Claim, Vec<G>)> = None;
    if rejects.is_empty() {
      let owned: Vec<Address> = ids
        .iter()
        .flat_map(|&b| blocks[b as usize].members.iter().cloned())
        .collect();
      match run_check_env_claim(
        toplevel, fun_idx, &shared_io, &record, env, &owned,
      ) {
        Ok(pair) => span_claim = Some(pair),
        Err(e) => {
          eprintln!("[shard {si}] seal claim failed: {e}");
        },
      }
    }
    let clean = rejects.is_empty() && span_claim.is_some();
    if clean {
      // Counts are already exact from inline accumulation, except the
      // harness's own per-block gauntlet calls: debump each, and
      // retract the consumption subgraph of any root the seal claim
      // never consumed (see `trace::cancel_dead_roots`).
      let mut dead_roots: Vec<(usize, Vec<G>)> = Vec::new();
      for &b in &ids {
        let key = addr_key(&blocks[b as usize].addr);
        if record.function_queries[block_fun_idx].debump(&key) == 0 {
          dead_roots.push((block_fun_idx, key));
        }
      }
      let dio = IOBuffer::with_shared(shared_io.clone());
      aiur::trace::cancel_dead_roots(toplevel, &record, &dio, &dead_roots);
    } else {
      failures += 1;
    }
    let peak = system.peak_prove_bytes(&record).peak;
    let fits = peak <= budget_bytes;
    let line = format!(
      "[shard {si}] {} blocks, exact peak {:.1} GiB {} budget \
       {budget_gib:.0} GiB{}, {:.0}s",
      ids.len(),
      f64_from_usize(peak) / GIB,
      if fits { "<=" } else { "OVER" },
      if clean { "" } else { " [REJECTED BLOCKS — not provable]" },
      ts.elapsed().as_secs_f64(),
    );
    eprintln!("{line}");
    report.push_str(&line);
    report.push('\n');
    if !clean {
      continue;
    }
    if !fits {
      // Immutable work unit: report with the stable code and fail the
      // run (dry mode reports only — the measurement IS its product).
      if !dry_run {
        failures += 1;
        let l = format!(
          "[shard {si}] REFUSED: AIUR_SHARD_OVER_BUDGET shard={si} \
           blocks={} peak_bytes={peak} budget_bytes={budget_bytes}",
          ids.len(),
        );
        eprintln!("{l}");
        report.push_str(&l);
        report.push('\n');
      }
      continue;
    }
    if !dry_run {
      let mut claims: Vec<Vec<G>> = Vec::with_capacity(1);
      if let Some((_, inp)) = &span_claim
        && let Some(q) = record.function_queries[fun_idx].get(inp)
      {
        claims.push(aiur::synthesis::function_claim(fun_idx, inp, q.output));
      }
      let io = IOBuffer::with_shared(shared_io.clone());
      let pt = std::time::Instant::now();
      let proof = system.prove_sealed(record, &io, &claims);
      system
        .verify_sealed(&claims, &proof)
        .map_err(|e| format!("shard {si} proof failed verification: {e:?}"))?;
      let proof_bytes =
        proof.to_bytes().map_err(|e| format!("proof encode: {e:?}"))?;
      let proof_len = proof_bytes.len();
      // Persist: the shard's proof is the artifact a box ships for
      // aggregation, and the address is what `ix verify` consumes.
      let stored = match &span_claim {
        Some((ixon_claim, _)) => store_proof(ixon_claim, proof_bytes)?,
        None => return Err(format!("shard {si}: no claim to store")),
      };
      let pline = format!(
        "[shard {si}] proved+verified in {:.0}s, proof {:.1} MiB, \
         rss {:.0}G, stored {}",
        pt.elapsed().as_secs_f64(),
        f64_from_usize(proof_len) / (1024.0 * 1024.0),
        process_rss_gib(),
        stored.hex(),
      );
      eprintln!("{pline}");
      report.push_str(&pline);
      report.push('\n');
    }
  }
  if failures > 0 {
    return Err(format!(
      "{report}FAILED: {failures} shard(s) rejected, unprovable, or \
       over budget"
    ));
  }
  Ok(report)
}

/// `Aiur.AiurSystem.executeEnvProveWithEnv`: cut-mode whole-env
/// execution where each sealed span record proceeds straight to the
/// STARK and is verified (see [`execute_env`]'s prove path). The
/// record is the witness — no re-execution, no manifest. String
/// params (ABI-simple): `workers` ("0" = default width), `fail_fast`
/// ("0" records and skips rejects), `dry_run` — "1" runs everything
/// except the STARKs and reports each span's exact measured peak.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_execute_env_prove_with_env(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  block_fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  workers: LeanString<LeanBorrowed<'_>>,
  fail_fast: LeanString<LeanBorrowed<'_>>,
  dry_run: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let system = aiur_system_obj.get();
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let block_fun_idx =
    crate::aiur::lean_unbox_nat_as_usize(block_fun_idx.inner());
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let fail_fast = fail_fast.to_string() != "0";
  let dry_run = dry_run.to_string() != "0";
  match execute_env(
    system.toplevel(),
    fun_idx,
    block_fun_idx,
    &env_handle.get().env,
    workers,
    fail_fast,
    dry_run,
    system,
  ) {
    Ok(report) => {
      eprintln!("[rs_exec]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => {
      LeanExcept::error_string(&format!("rs_aiur_execute_env_prove: {e}"))
    },
  }
}

/// `Aiur.AiurSystem.executeShardsProveWithEnv`: cluster-shard
/// measure/prove (see [`execute_shards`]). String params (ABI-simple):
/// `workers` ("0" = default width), `manifest_path`, `shard_sel` — a
/// decimal index or "" for all shards; `dry_run` — "1" measures only.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_execute_shards_prove_with_env(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  block_fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  workers: LeanString<LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  shard_sel: LeanString<LeanBorrowed<'_>>,
  dry_run: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let system = aiur_system_obj.get();
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let block_fun_idx =
    crate::aiur::lean_unbox_nat_as_usize(block_fun_idx.inner());
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let manifest_path = manifest_path.to_string();
  let shard_sel = {
    let s = shard_sel.to_string();
    if s.is_empty() { None } else { s.parse::<usize>().ok() }
  };
  let dry_run = dry_run.to_string() != "0";
  match execute_shards(
    system.toplevel(),
    fun_idx,
    block_fun_idx,
    &env_handle.get().env,
    workers,
    &manifest_path,
    shard_sel,
    dry_run,
    Some(system),
  ) {
    Ok(report) => {
      eprintln!("[rs_shards]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => {
      LeanExcept::error_string(&format!("rs_aiur_execute_shards_prove: {e}"))
    },
  }
}
