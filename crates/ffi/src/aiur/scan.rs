//! Scan-and-cut sharding: shard boundaries from Aiur's own measured cost.
//!
//! Instead of predicting shard cost from profile counters, the env's check
//! schedule is EXECUTED through the codegen'd circuit kernel, and a shard
//! boundary is cut where the analytic peak-prove-RSS prediction computed
//! from the running record's circuit shapes
//! ([`AiurSystem::peak_prove_bytes`]) reaches the margined RAM budget.
//! Execution is the mandatory prefix of proving, so the measurement is the
//! prove's own cost, not a proxy — the failure mode where a recorder-side
//! counter under-represents circuit work by a content-dependent factor
//! cannot occur.
//!
//! The measurement unit is the SAME claim the prover pays for: a
//! thin-frontier `CheckEnv`, one per BATCH of schedule blocks. Each
//! segment grows batch by batch — execute the batch's claim against a
//! shared `QueryRecord`, checkpoint (fft, record bytes), continue while
//! under the cut — so every constant is checked once per segment and
//! dependencies stop at the assumed frontier. (Per-constant
//! `Check{assumptions: None}` claims are NOT usable here: without a
//! frontier the kernel checks the constant's whole dependency closure,
//! which measures 100-1000× the real per-block shard cost and rederives
//! the env spine per segment.) The shared record over-counts slightly —
//! each claim walks its own owned/assumption trees, and members assumed
//! by one claim may be checked by the next — but batching divides that
//! per-claim overhead by the batch size and removes intra-batch frontier
//! edges entirely, so the checkpoint is a tight upper bound on the
//! emitted shard's cold cost: the safe direction for packing, accurate
//! enough to BE the manifest cost without a blanket re-price.
//!
//! Witness bytes are served LAZILY (`EnvFaultSource`): only the claim
//! wires are seeded per attempt, and constant/hint/blob bytes materialize
//! on first fault, so a worker's buffer holds one segment's touched set —
//! exactly the real shard-prove start state.
//!
//! Parallelism follows SP1's splicing design: the schedule is pre-cut into
//! coarse chunks whose edges are FORCED shard boundaries, and chunks scan
//! concurrently. A segment's start state is a cold memo table — exactly
//! the state a real shard prove begins in — so chunk-parallel scanning is
//! faithful by construction. A post-pass merges adjacent segments whose
//! FFT sum stays under the cut (the sum over-estimates the merged cost, so
//! the merged shard still fits), which decouples the chunk count — a pure
//! parallelism knob — from pack density. The schedule itself is the
//! byte-weighted min-cut linearization of the env's reference graph
//! (static, no profiling run), which keeps closure-overlapping blocks
//! adjacent so intra-segment memoization absorbs shared-dependency work.
//!
//! What crosses a boundary: nothing. Constants are order-independent
//! obligations; cross-shard soundness is the thin-frontier assumption tree
//! the claim layer already provides.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use rustc_hash::FxHashMap;

use aiur::{
  bytecode::Toplevel,
  execute::{
    IOBuffer, QueryRecord, dump_query_stats, f64_from_usize,
    query_stats_enabled, record_fft_cost, record_heap_bytes,
  },
  synthesis::AiurSystem,
};
use ix_common::address::Address;
use ix_kernel::profile::{OpCounts, ProfileBuilder};
use ix_kernel::shard::{
  ShardCost, ShardInfo, ShardManifest, aiur_prove_secs_for_fft,
  balanced_agg_tree, cost_fft, cut_coherent_order,
};
use ixon::constant::ConstantInfo as IxonCI;
use ixon::env::Env as IxonEnv;
use ixvm_codegen::aiur_ixvm_runner::execute_ixvm_with_record;
use ixvm_codegen::aiur_ixvm_witness::{
  EnvFaultSource, seed_shard_check_env_claim,
};

/// Bytes per GiB.
const GIB: f64 = 1_073_741_824.0;

/// Current process resident set in GiB (`/proc/self/status` VmRSS);
/// 0 where unreadable (non-Linux). Reported in segment logs.
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
  // Pass 1: home address per constant.
  let mut home: FxHashMap<Address, Address> = FxHashMap::default();
  for entry in env.consts.iter() {
    let (addr, lazy) = (entry.key(), entry.value());
    let Ok(c) = lazy.get() else { continue };
    let h = match &c.info {
      IxonCI::IPrj(p) => p.block.clone(),
      IxonCI::CPrj(p) => p.block.clone(),
      IxonCI::RPrj(p) => p.block.clone(),
      IxonCI::DPrj(p) => p.block.clone(),
      _ => addr.clone(),
    };
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

/// The byte-weighted min-cut linearization of the block graph. Weights ride
/// the `intern` counter slot (the only op counter in the step-cost formula
/// that we can set to a pure byte value), nets are the ref edges; the
/// bisection keeps closure-overlapping blocks adjacent.
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
  cut_coherent_order(&profile, pieces, 0.05)
}

/// One scanned segment: its blocks (as schedule ids) and BOTH measured
/// resource terms — FFT cost (prove compute/trace) and retained record
/// bytes (the execute-side store the prove replays into). Record bytes
/// are not derivable from FFT cost: measured GiB-per-BFFT varies ~2x
/// across segments (heavy single blocks run byte-lean, block-dense
/// segments byte-rich), so a RAM budget must price the pair.
struct Segment {
  blocks: Vec<u32>,
  fft: f64,
  ram_gib: f64,
}

/// Everything a chunk scanner needs besides its own chunk: kernel, env,
/// schedule, and the cut threshold.
struct ScanCtx<'a> {
  toplevel: &'a Toplevel,
  fun_idx: usize,
  env: &'a Arc<IxonEnv>,
  blocks: &'a [SchedBlock],
  /// Combined-resource cut: a segment ends when
  /// `RAM_GIB_PER_BFFT·fft + record_bytes` reaches this headroom
  /// (the budget's usable GiB above the prove base, ε-discounted).
  cut_used_gib: f64,
  n_chunks: usize,
  /// Abort the whole scan on the first kernel-rejected block (the
  /// default). With `--no-fail-fast`, such blocks are recorded in
  /// `failed` and skipped; the manifest then does not cover them, which
  /// the downstream coverage gate reports — a partial partition can
  /// never pass as a full-env check.
  fail_fast: bool,
  /// Blocks whose check claim the kernel rejected, with the error.
  failed: &'a Mutex<Vec<(Address, String)>>,
  /// Set on a fatal error so every worker bails at its next BLOCK
  /// boundary — a failure aborts the fleet in seconds, not after the
  /// in-flight ranges drain.
  abort: &'a std::sync::atomic::AtomicBool,
  /// Blocks per measurement claim. Batching divides the claim layer's
  /// per-claim overhead (assumption-tree hashing, unshared `env_walk`
  /// frames) by K and shrinks frontiers (intra-batch edges stop being
  /// frontier members), keeping the running readout tight enough to
  /// serve as the shard cost without a blanket re-price.
  batch_blocks: usize,
  /// The compiled system, feeding the analytic peak-prove-RAM model that
  /// the scan's cut charges (`Some` for the scanner); `None` in
  /// execute-only mode, where the cut is the record's retained bytes
  /// against the per-worker share.
  system: Option<&'a AiurSystem>,
  /// Execute-only phase 1: defer a range's remainder to the fat phase
  /// when measured record growth per block exceeds this (bytes).
  /// `None` disables (the scan, and the fat phase itself).
  defer_growth: Option<f64>,
  /// Graceful record ceiling, GiB: a segment also cuts when its record's
  /// retained bytes reach this, independent of the model cut. In
  /// cgroup-capped worker processes it sits below the enforced cap
  /// (~80%), so legitimately record-heavy segments end at a claim
  /// boundary instead of being OOM-killed — the kill is reserved for
  /// MID-claim growth, which no boundary check can see. `f64::INFINITY`
  /// disables it (thread-pool mode).
  soft_record_gib: f64,
}

/// Default blocks per measurement claim; `IX_SCAN_BATCH_BLOCKS`
/// overrides (1 restores per-block claims). Fixed — never adaptive — so
/// the partition stays independent of scheduling. The claim is also the
/// granularity of the record-threshold check, so its worst-case record
/// growth must fit inside [`CLAIM_HEADROOM_GIB`]: dense FLT content
/// measured ~4 GiB of growth per 128-block claim, scaling roughly with
/// K. K=32 bounds that to ~1 GiB at a conservative measurement drift
/// between the measured +3.7% (K=64) and +11.6% (K=16) — drift only
/// overstates costs, tightening the plan, never breaking it.
const SCAN_BATCH_BLOCKS: usize = 32;

/// Target blocks per work-queue chunk. Chunks are the unit of stealing:
/// once fewer chunks remain than workers, the excess workers idle — the
/// serial tail is bounded by the largest chunk, so chunks must be much
/// finer than the worker count (workers×2 on FLT left 16 of 18 workers
/// idle for the last third of the scan). Chunk edges are forced segment
/// boundaries; the merge pass absorbs the extra fragmentation.
const CHUNK_TARGET_BLOCKS: usize = 2048;

/// A worker's non-record residency: env mmap, compiled AiurSystem,
/// runtime (fresh workers measured ~1.2-1.8 GiB on FLT), PLUS working
/// room for the env decode cache, which grows monotonically with
/// content touched (death is its shedding mechanism — but it must not
/// be the routine one, so the slot budgets a few GiB of cache first).
const WORKER_BASELINE_GIB: f64 = 3.5;

/// Target record growth per claim, GiB. Claim width K derives from it
/// (see [`scan_range`]): K = target / measured-growth-per-block, clamped
/// to `[1, SCAN_BATCH_BLOCKS]`. Per-claim overhead (assumption-tree
/// hashing, unshared `env_walk` frames) is roughly constant per claim,
/// so it is negligible against a claim carrying this much work — light
/// content runs at full width where the overhead would bite, dense
/// content shrinks to K=1-2 where each block dwarfs it. Bounding growth
/// per claim is what lets the between-claims threshold check act before
/// the cgroup kill on ANY content.
const CLAIM_TARGET_GIB: f64 = 0.75;

/// Worst mid-claim record growth past the threshold check: with claim
/// width derived from [`CLAIM_TARGET_GIB`], overshoot beyond the target
/// is one block's excess over its range's running estimate — bounded in
/// practice by the single-block record distribution's body; the tail
/// (true monster blocks) is the deferred cleanup's job, not headroom's.
const CLAIM_HEADROOM_GIB: f64 = 1.0;

/// Smallest useful per-worker slice: the soft record cut (the segment
/// measurement quantum, ~11.5 GiB at this floor — segments are summed
/// to the cut by the merge pass, so they never need to reach it alone)
/// plus the cache-inclusive worker baseline and one claim's headroom.
/// Bounds the auto worker count (`pool / floor`). Measured across the
/// FLT sweep: 8 GiB slots (60 workers) and 12 GiB slots (33 workers)
/// both ground down in the dense head — cache + a useful record quantum
/// simply need this much — while ~17-18 GiB slots ran it best; thinner
/// buys width the dense content immediately claws back in deaths.
const SLICE_FLOOR_GIB: f64 = 16.0;

/// Width of the deferred-block cleanup round: blocks whose own claim
/// died under a slot cap re-run after the fleet drains, each worker
/// capped at the freed pool split this many ways (~65-70 GiB on the
/// deliverable boxes). Sized from the monster-record distribution:
/// every escalated block ever measured except two fit under ~70 GiB,
/// so a wider round would trade slots that fit the population for
/// parallelism the survivors cannot use.
const CLEANUP_WORKERS: usize = 12;

/// Execute-only phase-1 deferral threshold: record growth per block
/// (bytes) above which a range's remainder is handed to the fat-slot
/// phase instead of walked thin. The measured distribution is bimodal
/// with a decade-wide gap (light content ~1-20 MB/block, dense
/// typeclass-web content ~300 MB-4 GiB/block), so any threshold in the
/// gap classifies robustly, and both error directions are cheap: an
/// over-deferred range walks warm in phase 2; an under-deferred one
/// triggers on its next claim. Growth is measured, not predicted —
/// record growth IS the reduction work just performed.
const DEFER_GROWTH_BYTES_PER_BLOCK: f64 = 1.0e8;

/// Merge-pass packing target as a multiple of the cut. Summed segment
/// costs overstate a merged shard's true cold cost (shared cones count
/// once per segment; padded heights are subadditive) — measured
/// true/summed = 0.606-0.623 on the three heaviest 500-budget shards —
/// so packing to the cut on sums leaves ~40% of the budget unused. The
/// merge packs past the cut by this factor and the cold RE-PRICE round
/// then measures every shard's true cost (one CheckEnv execution per
/// shard, the exact claim its prove runs); the deliberate gap below the
/// measured 1.6x slack keeps over-cut re-prices (which force a split)
/// rare.
const PACK_OVERSHOOT: f64 = 1.45;

/// Re-price round width: one cold execution per merged shard, each
/// holding only the shard's RECORD (~true prove RSS / 20), so slots are
/// pool/width ≈ 30-40 GiB — enough for every shard record plus a dense
/// opening cone.
const REPRICE_WORKERS: usize = 12;

/// Ranges a child serves before the parent proactively reaps and
/// respawns it. The env decode cache grows monotonically with content
/// touched — measured ~2-4 GiB per DENSE range — so recycling bounds
/// every child's cache to about one range's growth: slot headroom
/// belongs to the RECORD at every point in the schedule, dense strips
/// walk inline at fleet width, and mid-strip deaths (whose resume
/// points cannot re-open under a slot and would push whole strip
/// remainders into the narrow cleanup round) stay rare. Spawn cost is
/// seconds (order file + env mmap) against tens of seconds per range.
const WORKER_RECYCLE_RANGES: usize = 2;

/// Subtracted from box RAM (with the measured parent baseline) before
/// slicing the pool: kernel, page cache churn, and everything else on
/// the box that is not this scan.
const OS_RESERVE_GIB: f64 = 12.0;

/// Fraction of the derived pool actually sliced into worker caps. The
/// caps are a worst-case bound and dense regions reach it: on FLT's
/// head every worker sits near its cap simultaneously, so `Σ caps =
/// pool` runs the box to zero free (measured: 490/495 GB used, page
/// cache evicted to zero). The unsliced remainder is the fleet's slack —
/// all workers brushing their caps at once still leave it free.
const POOL_SLICE_FRAC: f64 = 0.85;

/// Worker counts shrink until every child's even slice of the pool
/// clears the slice floor; thread mode passes through.
fn bound_workers_by_pool(workers: usize, pool_gib: f64, proc: bool) -> usize {
  if !proc {
    return workers;
  }
  let by_floor: usize = format!("{:.0}", (pool_gib / SLICE_FLOOR_GIB).floor())
    .parse()
    .unwrap_or(1);
  workers.min(by_floor.max(1)).max(1)
}

/// The min-cut schedule order, windowed by the `IX_SCAN_SKIP_BLOCKS` /
/// `IX_SCAN_LIMIT_BLOCKS` debug knobs (a full-pipeline reproducer over a
/// slice of a huge env, without extracting one; the result then does NOT
/// cover the env). Skip drops the order's head, limit truncates what
/// remains — composed, they select any window; skip alone replays the
/// schedule's TAIL, where min-cut ordering concentrates the dense
/// content that dominates scan wall.
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

/// Blocks per chunk past which an edge is forced regardless of bytes.
/// Chunks are byte-balanced, but cost per byte is wildly non-uniform:
/// FLT's dense proof blocks are small in bytes and huge in cost, so
/// byte-only balancing packed up to ~3,100 of them into one chunk —
/// ~10 sequential cut-sized segments for a single owner, the measured
/// serial tail of the scan. The count clamp splits exactly those
/// chunks; the merge pass absorbs the extra forced boundaries.
const CHUNK_MAX_BLOCKS: usize = 512;

/// Equal-byte contiguous chunks over the order, block-count clamped
/// (see [`CHUNK_MAX_BLOCKS`]); edges are forced segment boundaries (the
/// parallelism unit); the scan's merge pass repairs the resulting
/// fragmentation, so chunk granularity is a pure parallelism knob.
fn make_chunk_bounds(
  order: &[u32],
  blocks: &[SchedBlock],
  env_bytes: u64,
  n_chunks: usize,
) -> Vec<(usize, usize)> {
  let per_chunk = (env_bytes / n_chunks as u64).max(1);
  let mut bounds: Vec<(usize, usize)> = Vec::new();
  let mut start = 0usize;
  let mut acc = 0u64;
  for (i, &b) in order.iter().enumerate() {
    acc += blocks[b as usize].size;
    if acc >= per_chunk || i + 1 - start >= CHUNK_MAX_BLOCKS {
      bounds.push((start, i + 1));
      start = i + 1;
      acc = 0;
    }
  }
  if start < order.len() {
    bounds.push((start, order.len()));
  }
  // Baseline before any execution: the schedule pass decoded every
  // constant into the shared env's lazy cache, so this RSS is (cache +
  // static structures) — the floor the worker footprints sit on.
  eprintln!("[scan] post-schedule baseline rss {:.0}G", process_rss_gib());
  bounds
}

/// Work-stealing worker pool over the chunks: workers pull `(origin
/// chunk, seq, blocks)` ranges off a shared deque; a range yields at
/// most [`RANGE_SEGMENTS`] segments, then re-queues its remainder for
/// any idle worker, so dense regions self-parallelize. The split policy
/// is count-based, not time- or RAM-based, so the resulting segments do
/// not depend on scheduling; they are tagged `(origin, seq)` and sorted
/// at the end, so the returned order is the schedule order.
fn run_pool(
  ctx: &ScanCtx<'_>,
  chunks: Vec<Vec<u32>>,
  workers: usize,
) -> Result<Vec<Segment>, String> {
  type Range = (u32, u32, Vec<u32>);
  let queue: Mutex<std::collections::VecDeque<Range>> = Mutex::new(
    chunks
      .into_iter()
      .enumerate()
      .map(|(i, c)| (u32::try_from(i).expect("chunk count fits u32"), 0u32, c))
      .collect(),
  );
  let in_flight = AtomicUsize::new(0);
  let done: Mutex<Vec<((u32, u32), Vec<Segment>)>> = Mutex::new(Vec::new());
  let failure: Mutex<Option<String>> = Mutex::new(None);
  std::thread::scope(|s| {
    for _ in 0..workers {
      s.spawn(|| {
        loop {
          if failure.lock().unwrap().is_some() {
            break;
          }
          // Pop and the in-flight increment are ATOMIC under the queue
          // lock: a worker that sees the queue empty is then guaranteed a
          // consistent in-flight read — the last popper has already
          // registered. (Split, the window between pop and increment let
          // idle workers read `empty && in_flight == 0` and exit while
          // work remained; the fleet silently drained.)
          let next = {
            let mut q = queue.lock().unwrap();
            let popped = q.pop_front();
            if popped.is_some() {
              in_flight.fetch_add(1, Ordering::AcqRel);
            }
            popped
          };
          let Some((origin, seq, range)) = next else {
            // Empty queue but ranges in flight may still re-queue
            // remainders; only quit when nothing can produce more work.
            if in_flight.load(Ordering::Acquire) == 0 {
              break;
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
            continue;
          };
          match scan_range(ctx, &range, origin) {
            Ok((segs, rest, _defer)) => {
              done.lock().unwrap().push(((origin, seq), segs));
              // Remainder goes back BEFORE the in-flight decrement, so
              // `empty && in_flight == 0` still implies no future work.
              if !rest.is_empty() {
                queue.lock().unwrap().push_back((origin, seq + 1, rest));
              }
            },
            Err(e) => {
              ctx.abort.store(true, Ordering::Release);
              let mut f = failure.lock().unwrap();
              if f.is_none() {
                *f = Some(e);
              }
            },
          }
          in_flight.fetch_sub(1, Ordering::AcqRel);
        }
      });
    }
  });
  if let Some(e) = failure.into_inner().unwrap() {
    return Err(e);
  }
  let mut tagged = done.into_inner().unwrap();
  tagged.sort_by_key(|(k, _)| *k);
  let mut segments: Vec<Segment> = Vec::new();
  for (_, mut segs) in tagged {
    segments.append(&mut segs);
  }
  Ok(segments)
}

/// The scan worker's stdin/stdout loop: a child process spawned by the
/// process pool, deterministically re-deriving the same schedule as its
/// parent and executing order-index ranges on command. Line protocol
/// (one command per stdin line, replies on stdout):
///
/// - `SCAN <lo> <hi> [narrow]` — scan `order[lo..hi)` exactly like a
///   thread worker's range: up to [`RANGE_SEGMENTS`] segments, then hand
///   the remainder back. The optional `narrow` count single-steps the
///   range's first N blocks (one per claim) — sent by the parent when a
///   range resumes after a death so a dense stretch banks per-block
///   progress instead of re-dying at full claim width. Replies:
///   `SEG <lo> <hi> <fft> <ram_gib>` per emitted segment (absolute order
///   indices), `SKIP <addr-hex> <msg-hex>` per kernel-rejected block,
///   then `END <next>` (`next == hi` when the range is exhausted). A
///   unit range (`hi == lo+1`) degenerates to a single-block claim —
///   the deferred-block cleanup round measures blocks this way, no
///   dedicated verb needed.
///
/// The worker never applies fail-fast itself — it reports SKIPs and the
/// parent enforces policy. RAM: the enclosing cgroup's `memory.max` is
/// the hard cap (an over-cap worker is OOM-killed and the parent
/// recovers); `soft_record_gib` cuts segments gracefully below it so
/// only MID-claim growth ever reaches the kill.
pub fn scan_worker(
  system: &AiurSystem,
  fun_idx: usize,
  env: &Arc<IxonEnv>,
  cut_used_gib: f64,
  batch_blocks: usize,
  soft_record_gib: f64,
  pieces: usize,
  exec_only: bool,
  defer_growth: bool,
) -> Result<(), String> {
  use std::io::{BufRead, Write};
  let toplevel = system.toplevel();
  // The parent already derived the schedule; children read it from the
  // order file instead of re-deriving (30 children re-running the
  // min-cut bisection concurrently was minutes of pure startup on
  // FLT-scale envs). Fallback to self-derivation keeps the worker
  // usable standalone.
  let (blocks, order) = match std::env::var("IX_SCAN_ORDER_FILE") {
    Ok(path) => read_order_file(&path)?,
    Err(_) => {
      let (blocks, adj) = schedule_blocks(env);
      let order = ordered_schedule(&blocks, &adj, pieces);
      (blocks, order)
    },
  };
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let abort = std::sync::atomic::AtomicBool::new(false);
  // Shard member lists for `PRICE`, loaded lazily on first use — most
  // children never price.
  let mut price_table: Option<Vec<Vec<u32>>> = None;
  let ctx = ScanCtx {
    toplevel,
    fun_idx,
    env,
    blocks: &blocks,
    cut_used_gib,
    n_chunks: pieces,
    fail_fast: false,
    failed: &failed,
    abort: &abort,
    batch_blocks,
    system: if exec_only { None } else { Some(system) },
    defer_growth: defer_growth.then_some(DEFER_GROWTH_BYTES_PER_BLOCK),
    soft_record_gib,
  };
  let stdout = std::io::stdout();
  let mut out = stdout.lock();
  writeln!(out, "READY {}", order.len()).map_err(|e| e.to_string())?;
  out.flush().map_err(|e| e.to_string())?;
  let stdin = std::io::stdin();
  for line in stdin.lock().lines() {
    let line = line.map_err(|e| e.to_string())?;
    let mut it = line.split_whitespace();
    let (verb, lo, hi) = (
      it.next().unwrap_or(""),
      it.next().and_then(|v| v.parse::<usize>().ok()),
      it.next().and_then(|v| v.parse::<usize>().ok()),
    );
    // A third field (a since-removed narrow-prefix hint) is accepted
    // and ignored for wire compatibility with parents of that vintage.
    let _ = it.next();
    if verb == "PRICE" {
      // Cold re-price of one merged shard: execute its whole CheckEnv
      // claim (the exact claim its prove runs) with a fresh record and
      // report the record's measured fft plus the analytic peak prove
      // RSS. `lo` is the shard index in the price file.
      let Some(k) = lo else {
        return Err(format!("worker: malformed command {line:?}"));
      };
      if price_table.is_none() {
        let path = std::env::var("IX_SCAN_PRICE_FILE")
          .map_err(|_e| "worker: PRICE without IX_SCAN_PRICE_FILE")?;
        price_table = Some(read_price_file(&path)?);
      }
      let table = price_table.as_ref().unwrap();
      let members = table
        .get(k)
        .ok_or_else(|| format!("worker: PRICE {k} out of range"))?;
      let addrs: Vec<Address> = members
        .iter()
        .map(|&b| blocks[b as usize].addr.clone())
        .collect();
      let mut record = QueryRecord::new(toplevel);
      let mut io =
        IOBuffer::with_backing(EnvFaultSource::new(env.clone()));
      let priced = seed_shard_check_env_claim(env, &addrs, &mut io).and_then(
        |(_claim, input)| {
          execute_ixvm_with_record(toplevel, fun_idx, &input, &mut io, &mut record)
            .map(|_| ())
            .map_err(|e| e.to_string())
        },
      );
      match priced {
        Ok(()) => {
          let fft = record_fft_cost(toplevel, &record);
          let ram = match ctx.system {
            Some(sys) => {
              f64_from_usize(sys.peak_prove_bytes(&record).peak) / GIB
            },
            None => f64_from_usize(record_heap_bytes(&record)) / GIB,
          };
          writeln!(out, "COST {fft} {ram}").map_err(|e| e.to_string())?;
        },
        Err(e) => {
          writeln!(out, "PERR {}", hex_encode(e.as_bytes()))
            .map_err(|e| e.to_string())?;
        },
      }
      out.flush().map_err(|e| e.to_string())?;
      continue;
    }
    let (Some(lo), Some(hi)) = (lo, hi) else {
      return Err(format!("worker: malformed command {line:?}"));
    };
    if hi > order.len() || lo >= hi {
      return Err(format!("worker: range {lo}..{hi} out of bounds"));
    }
    match verb {
      "SCAN" => {
        let range = &order[lo..hi];
        let (segs, rest, deferred) =
          scan_range(&ctx, range, u32::try_from(lo).unwrap_or(0))?;
        // Segments consume the range in order; skipped blocks sit in the
        // gaps. Recover absolute bounds by cursor-matching first ids.
        let mut cursor = lo;
        for s in &segs {
          while order[cursor] != s.blocks[0] {
            cursor += 1; // a skipped block
          }
          let end = cursor + s.blocks.len();
          writeln!(out, "SEG {cursor} {end} {} {}", s.fft, s.ram_gib)
            .map_err(|e| e.to_string())?;
          cursor = end;
        }
        for (a, e) in failed.lock().unwrap().drain(..) {
          writeln!(out, "SKIP {} {}", a.hex(), hex_encode(e.as_bytes()))
            .map_err(|e| e.to_string())?;
        }
        let verb = if deferred { "DEFER" } else { "END" };
        writeln!(out, "{verb} {}", hi - rest.len())
          .map_err(|e| e.to_string())?;
      },
      _ => return Err(format!("worker: unknown verb {verb:?}")),
    }
    out.flush().map_err(|e| e.to_string())?;
  }
  Ok(())
}

/// Serialize the derived schedule for worker children: block addresses
/// (in block-id order) and the min-cut order. Members and sizes are
/// parent-side concerns (chunking, manifest assembly) — a worker needs
/// only `id → addr` for claims and the order for range indexing.
fn write_order_file(
  path: &std::path::Path,
  blocks: &[SchedBlock],
  order: &[u32],
) -> Result<(), String> {
  let mut buf: Vec<u8> =
    Vec::with_capacity(16 + blocks.len() * 32 + order.len() * 4);
  buf.extend_from_slice(&(blocks.len() as u64).to_le_bytes());
  for b in blocks {
    buf.extend_from_slice(b.addr.as_bytes());
  }
  buf.extend_from_slice(&(order.len() as u64).to_le_bytes());
  for &o in order {
    buf.extend_from_slice(&o.to_le_bytes());
  }
  std::fs::write(path, buf).map_err(|e| format!("write {path:?}: {e}"))
}

fn read_order_file(path: &str) -> Result<(Vec<SchedBlock>, Vec<u32>), String> {
  let buf =
    std::fs::read(path).map_err(|e| format!("read order file {path}: {e}"))?;
  let take_u64 = |buf: &[u8], pos: usize| -> Result<u64, String> {
    buf
      .get(pos..pos + 8)
      .and_then(|b| b.try_into().ok())
      .map(u64::from_le_bytes)
      .ok_or_else(|| format!("order file {path}: truncated"))
  };
  let nblocks = usize::try_from(take_u64(&buf, 0)?)
    .map_err(|_e| "order file: block count overflow".to_string())?;
  let mut pos = 8;
  let mut blocks = Vec::with_capacity(nblocks);
  for _ in 0..nblocks {
    let addr = buf
      .get(pos..pos + 32)
      .and_then(|b| Address::from_slice(b).ok())
      .ok_or_else(|| format!("order file {path}: truncated address"))?;
    blocks.push(SchedBlock { addr, members: Vec::new(), size: 0 });
    pos += 32;
  }
  let norder = usize::try_from(take_u64(&buf, pos)?)
    .map_err(|_e| "order file: order count overflow".to_string())?;
  pos += 8;
  let mut order = Vec::with_capacity(norder);
  for _ in 0..norder {
    let v = buf
      .get(pos..pos + 4)
      .and_then(|b| b.try_into().ok())
      .map(u32::from_le_bytes)
      .ok_or_else(|| format!("order file {path}: truncated order"))?;
    order.push(v);
    pos += 4;
  }
  Ok((blocks, order))
}

/// Serialize merged shards' member block ids for the re-price workers:
/// `[u64 shard count][per shard: u64 len, u32 ids…]`. Members are block
/// ids into the order file's block table, so a worker prices exactly
/// the claim the manifest will carry (holes from skipped blocks
/// included).
fn write_price_file(
  path: &std::path::Path,
  shards: &[Vec<u32>],
) -> Result<(), String> {
  let total: usize = shards.iter().map(Vec::len).sum();
  let mut buf: Vec<u8> = Vec::with_capacity(8 + shards.len() * 8 + total * 4);
  buf.extend_from_slice(&(shards.len() as u64).to_le_bytes());
  for m in shards {
    buf.extend_from_slice(&(m.len() as u64).to_le_bytes());
    for &b in m {
      buf.extend_from_slice(&b.to_le_bytes());
    }
  }
  std::fs::write(path, buf).map_err(|e| format!("write {path:?}: {e}"))
}

fn read_price_file(path: &str) -> Result<Vec<Vec<u32>>, String> {
  let buf =
    std::fs::read(path).map_err(|e| format!("read price file {path}: {e}"))?;
  let take_u64 = |pos: usize| -> Result<u64, String> {
    buf
      .get(pos..pos + 8)
      .and_then(|b| b.try_into().ok())
      .map(u64::from_le_bytes)
      .ok_or_else(|| format!("price file {path}: truncated"))
  };
  let count = usize::try_from(take_u64(0)?)
    .map_err(|_e| "price file: count overflow".to_string())?;
  let mut pos = 8;
  let mut shards = Vec::with_capacity(count);
  for _ in 0..count {
    let len = usize::try_from(take_u64(pos)?)
      .map_err(|_e| "price file: len overflow".to_string())?;
    pos += 8;
    let mut members = Vec::with_capacity(len);
    for _ in 0..len {
      let v = buf
        .get(pos..pos + 4)
        .and_then(|b| b.try_into().ok())
        .map(u32::from_le_bytes)
        .ok_or_else(|| format!("price file {path}: truncated member"))?;
      members.push(v);
      pos += 4;
    }
    shards.push(members);
  }
  Ok(shards)
}

fn hex_encode(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode(s: &str) -> Option<Vec<u8>> {
  if !s.len().is_multiple_of(2) {
    return None;
  }
  (0..s.len() / 2)
    .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok())
    .collect()
}

/// Whether `systemd-run --user --scope` is available to enforce
/// per-worker memory caps (the kernel migration a session-scoped process
/// cannot do itself, done by the user manager over D-Bus). Probed once
/// per pool; without it workers run uncapped with a loud warning.
fn systemd_scope_caps_available() -> bool {
  std::process::Command::new("systemd-run")
    .args(["--user", "--scope", "--quiet", "--", "true"])
    .status()
    .map(|st| st.success())
    .unwrap_or(false)
}

/// Everything the process pool needs to spawn and command workers.
struct ProcPool<'a> {
  bin: String,
  ixe: String,
  cut_used_gib: f64,
  batch_blocks: usize,
  soft_record_gib: f64,
  pieces: usize,
  exec_only: bool,
  cap_bytes: u64,
  /// Per-worker cap of the deferred-block cleanup round (the drained
  /// pool split [`CLEANUP_WORKERS`] ways): after the fleet finishes,
  /// blocks that could not run under a slot cap re-run through the same
  /// pool code under these fat caps; survivors are named
  /// resource-infeasible.
  cleanup_cap_bytes: u64,
  /// True in the cleanup round itself — a block failing there is named
  /// infeasible instead of deferred again.
  cleanup: bool,
  /// The parent-derived schedule serialized for children (deleted when
  /// the pool drops) — spawn startup is env-mmap + system build, not a
  /// re-derivation.
  order_file: std::path::PathBuf,
  /// Caps are enforced via `systemd-run --user --scope -p MemoryMax=`;
  /// false means the probe failed and workers run UNCAPPED.
  capped: bool,
  order: &'a [u32],
  blocks: &'a [SchedBlock],
  fail_fast: bool,
  /// Name deferred ranges resource-infeasible instead of walking them
  /// in the cleanup round (`ix shard --defer-infeasible`).
  defer_infeasible: bool,
  /// Execute-only phase 1: children measure growth and hand dense
  /// remainders back (`DEFER`) for the fat phase.
  defer_growth: bool,
  /// Shard member lists for the re-price round (`PRICE` verb); exported
  /// to children via `IX_SCAN_PRICE_FILE`.
  price_file: Option<std::path::PathBuf>,
}

struct WorkerHandle {
  child: std::process::Child,
  stdin: std::process::ChildStdin,
  stdout: std::io::BufReader<std::process::ChildStdout>,
}

/// One `SCAN` round-trip's outcome.
struct ScanReply {
  segs: Vec<Segment>,
  skips: Vec<(Address, String)>,
  next: usize,
  /// The worker stopped at `next` because measured growth crossed the
  /// phase-1 threshold — the remainder belongs to the fat phase.
  deferred: bool,
}

impl Drop for ProcPool<'_> {
  fn drop(&mut self) {
    let _ = std::fs::remove_file(&self.order_file);
  }
}

impl ProcPool<'_> {
  /// Spawn with one retry: a fresh worker that dies before its READY
  /// handshake is a transient environment hiccup (systemd/D-Bus under
  /// respawn churn measured one EOF in ~100 respawns), not a scan
  /// failure — but an unhandled one aborts the whole scan. One backoff
  /// retry covers it; a second failure is real and propagates.
  fn spawn(&self, slot: usize) -> Result<WorkerHandle, String> {
    self.spawn_once(slot).or_else(|e| {
      eprintln!("[scan] worker {slot} spawn failed ({e}); retrying once");
      std::thread::sleep(std::time::Duration::from_secs(2));
      self.spawn_once(slot)
    })
  }

  fn spawn_once(&self, slot: usize) -> Result<WorkerHandle, String> {
    use std::process::{Command, Stdio};
    let cap_bytes = self.cap_bytes;
    let mut cmd = if self.capped {
      let mut c = Command::new("systemd-run");
      c.args([
        "--user",
        "--scope",
        "--quiet",
        "-p",
        &format!("MemoryMax={cap_bytes}"),
        "-p",
        "MemorySwapMax=0",
        "--",
        &self.bin,
      ]);
      c
    } else {
      Command::new(&self.bin)
    };
    cmd
      .arg("shard-worker")
      .env("IX_SCAN_ORDER_FILE", &self.order_file);
    if let Some(pf) = &self.price_file {
      cmd.env("IX_SCAN_PRICE_FILE", pf);
    }
    cmd
      // Return freed pages to the OS immediately: the record drops at
      // every segment cut, but mimalloc retains the pages by default, so
      // worker RSS ratchets to its per-segment peak and the fleet sits
      // at Σ caps regardless of live bytes.
      .env("MIMALLOC_PURGE_DELAY", "0")
      .args(["--ixe", &self.ixe])
      .args(["--cut-gib", &format!("{}", self.cut_used_gib)])
      .args(["--batch", &format!("{}", self.batch_blocks)])
      .args(["--soft-cap-gib", &format!("{}", self.soft_record_gib)])
      .args(["--pieces", &format!("{}", self.pieces)])
      .stdin(Stdio::piped())
      .stdout(Stdio::piped());
    if self.exec_only {
      cmd.arg("--exec-only");
    }
    if self.defer_growth {
      cmd.arg("--defer-growth");
    }
    let mut child = cmd
      .spawn()
      .map_err(|e| format!("spawn worker {slot} ({}): {e}", self.bin))?;
    let stdin = child.stdin.take().expect("piped stdin");
    let stdout =
      std::io::BufReader::new(child.stdout.take().expect("piped stdout"));
    let mut h = WorkerHandle { child, stdin, stdout };
    // Verify the child derived the same schedule before trusting indices.
    let ready = h.read_line()?;
    let n: usize = ready
      .strip_prefix("READY ")
      .and_then(|v| v.trim().parse().ok())
      .ok_or_else(|| format!("worker {slot}: bad handshake {ready:?}"))?;
    if n != self.order.len() {
      return Err(format!(
        "worker {slot}: schedule mismatch ({n} blocks vs {})",
        self.order.len()
      ));
    }
    Ok(h)
  }

  /// Send one `SCAN` and collect its replies. `Err(committed)` = the
  /// worker died mid-range; `committed` carries whatever segments and
  /// skips arrived before death plus the index scanning had reached.
  fn scan(
    &self,
    h: &mut WorkerHandle,
    lo: usize,
    hi: usize,
  ) -> Result<ScanReply, ScanReply> {
    use std::io::Write;
    let mut reply = ScanReply {
      segs: Vec::new(),
      skips: Vec::new(),
      next: lo,
      deferred: false,
    };
    if writeln!(h.stdin, "SCAN {lo} {hi}").is_err() || h.stdin.flush().is_err()
    {
      return Err(reply);
    }
    loop {
      let line = match h.read_line() {
        Ok(l) => l,
        Err(_) => return Err(reply),
      };
      let mut it = line.split_whitespace();
      match it.next() {
        Some("SEG") => {
          let (Some(s), Some(e), Some(fft), Some(ram)) = (
            it.next().and_then(|v| v.parse::<usize>().ok()),
            it.next().and_then(|v| v.parse::<usize>().ok()),
            it.next().and_then(|v| v.parse::<f64>().ok()),
            it.next().and_then(|v| v.parse::<f64>().ok()),
          ) else {
            return Err(reply);
          };
          reply.segs.push(Segment {
            blocks: self.order[s..e].to_vec(),
            fft,
            ram_gib: ram,
          });
          reply.next = e;
        },
        Some("SKIP") => {
          let (Some(addr), Some(msg)) = (
            it.next().and_then(Address::from_hex),
            it.next().and_then(hex_decode),
          ) else {
            return Err(reply);
          };
          reply.skips.push((addr, String::from_utf8_lossy(&msg).into_owned()));
        },
        Some("END") => {
          let Some(next) = it.next().and_then(|v| v.parse::<usize>().ok())
          else {
            return Err(reply);
          };
          reply.next = next;
          return Ok(reply);
        },
        Some("DEFER") => {
          let Some(next) = it.next().and_then(|v| v.parse::<usize>().ok())
          else {
            return Err(reply);
          };
          reply.next = next;
          reply.deferred = true;
          return Ok(reply);
        },
        _ => return Err(reply),
      }
    }
  }
}

impl ProcPool<'_> {
  /// One `PRICE` round-trip: the child executes shard `k`'s whole
  /// CheckEnv claim cold and reports `(fft, ram_gib)` from the record —
  /// the exact cost its prove pays. `Err` = the child died (over-cap
  /// shard) or reported a pricing error.
  fn price(
    &self,
    h: &mut WorkerHandle,
    k: usize,
  ) -> Result<(f64, f64), String> {
    use std::io::Write;
    writeln!(h.stdin, "PRICE {k}").map_err(|e| e.to_string())?;
    h.stdin.flush().map_err(|e| e.to_string())?;
    let line = h.read_line()?;
    let mut it = line.split_whitespace();
    match it.next() {
      Some("COST") => {
        let (Some(fft), Some(ram)) = (
          it.next().and_then(|v| v.parse::<f64>().ok()),
          it.next().and_then(|v| v.parse::<f64>().ok()),
        ) else {
          return Err(format!("bad COST reply {line:?}"));
        };
        Ok((fft, ram))
      },
      Some("PERR") => Err(
        it.next()
          .and_then(hex_decode)
          .map_or_else(
            || "pricing error".to_string(),
            |m| String::from_utf8_lossy(&m).into_owned(),
          ),
      ),
      _ => Err(format!("bad PRICE reply {line:?}")),
    }
  }
}

impl WorkerHandle {
  fn read_line(&mut self) -> Result<String, String> {
    use std::io::BufRead;
    let mut line = String::new();
    match self.stdout.read_line(&mut line) {
      Ok(0) => Err("worker EOF".to_string()),
      Ok(_) => Ok(line.trim_end().to_string()),
      Err(e) => Err(e.to_string()),
    }
  }

  fn reap(mut self) -> String {
    let _ = self.child.kill();
    match self.child.wait() {
      Ok(st) => format!("{st}"),
      Err(e) => format!("wait failed: {e}"),
    }
  }
}

/// Process-pool scan: like [`run_pool`], but each worker is a separate
/// `ix shard-worker` process under a cgroup memory cap. A worker's env
/// decode cache grows monotonically with the content it executes (the
/// record drops at segment cuts; the cache never shrinks), so on dense
/// content every worker periodically fills its cap and is OOM-killed —
/// death IS the cache-shedding mechanism, and it is cheap: segments
/// stream as they close, so a kill loses only the work since the last
/// closed segment. The parent respawns and resumes from the committed
/// index with a narrow prefix (the resumed range's first blocks execute
/// one per claim), so a dense stretch banks per-block progress instead
/// of re-dying at full claim width. A block whose own single claim dies
/// under the slot cap is DEFERRED: after the fleet drains, the deferred
/// blocks re-run through this same function under fat caps (the freed
/// pool split [`CLEANUP_WORKERS`] ways); a block that dies even there is
/// named resource-infeasible. The fleet's RAM bound is `Σ caps`,
/// enforced by the kernel, independent of content.
fn run_pool_procs(
  pool: &ProcPool<'_>,
  chunks: Vec<(usize, usize)>,
  workers: usize,
  failed: &Mutex<Vec<(Address, String)>>,
) -> Result<Vec<Segment>, String> {
  // (origin chunk, commit sequence, lo, hi).
  type Range = (u32, u32, usize, usize);
  let total_blocks: usize = chunks.iter().map(|(lo, hi)| hi - lo).sum();
  let start = std::time::Instant::now();
  let queue: Mutex<std::collections::VecDeque<Range>> = Mutex::new(
    chunks
      .into_iter()
      .enumerate()
      .map(|(i, (lo, hi))| {
        (u32::try_from(i).expect("chunk count fits u32"), 0u32, lo, hi)
      })
      .collect(),
  );
  let in_flight = AtomicUsize::new(0);
  let blocks_done = AtomicUsize::new(0);
  let last_pct = AtomicUsize::new(0);
  let done: Mutex<Vec<((u32, u32), Vec<Segment>)>> = Mutex::new(Vec::new());
  let failure: Mutex<Option<String>> = Mutex::new(None);
  let abort = std::sync::atomic::AtomicBool::new(false);
  // (origin, lo, hi) ranges whose opening claim died on a fresh worker —
  // walked cumulatively in the cleanup round after the fleet drains.
  // Deep dense strips are only cheap CUMULATIVELY (a walk shares the
  // strip's dependency cone in one record; any solo measurement pays the
  // whole cone per block), so a range whose resume point cannot even
  // open under a slot moves to the fat round wholesale instead of the
  // fleet paying one doomed cone-derivation per block.
  let deferred: Mutex<Vec<(u32, usize, usize)>> = Mutex::new(Vec::new());
  std::thread::scope(|s| {
    let (queue, in_flight, done, failure, abort) =
      (&queue, &in_flight, &done, &failure, &abort);
    let (blocks_done, last_pct, deferred) = (&blocks_done, &last_pct, &deferred);
    for slot in 0..workers {
      s.spawn(move || {
        // Ranges served by the current child; at [`WORKER_RECYCLE_RANGES`]
        // the parent reaps and respawns it proactively.
        let mut served = 0usize;
        // True until the current child completes its first scan: only a
        // FRESH child's zero-progress death convicts a block — an aged
        // child dying on a range's first claim indicts its own decode
        // cache, not the block (348 false deferrals measured before this
        // distinction; the requeued range simply waits for a fresh
        // owner).
        let mut fresh = true;
        let mut worker = match pool.spawn(slot) {
          Ok(w) => w,
          Err(e) => {
            let mut f = failure.lock().unwrap();
            if f.is_none() {
              *f = Some(e);
            }
            abort.store(true, Ordering::Release);
            return;
          },
        };
        // Monotonic committed-block count; one line per percent crossed.
        let progress = |n: usize| {
          if n == 0 {
            return;
          }
          let d = blocks_done.fetch_add(n, Ordering::AcqRel) + n;
          let pct = d * 100 / total_blocks.max(1);
          if pct > last_pct.fetch_max(pct, Ordering::AcqRel) {
            eprintln!(
              "[scan] {d}/{total_blocks} blocks ({pct}%), {:.0}s",
              start.elapsed().as_secs_f64()
            );
          }
        };
        let commit =
          |reply: ScanReply, origin: u32, seq: u32| -> Result<usize, ()> {
            if !reply.segs.is_empty() {
              done.lock().unwrap().push(((origin, seq), reply.segs));
            }
            if !reply.skips.is_empty() {
              let fatal = pool.fail_fast;
              let first = reply.skips.first().cloned();
              failed.lock().unwrap().extend(reply.skips);
              if fatal {
                if let Some((a, e)) = first {
                  let mut f = failure.lock().unwrap();
                  if f.is_none() {
                    *f = Some(format!(
                      "CheckEnv of block {} failed during scan: {e} \
                     (--no-fail-fast records and skips such blocks)",
                      a.hex()
                    ));
                  }
                }
                return Err(());
              }
            }
            Ok(reply.next)
          };
        // Remainders go to the queue FRONT: a healthy remainder is
        // usually re-popped by the worker that just banked its segments
        // (cache still warm with the region's cone), and a death's
        // remainder retries while its neighborhood is warm — pushed to
        // the back, dense-region remainders sank behind hundreds of
        // chunks and resurfaced 20 minutes later on cold workers, which
        // died again and deferred the region wholesale.
        let requeue = |origin: u32, seq: u32, lo: usize, hi: usize| {
          if lo < hi {
            queue.lock().unwrap().push_front((origin, seq, lo, hi));
          }
        };
        loop {
          if abort.load(Ordering::Acquire) {
            break;
          }
          let next = {
            let mut q = queue.lock().unwrap();
            let popped = q.pop_front();
            if popped.is_some() {
              in_flight.fetch_add(1, Ordering::AcqRel);
            }
            popped
          };
          let Some((origin, seq, lo, hi)) = next else {
            if in_flight.load(Ordering::Acquire) == 0 {
              break;
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
            continue;
          };
          // Proactive recycle between ranges: the env decode cache grows
          // monotonically and never shrinks, so a long-lived child ages
          // toward its cap until ANY dense block kills it — a full-scan
          // fleet reaching the dense tail with saturated caches misread
          // the whole zone as monsters (161 false deferrals; the same
          // tail scanned by young workers ran in 2 minutes with zero).
          // A fresh child costs seconds (order file + env mmap).
          served += 1;
          if served > WORKER_RECYCLE_RANGES {
            served = 1;
            match pool.spawn(slot) {
              Ok(w) => {
                std::mem::replace(&mut worker, w).reap();
                fresh = true;
              },
              Err(err) => {
                let mut f = failure.lock().unwrap();
                if f.is_none() {
                  *f = Some(err);
                }
                abort.store(true, Ordering::Release);
                break;
              },
            }
          }
          match pool.scan(&mut worker, lo, hi) {
            Ok(reply) => {
              fresh = false;
              let was_deferred = reply.deferred;
              let Ok(next) = commit(reply, origin, seq) else {
                abort.store(true, Ordering::Release);
                break;
              };
              if was_deferred && next < hi {
                // Growth-threshold handoff: the walked prefix is banked;
                // the dense remainder waits for the fat phase.
                eprintln!(
                  "[scan] range {next}..{hi} defers to the fat phase \
                   (growth threshold)"
                );
                deferred.lock().unwrap().push((origin, next, hi));
                progress(hi.saturating_sub(lo));
              } else {
                progress(next.saturating_sub(lo));
                requeue(origin, seq + 1, next, hi);
              }
            },
            Err(partial) => {
              let was_fresh = fresh;
              let e = match commit(partial, origin, seq) {
                Ok(n) => n,
                Err(()) => {
                  abort.store(true, Ordering::Release);
                  break;
                },
              };
              progress(e.saturating_sub(lo));
              let status = std::mem::replace(
                &mut worker,
                match pool.spawn(slot) {
                  Ok(w) => w,
                  Err(err) => {
                    let mut f = failure.lock().unwrap();
                    if f.is_none() {
                      *f = Some(err);
                    }
                    abort.store(true, Ordering::Release);
                    break;
                  },
                },
              )
              .reap();
              fresh = true;
              if e >= hi {
                eprintln!(
                  "[scan] worker {slot} died ({status}) after completing \
                   its range; respawned"
                );
              } else if e > lo || !was_fresh {
                // A cache-shed kill: the respawned child (fresh record
                // and decode cache) continues from the committed index.
                // An AGED child dying on a range's first claim indicts
                // its cache, not the block — the range requeues intact
                // and waits for a fresh owner to judge it.
                eprintln!(
                  "[scan] worker {slot} died ({status}) at index {e}; \
                   respawned, continuing"
                );
                requeue(origin, seq + 1, e, hi);
              } else {
                // A fresh worker died on the range's opening claim: this
                // resume point cannot even open under a slot. In the
                // fleet, the WHOLE remainder defers to the cleanup round,
                // which walks it cumulatively under a fat cap — deferring
                // only the block would re-pay the strip's cone per block,
                // one doomed execution each (measured: 1,086 deferrals).
                // In the cleanup round itself the block is named
                // resource-infeasible and the walk continues past it.
                let addr = pool.blocks[pool.order[e] as usize].addr.clone();
                if pool.cleanup {
                  eprintln!(
                    "[scan] block {} exceeded the cleanup cap ({status}) \
                     — resource-infeasible; skipped",
                    addr.hex()
                  );
                  failed.lock().unwrap().push((
                    addr,
                    format!(
                      "record outgrew the {:.1} GiB cleanup cap mid-claim \
                       (cgroup OOM-kill)",
                      f64_from_usize(
                        usize::try_from(pool.cap_bytes).unwrap_or(usize::MAX)
                      ) / GIB
                    ),
                  ));
                  progress(1);
                  requeue(origin, seq + 1, e + 1, hi);
                } else {
                  eprintln!(
                    "[scan] range {e}..{hi} cannot open under its slot \
                     cap ({status}); deferred to the cleanup round"
                  );
                  let _ = addr;
                  deferred.lock().unwrap().push((origin, e, hi));
                  progress(hi - e);
                }
              }
            },
          }
          in_flight.fetch_sub(1, Ordering::AcqRel);
        }
        worker.reap();
      });
    }
  });
  if let Some(e) = failure.into_inner().unwrap() {
    return Err(e);
  }
  let mut tagged = done.into_inner().unwrap();
  tagged.sort_by_key(|(k, _)| *k);
  let mut segments: Vec<Segment> = Vec::new();
  for (_, mut segs) in tagged {
    segments.append(&mut segs);
  }
  let mut deferred = deferred.into_inner().unwrap();
  // Defer-infeasible mode: name every deferred block
  // resource-infeasible instead of walking the deferred ranges under
  // fat caps. The deferred region's cost is cone-bound kernel
  // execution (measured ~6-10 worker-hours on FLT's typeclass-instance
  // core in every slot configuration), so a caller can choose a
  // partition of the tractable content NOW plus an exact exclusion
  // inventory, over an hours-long exhaustive walk.
  if !deferred.is_empty() && pool.defer_infeasible {
    deferred.sort_unstable();
    deferred.dedup();
    let mut f = failed.lock().unwrap();
    let mut named = 0usize;
    for &(_, lo, hi) in &deferred {
      for &b in &pool.order[lo..hi] {
        f.push((
          pool.blocks[b as usize].addr.clone(),
          "deferred dense-core block (IX_SCAN_DEFER_INFEASIBLE=1): \
           opening cone exceeds a fleet slot; not measured"
            .to_string(),
        ));
        named += 1;
      }
    }
    eprintln!(
      "[scan] defer-infeasible: {named} deferred block(s) in \
       {} range(s) named infeasible without measurement",
      deferred.len()
    );
    return Ok(segments);
  }
  if !deferred.is_empty() {
    // Cleanup round: the deferred ranges re-run through this same
    // function under fat caps — the drained pool split a few ways — so
    // dense strips WALK (cone shared, segments cut gracefully at the
    // fat soft cut) instead of being excluded by a slot's even share.
    // Sorted for a deterministic round; `cleanup: true` names blocks
    // that still cannot open resource-infeasible.
    deferred.sort_unstable();
    deferred.dedup();
    // The fat phase's soft cut is cap-derived: dense-region cones run
    // 12-16+ GiB, so segments must exceed the cone to amortize it — a
    // small quantum re-pays the cone per segment (measured: no faster
    // and many more false infeasibles).
    let cleanup_soft_gib = (f64_from_usize(
      usize::try_from(pool.cleanup_cap_bytes).unwrap_or(usize::MAX),
    ) / GIB
      - WORKER_BASELINE_GIB
      - CLAIM_HEADROOM_GIB)
      .max(1.0);
    let cleanup_pool = ProcPool {
      bin: pool.bin.clone(),
      ixe: pool.ixe.clone(),
      cut_used_gib: pool.cut_used_gib,
      batch_blocks: pool.batch_blocks,
      soft_record_gib: cleanup_soft_gib,
      pieces: pool.pieces,
      exec_only: pool.exec_only,
      cap_bytes: pool.cleanup_cap_bytes,
      cleanup_cap_bytes: pool.cleanup_cap_bytes,
      cleanup: true,
      order_file: pool.order_file.clone(),
      capped: pool.capped,
      order: pool.order,
      blocks: pool.blocks,
      fail_fast: pool.fail_fast,
      defer_infeasible: false,
      defer_growth: false,
      price_file: None,
    };
    // Coalesce adjacent deferred ranges: strip remainders abut when a
    // strip spans chunk edges, and a merged range shares its dependency
    // cone across the walk.
    let mut ranges: Vec<(usize, usize)> = Vec::new();
    for &(_, lo, hi) in &deferred {
      match ranges.last_mut() {
        Some((_, top)) if *top >= lo => *top = (*top).max(hi),
        _ => ranges.push((lo, hi)),
      }
    }
    let total: usize = ranges.iter().map(|(lo, hi)| hi - lo).sum();
    eprintln!(
      "[scan] cleanup round: {total} deferred block(s) in {} range(s), {} \
       workers × {:.1} GiB",
      ranges.len(),
      CLEANUP_WORKERS.min(ranges.len()),
      f64_from_usize(
        usize::try_from(pool.cleanup_cap_bytes).unwrap_or(usize::MAX)
      ) / GIB
    );
    let extra = run_pool_procs(
      &cleanup_pool,
      ranges,
      CLEANUP_WORKERS.min(deferred.len()),
      failed,
    )?;
    segments.extend(extra);
    // Deferred singles landed out of order; restore schedule adjacency
    // so the merge pass sums true neighbors.
    let pos: std::collections::HashMap<u32, usize> =
      pool.order.iter().enumerate().map(|(i, &b)| (b, i)).collect();
    segments.sort_by_key(|s| pos.get(&s.blocks[0]).copied().unwrap_or(0));
  }
  Ok(segments)
}

/// Execute-only mode: run the whole env's check schedule through the
/// codegen'd kernel in parallel — no partition, no manifest, no prove
/// concerns. Segments exist only to drop records (cut when a worker's
/// record bytes reach its planned share of box RAM), and the report is
/// the check verdict: blocks checked, kernel rejects named, total
/// measured FFT cost. This is the Aiur-kernel counterpart of the Rust
/// kernel's whole-env check, for wall-clock comparison and for finding
/// divergences (constants one kernel accepts and the other rejects).
pub fn execute_env(
  toplevel: &Toplevel,
  fun_idx: usize,
  env: &Arc<IxonEnv>,
  workers: usize,
  fail_fast: bool,
  proc_workers: Option<(&str, &str)>,
) -> Result<String, String> {
  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  let env_bytes: u64 = blocks.iter().map(|b| b.size).sum();
  let workers = if workers == 0 {
    std::thread::available_parallelism()
      .map_or(4, usize::from)
      .saturating_sub(2)
      .max(1)
  } else {
    workers
  };
  // Provisional: re-bounded by pool/cap-floor once the measured
  // baseline is known (proc mode only).

  let batch_blocks = std::env::var("IX_SCAN_BATCH_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .filter(|&k| k >= 1)
    .unwrap_or(SCAN_BATCH_BLOCKS);
  // The schedule granularity is fixed by the core count so worker sizing
  // cannot change the partition.
  let sched_pieces =
    (std::thread::available_parallelism().map_or(4, usize::from) * 2)
      .min(blocks.len())
      .max(16);
  let order = ordered_schedule(&blocks, &adj, sched_pieces);
  let covered = order.len();
  // Post-schedule RSS: the parent's decode cache and static structures —
  // the residency the worker fleet's record budget sits on top of.
  let baseline_gib = process_rss_gib();
  // `IX_SCAN_RAM_GIB` overrides detected box RAM: every derived number
  // (pool, width, caps, fat-phase slots) then scales exactly as a box
  // of that size would — a budget emulation knob for capacity tests.
  let ram = std::env::var("IX_SCAN_RAM_GIB")
    .ok()
    .and_then(|v| v.parse::<f64>().ok())
    .unwrap_or_else(|| crate::kernel::system_ram_gib().unwrap_or(64.0));
  // Fleet bound by construction: Σ worker slices + parent + OS reserve +
  // the env's page-cache residency (×2 re-read slack) = box RAM. Width
  // goes to the core count when the pool affords a floor slice per
  // worker.
  let env_cache_gib = 2.0 * f64_from_usize(
    usize::try_from(env_bytes).unwrap_or(usize::MAX),
  ) / GIB;
  let pool_gib = ((ram - baseline_gib - OS_RESERVE_GIB - env_cache_gib)
    * POOL_SLICE_FRAC)
    .max(SLICE_FLOOR_GIB);
  let workers =
    bound_workers_by_pool(workers, pool_gib, proc_workers.is_some());
  // Record drop: each worker's even slice of the pool — segments cut
  // (and drop their record) when the record's exact heap reaches it.
  let record_cut_gib = (pool_gib / f64_from_usize(workers))
    - WORKER_BASELINE_GIB
    - CLAIM_HEADROOM_GIB;
  let record_cut_gib = record_cut_gib.max(1.0);
  let n_chunks = (blocks.len() / CHUNK_TARGET_BLOCKS)
    .max(workers * 2)
    .min(blocks.len());
  let bounds = make_chunk_bounds(&order, &blocks, env_bytes, n_chunks);
  eprintln!(
    "[exec] {} blocks, {workers} workers over {} chunks, record \
     drop at {record_cut_gib:.1} GiB, {batch_blocks} blocks per claim",
    blocks.len(),
    bounds.len()
  );
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let abort = std::sync::atomic::AtomicBool::new(false);
  let ctx = ScanCtx {
    toplevel,
    fun_idx,
    env,
    blocks: &blocks,
    cut_used_gib: record_cut_gib,
    n_chunks: bounds.len(),
    fail_fast,
    failed: &failed,
    abort: &abort,
    batch_blocks,
    system: None,
    defer_growth: Some(DEFER_GROWTH_BYTES_PER_BLOCK),
    soft_record_gib: f64::INFINITY,
  };
  let segments = match proc_workers {
    Some((bin, ixe)) => {
      let cap_gib = pool_gib / f64_from_usize(workers);
      let soft_gib = record_cut_gib;
      let capped = systemd_scope_caps_available();
      if !capped {
        eprintln!(
          "[exec] systemd-run --user scopes unavailable — workers run \
           UNCAPPED"
        );
      }
      eprintln!(
        "[exec] process pool: {workers} workers, {cap_gib:.1} GiB cap \
         each{}",
        if capped { " (systemd MemoryMax)" } else { "" }
      );
      let order_file = std::env::temp_dir()
        .join(format!("ix-scan-order-{}.bin", std::process::id()));
      write_order_file(&order_file, &blocks, &order)?;
      let pool = ProcPool {
        bin: bin.to_string(),
        ixe: ixe.to_string(),
        cut_used_gib: soft_gib,
        batch_blocks,
        soft_record_gib: soft_gib,
        pieces: sched_pieces,
        exec_only: true,
        cap_bytes: gib_to_bytes_u64(cap_gib),
        cleanup_cap_bytes: gib_to_bytes_u64(
          pool_gib / f64_from_usize(CLEANUP_WORKERS),
        ),
        cleanup: false,
        order_file,
        capped,
        order: &order,
        blocks: &blocks,
        fail_fast,
        defer_infeasible: false,
        defer_growth: true,
        price_file: None,
      };
      run_pool_procs(&pool, bounds, workers, &failed)?
    },
    None => {
      let chunks =
        bounds.iter().map(|&(lo, hi)| order[lo..hi].to_vec()).collect();
      run_pool(&ctx, chunks, workers)?
    },
  };
  let total_fft: f64 = segments.iter().map(|s| s.fft).sum();
  let checked: usize = segments.iter().map(|s| s.blocks.len()).sum();
  let failed = failed.into_inner().unwrap();
  let mut report = format!(
    "execute: {checked}/{covered} blocks checked in {} segment(s), total \
     measured {:.1} BFFT",
    segments.len(),
    total_fft / 1e9,
  );
  if !failed.is_empty() {
    report.push_str(&format!(
      "\n  [{} kernel-rejected block(s) SKIPPED:]",
      failed.len()
    ));
    for (a, e) in &failed {
      report.push_str(&format!("\n    {} — {e}", a.hex()));
    }
  }
  Ok(report)
}

/// Scan-and-cut over the whole env: returns the manifest report, writing
/// the manifest and its costs sidecar to `out_path`.
#[allow(clippy::too_many_arguments)]
/// The predicted-vs-measured margin the cut leaves under the budget:
/// the analytic model predicts live bytes, and measured MaxRSS runs a
/// few percent above (allocator slack, the prove process's own env
/// decode cache, OS overhead) — validated at +3.0% worst across a
/// stratified Init prove sample. 0.95 covers it with room.
const PROVE_RAM_MARGIN: f64 = 0.95;

/// GiB → whole bytes via the decimal round-trip (no `as` cast); caps are
/// small positive magnitudes.
fn gib_to_bytes_u64(gib: f64) -> u64 {
  format!("{:.0}", (gib * GIB).max(0.0)).parse().unwrap_or(u64::MAX)
}

pub fn scan_shards(
  system: &AiurSystem,
  fun_idx: usize,
  env: &Arc<IxonEnv>,
  budget_gib: f64,
  eps: f64,
  workers: usize,
  fail_fast: bool,
  defer_infeasible: bool,
  reprice: bool,
  out_path: &str,
  proc_workers: Option<(&str, &str)>,
) -> Result<String, String> {
  let toplevel = system.toplevel();
  if budget_gib < 4.0 {
    return Err(format!(
      "budget {budget_gib} GiB is below the prover's fixed floor \
       (preprocessed gadget tables + base structures)"
    ));
  }
  // The ε-discounted cut: a shard ends when its predicted peak prove
  // RSS (analytic, from circuit shapes) reaches the margined budget.
  let cut_used_gib = budget_gib * PROVE_RAM_MARGIN * (1.0 - eps);

  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  let env_bytes: u64 = blocks.iter().map(|b| b.size).sum();
  let workers = if workers == 0 {
    std::thread::available_parallelism()
      .map_or(4, usize::from)
      .saturating_sub(2)
      .max(1)
  } else {
    workers
  };
  // Provisional: re-bounded by pool/cap-floor once the measured
  // baseline is known (proc mode only).

  let batch_blocks = std::env::var("IX_SCAN_BATCH_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .filter(|&k| k >= 1)
    .unwrap_or(SCAN_BATCH_BLOCKS);
  // The schedule granularity is fixed by the core count so worker sizing
  // cannot change the partition.
  let sched_pieces =
    (std::thread::available_parallelism().map_or(4, usize::from) * 2)
      .min(blocks.len())
      .max(16);
  let order = ordered_schedule(&blocks, &adj, sched_pieces);
  // Post-schedule RSS: the parent's decode cache and static structures —
  // the residency the worker pool's budget sits on top of.
  let baseline_gib = process_rss_gib();
  // Width-first sizing: full core width while every worker's even slice
  // of the pool clears the floor. Claim widths derived from measured
  // growth bound mid-claim overshoot on any content, so slices are
  // segment quanta, not worst-case-claim reserves — the merge pass sums
  // segments to the cut, and the kernel kill stays a backstop. Blocks
  // too heavy even for a slice are deferred to the fat-cap cleanup
  // round or named infeasible.
  // `IX_SCAN_RAM_GIB` overrides detected box RAM: every derived number
  // (pool, width, caps, fat-phase slots) then scales exactly as a box
  // of that size would — a budget emulation knob for capacity tests.
  let ram = std::env::var("IX_SCAN_RAM_GIB")
    .ok()
    .and_then(|v| v.parse::<f64>().ok())
    .unwrap_or_else(|| crate::kernel::system_ram_gib().unwrap_or(64.0));
  // Fleet bound by construction: Σ worker slices + parent + OS reserve +
  // the env's page-cache residency = box RAM. The env term keeps the
  // shared mmap cache-resident (×2 for re-read slack): without it, a
  // fleet at its caps evicts the very pages every worker faults from.
  let env_cache_gib = 2.0 * f64_from_usize(
    usize::try_from(env_bytes).unwrap_or(usize::MAX),
  ) / GIB;
  let pool_gib = ((ram - baseline_gib - OS_RESERVE_GIB - env_cache_gib)
    * POOL_SLICE_FRAC)
    .max(SLICE_FLOOR_GIB);
  let workers =
    bound_workers_by_pool(workers, pool_gib, proc_workers.is_some());
  let proc_cap_gib = proc_workers.map(|_| {
    std::env::var("IX_SCAN_WORKER_CAP_GIB")
      .ok()
      .and_then(|v| v.parse::<f64>().ok())
      .unwrap_or_else(|| pool_gib / f64_from_usize(workers))
  });
  let n_chunks = (blocks.len() / CHUNK_TARGET_BLOCKS)
    .max(workers * 2)
    .min(blocks.len());
  let bounds = make_chunk_bounds(&order, &blocks, env_bytes, n_chunks);
  let chunk_count = bounds.len();
  eprintln!(
    "[scan] {} blocks, {workers} workers over {chunk_count} chunks, cut at \
     {cut_used_gib:.1} GiB predicted prove RSS (margin \
     {:.0}%, ε pre-charged), {batch_blocks} blocks per claim",
    blocks.len(),
    (1.0 - PROVE_RAM_MARGIN) * 100.0
  );
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let abort = std::sync::atomic::AtomicBool::new(false);
  let ctx = ScanCtx {
    toplevel,
    fun_idx,
    env,
    blocks: &blocks,
    cut_used_gib,
    n_chunks: chunk_count,
    fail_fast,
    failed: &failed,
    abort: &abort,
    batch_blocks,
    system: Some(system),
    defer_growth: None,
    soft_record_gib: f64::INFINITY,
  };
  let segments = match proc_workers {
    Some((bin, ixe)) => {
      let cap_gib = proc_cap_gib.unwrap_or(16.0);
      let soft_gib =
        (cap_gib - WORKER_BASELINE_GIB - CLAIM_HEADROOM_GIB).max(1.0);
      let order_file = std::env::temp_dir()
        .join(format!("ix-scan-order-{}.bin", std::process::id()));
      write_order_file(&order_file, &blocks, &order)?;
      let capped = systemd_scope_caps_available();
      if !capped {
        eprintln!(
          "[scan] systemd-run --user scopes unavailable — workers run \
           UNCAPPED"
        );
      }
      eprintln!(
        "[scan] process pool: {workers} workers, {cap_gib:.1} GiB cap \
         each{}, soft record cut {soft_gib:.1} GiB",
        if capped { " (systemd MemoryMax)" } else { "" },
      );
      let pool = ProcPool {
        bin: bin.to_string(),
        ixe: ixe.to_string(),
        cut_used_gib,
        batch_blocks,
        soft_record_gib: soft_gib,
        pieces: sched_pieces,
        exec_only: false,
        cap_bytes: gib_to_bytes_u64(cap_gib),
        cleanup_cap_bytes: gib_to_bytes_u64(
          pool_gib / f64_from_usize(CLEANUP_WORKERS),
        ),
        cleanup: false,
        order_file,
        capped,
        order: &order,
        blocks: &blocks,
        fail_fast,
        defer_infeasible,
        defer_growth: false,
        price_file: None,
      };
      run_pool_procs(&pool, bounds, workers, &failed)?
    },
    None => {
      let chunks =
        bounds.iter().map(|&(lo, hi)| order[lo..hi].to_vec()).collect();
      run_pool(&ctx, chunks, workers)?
    },
  };

  // Assemble shards by summing adjacent segments, then COLD RE-PRICE
  // each merged shard: one execution of its whole CheckEnv claim (the
  // exact claim its prove runs) replaces the summed cost. Sums are
  // conservative (shared cones derive once in the union; padded heights
  // are subadditive) but by a measured ~1.6x, so the merge packs past
  // the cut by [`PACK_OVERSHOOT`] and the re-price decides: an over-cut
  // shard splits at its ram midpoint and the halves re-price, to a
  // bounded depth. Process-pool mode only; the thread pool (tests)
  // keeps the pure summed pack at the plain cut.
  let pre_merge = segments.len();
  // Opt-in (`ix shard --reprice`, fail-fast mode strings "3"/"4"): the
  // cold re-price is prove-validated on Init (+0.77% at a shard packed
  // to the cut) but not yet on FLT/Mathlib-class content, so summed
  // conservative costs remain the default until each env's re-priced
  // manifest passes its heaviest-shard prove protocol.
  let pricing = reprice && proc_workers.is_some();
  let pack_target =
    if pricing { cut_used_gib * PACK_OVERSHOOT } else { cut_used_gib };
  let mut groups: Vec<Vec<Segment>> = Vec::new();
  {
    let mut sums: Vec<f64> = Vec::new();
    for seg in segments {
      match (groups.last_mut(), sums.last_mut()) {
        (Some(g), Some(sum)) if *sum + seg.ram_gib < pack_target => {
          *sum += seg.ram_gib;
          g.push(seg);
        },
        _ => {
          sums.push(seg.ram_gib);
          groups.push(vec![seg]);
        },
      }
    }
  }
  // (summed fft, summed ram, priced (fft, ram) once measured)
  let group_sum = |g: &Vec<Segment>| -> (f64, f64) {
    g.iter().fold((0.0, 0.0), |(f, r), s| (f + s.fft, r + s.ram_gib))
  };
  let mut priced: Vec<Option<(f64, f64)>> = vec![None; groups.len()];
  if pricing {
    let (bin, ixe) = proc_workers.expect("pricing implies proc workers");
    let t0 = std::time::Instant::now();
    // The scan pool (and its order file) are gone; the price pool gets
    // fresh copies of both sidecar files.
    let order_file = std::env::temp_dir()
      .join(format!("ix-price-order-{}.bin", std::process::id()));
    write_order_file(&order_file, &blocks, &order)?;
    let price_file = std::env::temp_dir()
      .join(format!("ix-price-shards-{}.bin", std::process::id()));
    let width = REPRICE_WORKERS.min(groups.len()).max(1);
    let cap_gib = (pool_gib / f64_from_usize(REPRICE_WORKERS))
      .max(SLICE_FLOOR_GIB);
    let price_pool = ProcPool {
      bin: bin.to_string(),
      ixe: ixe.to_string(),
      cut_used_gib,
      batch_blocks,
      soft_record_gib: f64::INFINITY,
      pieces: sched_pieces,
      exec_only: false,
      cap_bytes: gib_to_bytes_u64(cap_gib),
      cleanup_cap_bytes: gib_to_bytes_u64(cap_gib),
      cleanup: true,
      order_file: order_file.clone(),
      capped: systemd_scope_caps_available(),
      order: &order,
      blocks: &blocks,
      fail_fast: false,
      defer_infeasible: false,
      defer_growth: false,
      price_file: Some(price_file.clone()),
    };
    // Rounds: price every unpriced group; split over-cut multi-segment
    // groups at their summed-ram midpoint and unprice the halves.
    for _round in 0..3 {
      let todo: Vec<usize> =
        (0..groups.len()).filter(|&i| priced[i].is_none()).collect();
      if todo.is_empty() {
        break;
      }
      let members: Vec<Vec<u32>> = todo
        .iter()
        .map(|&i| {
          groups[i].iter().flat_map(|s| s.blocks.iter().copied()).collect()
        })
        .collect();
      write_price_file(&price_file, &members)?;
      let queue: Mutex<std::collections::VecDeque<usize>> =
        Mutex::new((0..todo.len()).collect());
      let results: Mutex<Vec<Option<(f64, f64)>>> =
        Mutex::new(vec![None; todo.len()]);
      std::thread::scope(|sc| {
        for slot in 0..width.min(todo.len()) {
          let (queue, results, price_pool) = (&queue, &results, &price_pool);
          sc.spawn(move || {
            let mut worker = match price_pool.spawn(slot) {
              Ok(w) => w,
              Err(_e) => return,
            };
            loop {
              let Some(j) = queue.lock().unwrap().pop_front() else {
                break;
              };
              match price_pool.price(&mut worker, j) {
                Ok(cost) => results.lock().unwrap()[j] = Some(cost),
                Err(_e) => {
                  // Death or pricing error: one fresh-worker retry,
                  // then the group falls back to its summed cost.
                  worker = match price_pool.spawn(slot) {
                    Ok(w) => w,
                    Err(_e) => break,
                  };
                  if let Ok(cost) = price_pool.price(&mut worker, j) {
                    results.lock().unwrap()[j] = Some(cost);
                  }
                }
              }
            }
            worker.reap();
          });
        }
      });
      let results = results.into_inner().unwrap();
      for (pos, &i) in todo.iter().enumerate() {
        priced[i] = Some(match results[pos] {
          Some(cost) => cost,
          None => group_sum(&groups[i]),
        });
      }
      // Split over-cut multi-segment groups; their halves re-price in
      // the next round.
      let mut next_groups: Vec<Vec<Segment>> = Vec::new();
      let mut next_priced: Vec<Option<(f64, f64)>> = Vec::new();
      let mut split = 0usize;
      for (i, g) in groups.into_iter().enumerate() {
        let over = priced[i].is_some_and(|(_f, r)| r >= cut_used_gib);
        if over && g.len() > 1 {
          let total: f64 = g.iter().map(|s| s.ram_gib).sum();
          let mut acc = 0.0;
          let mut cutp = g.len() - 1;
          for (k, s) in g.iter().enumerate() {
            acc += s.ram_gib;
            if acc >= total / 2.0 {
              cutp = (k + 1).min(g.len() - 1);
              break;
            }
          }
          let mut a = g;
          let b = a.split_off(cutp);
          split += 1;
          next_groups.push(a);
          next_priced.push(None);
          next_groups.push(b);
          next_priced.push(None);
        } else {
          next_priced.push(priced[i]);
          next_groups.push(g);
        }
      }
      groups = next_groups;
      priced = next_priced;
      if split == 0 {
        break;
      }
      eprintln!("[scan] re-price: {split} over-cut shard(s) split");
    }
    let _ = std::fs::remove_file(&order_file);
    let _ = std::fs::remove_file(&price_file);
    let ratios: Vec<f64> = groups
      .iter()
      .zip(&priced)
      .filter_map(|(g, p)| {
        p.map(|(_f, r)| {
          let (_sf, sr) = group_sum(g);
          if sr > 0.0 { r / sr } else { 1.0 }
        })
      })
      .collect();
    let (rmin, rmax) = ratios.iter().fold((f64::MAX, 0.0f64), |(lo, hi), &r| {
      (lo.min(r), hi.max(r))
    });
    eprintln!(
      "[scan] re-price: {} shard(s) cold-priced in {:.0}s \
       (true/summed {:.2}-{:.2})",
      groups.len(),
      t0.elapsed().as_secs_f64(),
      rmin,
      rmax
    );
  }
  // Flatten to the manifest's segment shape, carrying the priced (or
  // summed-fallback) cost per shard.
  let segments: Vec<Segment> = groups
    .into_iter()
    .zip(priced)
    .map(|(g, p)| {
      let (sf, sr) = group_sum(&g);
      let (fft, ram_gib) = p.unwrap_or((sf, sr));
      let blocks: Vec<u32> =
        g.into_iter().flat_map(|s| s.blocks).collect();
      Segment { blocks, fft, ram_gib }
    })
    .collect();

  // Manifest: owned blocks per segment; frontier fields are the claim
  // layer's business (reconstructed from env + owned at check/prove time).
  let num = segments.len();
  let mut infos = Vec::with_capacity(num);
  for (id, seg) in segments.iter().enumerate() {
    let mut addrs: Vec<Address> =
      seg.blocks.iter().map(|&b| blocks[b as usize].addr.clone()).collect();
    addrs.sort();
    let own_size: u64 =
      seg.blocks.iter().map(|&b| blocks[b as usize].size).sum();
    infos.push(ShardInfo {
      id: u32::try_from(id).expect("shard count exceeds u32"),
      blocks: addrs,
      cost: ShardCost::AiurFft(cost_fft(seg.fft)),
      own_size,
      foreign_blocks: Vec::new(),
      cross_ingress: 0,
      assumption_root: None,
    });
  }
  let num_u32 = u32::try_from(num).expect("shard count exceeds u32");
  let manifest = ShardManifest {
    num_shards: num_u32,
    shards: infos,
    total_cross_ingress: 0,
    tree: Some(balanced_agg_tree(0, num_u32)),
  };
  std::fs::write(out_path, manifest.to_bytes())
    .map_err(|e| format!("write {out_path}: {e}"))?;

  // Costs sidecar: MEASURED fft per shard mapped through the calibrated
  // resource lines — same header the batch prove driver's heaviest-first
  // ordering reads; the counter columns are zero (nothing was predicted).
  let mut csv = String::from(
    "shard,union_bytes,hb,subst,subst_unique,whnf,def_eq,nat_arith,\
     pred_ram_gib,pred_prove_s\n",
  );
  let mut max_ram = 0.0f64;
  let mut over = 0usize;
  for (id, seg) in segments.iter().enumerate() {
    let own: u64 = seg.blocks.iter().map(|&b| blocks[b as usize].size).sum();
    // Predicted prove RSS = the fft resource line PLUS the measured
    // record bytes the prove's execute replays into — the second term is
    // what the fitted line missed on arithmetic-heavy shards.
    let ram = seg.ram_gib;
    csv.push_str(&format!(
      "{},{},0,0,0,0,0,0,{:.2},{:.2}\n",
      id,
      own,
      ram,
      aiur_prove_secs_for_fft(seg.fft),
    ));
    max_ram = max_ram.max(ram);
    if seg.ram_gib >= cut_used_gib / (1.0 - eps) {
      over += 1;
    }
  }
  let cp = format!("{out_path}.costs.csv");
  std::fs::write(&cp, csv).map_err(|e| format!("write {cp}: {e}"))?;

  let mut note = if over > 0 {
    format!(
      "\n  [{over} single-block segment(s) exceed the cap alone — atomically \
       infeasible at this budget]"
    )
  } else {
    String::new()
  };
  let failed = failed.into_inner().unwrap();
  if !failed.is_empty() {
    let mut fcsv = String::from("block,error\n");
    for (a, e) in &failed {
      fcsv.push_str(&format!(
        "{},{}\n",
        a.hex(),
        e.replace('\n', " ").replace(',', ";")
      ));
    }
    let fp = format!("{out_path}.failed.csv");
    std::fs::write(&fp, fcsv).map_err(|e| format!("write {fp}: {e}"))?;
    note.push_str(&format!(
      "\n  [{} kernel-rejected block(s) SKIPPED — the partition does NOT \
       cover them (the coverage gate will name them); see {fp}]",
      failed.len()
    ));
  }
  Ok(format!(
    "scan: {} blocks in {} chunks → {num} shards ({pre_merge} pre-merge) @ \
     {budget_gib:.0} GiB (cut at {:.1} GiB combined, ε {:.0}%)\nmax \
     predicted prove RSS {max_ram:.1} GiB (analytic, from circuit \
     shapes){note}",
    blocks.len(),
    chunk_count,
    cut_used_gib,
    eps * 100.0,
  ))
}

/// Number of segments one work-range yields before its remainder goes
/// back on the queue for any idle worker.
const RANGE_SEGMENTS: usize = 2;

/// Scan one range: execute thin-frontier `CheckEnv` claims — one per
/// BATCH of [`ScanCtx::batch_blocks`] blocks — against a shared record
/// and lazily-faulted witness, checkpointing the running (fft, record
/// bytes) after every claim and cutting on the batch boundary where it
/// reaches the cut (the crossing batch re-executes as the next segment's
/// first claim, so an emitted shard never exceeds the cut). Batching is
/// what keeps the running readout honest: the claim layer's per-claim
/// costs (in-circuit assumption-tree hashing, `env_walk` frames that are
/// never memo-shared across claims, members assumed by one claim then
/// checked by the next) shrink ~K-fold, and intra-batch edges stop being
/// frontier members entirely, so the checkpoint stays a tight upper
/// bound on the emitted shard's cold cost without a blanket re-price.
///
/// Any batch-level event that needs per-block attribution — the segment's
/// FIRST claim crossing the cut, a kernel reject, or a record-cap trip
/// with nothing banked — ends the segment at the last clean checkpoint
/// (the polluted record is dropped) and re-enters that batch through a
/// NARROW window, one block per claim, where the single-block semantics
/// apply verbatim: a lone block over the cut is emitted alone with its
/// measured cost, a rejected or over-cap block is named and skipped.
/// Emits at most [`RANGE_SEGMENTS`] segments, then returns the remaining
/// blocks for any idle worker; a remainder re-queued mid-window simply
/// rediscovers the event deterministically.
fn scan_range(
  ctx: &ScanCtx<'_>,
  chunk: &[u32],
  origin: u32,
) -> Result<(Vec<Segment>, Vec<u32>, bool), String> {
  let t0 = std::time::Instant::now();
  let chunk_id = origin;
  let n_chunks = ctx.n_chunks;
  let mut segments: Vec<Segment> = Vec::new();
  let mut lo = 0usize;
  // Set when measured growth crossed the phase-1 threshold: the range's
  // remainder is handed back marked for the fat phase.
  let mut defer_rest = false;
  // Blocks below this index (and at/after `lo`) execute one per claim:
  // a batch-level event landed in [lo, narrow_until) and needs per-block
  // attribution. Stale values (< hi) are inert.
  let mut narrow_until = 0usize;
  // Running record growth per block (bytes), from the last claim's
  // measured growth — the range's execution history is content-fixed,
  // so the estimate (and thus every claim width) is deterministic.
  // `None` until the first claim measures.
  let mut growth_per_block: Option<f64> = None;
  while lo < chunk.len() && segments.len() < RANGE_SEGMENTS && !defer_rest {
    let mut record = QueryRecord::new(ctx.toplevel);
    let mut io = IOBuffer::with_backing(EnvFaultSource::new(ctx.env.clone()));
    let mut prev_fft = 0.0f64;
    let mut prev_ram = 0.0f64;
    let mut hi = lo;
    let mut skip_failed = false;
    let (seg_end, seg_fft, seg_ram) = loop {
      if hi >= chunk.len() {
        break (hi, prev_fft, prev_ram);
      }
      if ctx.abort.load(Ordering::Acquire) {
        return Err("aborted after a failure elsewhere".to_string());
      }
      // Claim width from measured growth: K sized so this claim's
      // expected record growth is ~CLAIM_TARGET_GIB. Light content runs
      // full width; dense content shrinks to K=1-2, where per-claim
      // overhead is negligible against per-block cost — one rule bounds
      // mid-claim growth on every content class. Before the first
      // measurement the estimate is unknown and the claim starts small.
      let k = if hi < narrow_until {
        1
      } else {
        let by_growth = match growth_per_block {
          // No measurement yet: a single block seeds the estimator. A
          // wider opening claim cascades in monster strips — after a
          // deferral the follow-up range also starts unmeasured, so any
          // multi-block seed re-dies block after block (measured: 998
          // one-death-one-deferral blocks at a 4-block seed, where the
          // same strips scanned clean once estimators were trained).
          None => 1,
          Some(g) => {
            let target = CLAIM_TARGET_GIB * GIB;
            format!("{:.0}", (target / g.max(1.0)).clamp(1.0, 4096.0))
              .parse::<usize>()
              .unwrap_or(1)
              .min(ctx.batch_blocks)
          },
        };
        by_growth.min(chunk.len() - hi)
      };
      let addrs: Vec<Address> = chunk[hi..hi + k]
        .iter()
        .map(|&b| ctx.blocks[b as usize].addr.clone())
        .collect();
      let heap_before = record_heap_bytes(&record);
      let out: Result<(), String> = seed_shard_check_env_claim(
        ctx.env, &addrs, &mut io,
      )
      .and_then(|(_claim, input)| {
        execute_ixvm_with_record(
          ctx.toplevel,
          ctx.fun_idx,
          &input,
          &mut io,
          &mut record,
        )
        .map(|_| ())
        .map_err(|e| e.to_string())
      });
      growth_per_block = Some(
        (f64_from_usize(record_heap_bytes(&record).saturating_sub(
          heap_before,
        )) / f64_from_usize(k))
        .max(1.0),
      );
      // Phase-1 growth deferral: the claim that just executed is banked
      // (its checks are done), and the remainder waits for the fat
      // phase — dense content is only cheap walked warm with room, and
      // the threshold sits in the decade-wide gap between the light and
      // dense growth populations.
      if let (Some(threshold), Some(g)) = (ctx.defer_growth, growth_per_block)
        && g > threshold
        && hi >= narrow_until
      {
        defer_rest = true;
        break (hi + k, record_fft_cost(ctx.toplevel, &record), {
          let rec =
            f64_from_usize(record_heap_bytes(&record)) / GIB;
          match ctx.system {
            Some(sys) => {
              f64_from_usize(sys.peak_prove_bytes(&record).peak) / GIB
            },
            None => rec,
          }
        });
      }
      if let Err(e) = out {
        if k > 1 {
          // Per-block attribution needed: end the segment at the last
          // clean checkpoint (dropping the polluted record) and rescan
          // this batch one block per claim.
          eprintln!(
            "[scan {chunk_id}/{n_chunks}] narrowing batch at block \
             {hi}: {e}"
          );
          narrow_until = hi + k;
          break (hi, prev_fft, prev_ram);
        }
        let addr = &addrs[0];
        if ctx.fail_fast {
          return Err(format!(
            "CheckEnv of block {} failed during scan: {e} \
             (--no-fail-fast records and skips such blocks)",
            addr.hex()
          ));
        }
        // No fail-fast: name the block NOW, drop it from the partition,
        // and emit the running segment so the failed execution's partial
        // rows cannot pollute later measurements (fresh record).
        eprintln!(
          "[scan {chunk_id}/{n_chunks}] SKIPPING block {}: {e}",
          addr.hex()
        );
        ctx.failed.lock().unwrap().push((addr.clone(), e));
        skip_failed = true;
        break (hi, prev_fft, prev_ram);
      }
      let fft = record_fft_cost(ctx.toplevel, &record);
      let rec_gib = f64_from_usize(record_heap_bytes(&record)) / GIB;
      // The cut measure: for the scan, the analytic peak-prove-RSS
      // prediction from the record's circuit shapes; for execute-only
      // segments (which exist only to bound the live record), the
      // record's retained bytes against the per-worker share.
      let ram_gib = match ctx.system {
        Some(sys) => f64_from_usize(sys.peak_prove_bytes(&record).peak) / GIB,
        None => rec_gib,
      };
      if ram_gib >= ctx.cut_used_gib || rec_gib >= ctx.soft_record_gib {
        if hi == lo {
          if k > 1 {
            // The segment's first batch crosses the whole cut: find the
            // culprit at per-block granularity before emitting anything.
            eprintln!(
              "[scan {chunk_id}/{n_chunks}] narrowing batch at block \
               {hi}: first claim crossed the cut"
            );
            narrow_until = hi + k;
            break (hi, prev_fft, prev_ram);
          }
          // A single block alone reaches the cut: atomically infeasible
          // at this budget — emitted alone with its measured cost.
          break (hi + 1, fft, ram_gib);
        }
        break (hi, prev_fft, prev_ram);
      }
      if segments.is_empty() && lo == 0 && hi == lo {
        // Bank the range's very first claim as its own segment: the
        // committed index then advances past it immediately, so any
        // later death in this range preserves progress (`e > lo`) and
        // is answered by respawn-and-continue. A zero-progress death
        // therefore means exactly "this claim, alone, on this worker" —
        // the conviction the deferral path assumes. One extra seed-size
        // segment per range; the merge pass absorbs it.
        break (hi + k, fft, ram_gib);
      }
      hi += k;
      prev_fft = fft;
      prev_ram = ram_gib;
    };
    if query_stats_enabled() {
      dump_query_stats(&record, &format!("scan {chunk_id} seg"));
    }
    // A failure on a segment's FIRST block leaves nothing to emit; the
    // failed block itself is skipped either way (`skip_failed`).
    if seg_end > lo {
      // Memory decomposition per segment: witness arena G-elements, io
      // map entries, record entries — with process RSS, these split the
      // footprint into decode-cache baseline / live worker data /
      // unaccounted, so a single run localizes any growth.
      let arena_g: usize = io.data.values().map(Vec::len).sum();
      let rec_e: usize =
        record.function_queries.iter().map(|m| m.len()).sum::<usize>()
          + record.memory_queries.iter().map(|(_, m)| m.len()).sum::<usize>();
      eprintln!(
        "[scan {chunk_id}/{n_chunks}] segment: {} blocks, {:.2} BFFT, \
         {:.1}G {}, {}/{} blocks done, {:.0}s, rss {:.0}G, arena {}M, \
         iomap {}k, rec {}M entries/{:.1}G heap",
        seg_end - lo,
        seg_fft / 1e9,
        seg_ram,
        if ctx.system.is_some() { "pred-RSS" } else { "rec" },
        seg_end,
        chunk.len(),
        t0.elapsed().as_secs_f64(),
        process_rss_gib(),
        arena_g / 1_000_000,
        io.map.len() / 1000,
        rec_e / 1_000_000,
        f64_from_usize(record_heap_bytes(&record)) / GIB
      );
      segments.push(Segment {
        blocks: chunk[lo..seg_end].to_vec(),
        fft: seg_fft,
        ram_gib: seg_ram,
      });
    }
    lo = seg_end + usize::from(skip_failed);
  }
  if lo >= chunk.len() {
    eprintln!(
      "[scan {chunk_id}/{n_chunks}] range done: {} blocks → {} segment(s), \
       {:.0}s",
      chunk.len(),
      segments.len(),
      t0.elapsed().as_secs_f64()
    );
  }
  Ok((segments, chunk[lo..].to_vec(), defer_rest))
}

use lean_ffi::object::{
  LeanBorrowed, LeanExcept, LeanExternal, LeanNat, LeanOwned, LeanString,
};

use crate::aiur::toplevel::decode_toplevel;
use crate::lean::LeanAiurToplevel;

/// `Bytecode.Toplevel.scanShardsWithEnv`: scan-and-cut sharding against a
/// Rust-owned `EnvHandle`. Numeric params are decimal strings (ABI-simple):
/// `budget_gib` (RAM budget per shard, GiB), `eps_pct` (pre-charged cut
/// headroom, percent), `workers` (parallel chunk scanners; `0` autoscales
/// to cores and detected RAM — each worker holds one segment's QueryRecord
/// and faulted witness). Writes `out_path` (.ixes) plus its `.costs.csv`
/// sidecar carrying the MEASURED per-shard FFT mapped through the
/// calibrated resource lines.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_scan_shards_with_env(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  budget_gib: LeanString<LeanBorrowed<'_>>,
  eps_pct: LeanString<LeanBorrowed<'_>>,
  workers: LeanString<LeanBorrowed<'_>>,
  fail_fast: LeanString<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
  worker_bin: LeanString<LeanBorrowed<'_>>,
  ixe_path: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let budget = budget_gib.to_string().parse::<f64>().unwrap_or(0.0);
  if budget <= 0.0 {
    return LeanExcept::error_string("scan: pass a positive RAM budget (GiB)");
  }
  let eps = eps_pct.to_string().parse::<f64>().unwrap_or(5.0) / 100.0;
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  // `fail_fast` mode string: "1" abort on the first kernel reject, "0"
  // record-and-skip, "2" record-and-skip + name deferred dense ranges
  // infeasible, "3" as "0" + cold re-price, "4" as "2" + cold re-price.
  let mode = fail_fast.to_string();
  let fail_fast = mode == "1";
  let defer_infeasible = mode == "2" || mode == "4";
  let reprice = mode == "3" || mode == "4";
  let (bin, ixe) = (worker_bin.to_string(), ixe_path.to_string());
  let proc_workers = (!bin.is_empty() && !ixe.is_empty())
    .then_some((bin.as_str(), ixe.as_str()));
  match scan_shards(
    system.get(),
    fun_idx,
    &env_handle.get().env,
    budget,
    eps,
    workers,
    fail_fast,
    defer_infeasible,
    reprice,
    &out_path.to_string(),
    proc_workers,
  ) {
    Ok(report) => {
      eprintln!("[rs_scan]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => LeanExcept::error_string(&format!("rs_aiur_scan_shards: {e}")),
  }
}

/// `Bytecode.Toplevel.executeEnvWithEnv`: execute-only whole-env check
/// through the codegen'd Aiur kernel — no partition, no manifest (see
/// [`execute_env`]). Numeric params are decimal strings (ABI-simple):
/// `workers` (`0` autoscales), `fail_fast` (`0` records and skips
/// kernel-rejected blocks instead of aborting).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_execute_env_with_env(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  workers: LeanString<LeanBorrowed<'_>>,
  fail_fast: LeanString<LeanBorrowed<'_>>,
  worker_bin: LeanString<LeanBorrowed<'_>>,
  ixe_path: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let fail_fast = fail_fast.to_string() != "0";
  let (bin, ixe) = (worker_bin.to_string(), ixe_path.to_string());
  let proc_workers = (!bin.is_empty() && !ixe.is_empty())
    .then_some((bin.as_str(), ixe.as_str()));
  match execute_env(
    &toplevel,
    fun_idx,
    &env_handle.get().env,
    workers,
    fail_fast,
    proc_workers,
  ) {
    Ok(report) => {
      eprintln!("[rs_exec]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => LeanExcept::error_string(&format!("rs_aiur_execute_env: {e}")),
  }
}

/// `Aiur.AiurSystem.scanWorker`: the child side of the process pool —
/// runs [`scan_worker`]'s stdin/stdout loop until EOF. Numeric params are
/// decimal strings: cut (GiB), batch blocks, soft record cut (GiB),
/// schedule pieces (must match the parent's chunk count), exec-only
/// ("1" = record-bytes cut, no model).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_scan_worker(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  cut_gib: LeanString<LeanBorrowed<'_>>,
  batch: LeanString<LeanBorrowed<'_>>,
  soft_cap_gib: LeanString<LeanBorrowed<'_>>,
  pieces: LeanString<LeanBorrowed<'_>>,
  exec_only: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let cut = cut_gib.to_string().parse::<f64>().unwrap_or(f64::INFINITY);
  let batch = batch.to_string().parse::<usize>().unwrap_or(SCAN_BATCH_BLOCKS);
  let soft = soft_cap_gib.to_string().parse::<f64>().unwrap_or(f64::INFINITY);
  let pieces = pieces.to_string().parse::<usize>().unwrap_or(16);
  // Mode string: "0" scan, "1" execute-only, "2" execute-only with
  // growth-threshold deferral (phase 1 of the two-phase execute).
  let mode = exec_only.to_string();
  let exec_only = mode == "1" || mode == "2";
  let defer_growth = mode == "2";
  match scan_worker(
    system.get(),
    fun_idx,
    &env_handle.get().env,
    cut,
    batch,
    soft,
    pieces,
    exec_only,
    defer_growth,
  ) {
    Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanExcept::error_string(&format!("rs_aiur_scan_worker: {e}")),
  }
}
