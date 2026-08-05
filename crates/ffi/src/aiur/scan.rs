//! Scan-and-cut sharding: shard boundaries from Aiur's own measured cost.
//!
//! Instead of predicting shard cost from profile counters, the env's check
//! schedule is EXECUTED through the codegen'd circuit kernel with a running
//! FFT-cost readout, and a shard boundary is cut where the measured cost
//! reaches the RAM budget's FFT equivalent. Execution is the mandatory
//! prefix of proving, so the measurement is the prove's own cost, not a
//! proxy — the failure mode where a recorder-side counter under-represents
//! circuit work by a content-dependent factor cannot occur.
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
    query_stats_enabled, record_fft_cost, record_retained_bytes,
  },
};
use ix_common::address::Address;
use ix_kernel::profile::{OpCounts, ProfileBuilder};
use ix_kernel::shard::{
  AIUR_RAM_BASE_GIB, AIUR_RAM_GIB_PER_BFFT, AIUR_RAM_USABLE_FRAC, ShardCost,
  ShardInfo, ShardManifest, aiur_prove_secs_for_fft, aiur_ram_gib_for_fft,
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

/// Fraction of detected system RAM the worker fleet may plan against.
/// The fleet bound is arithmetic, not reactive: `workers × record cap`
/// is chosen under this line at startup, and the per-worker cap is
/// enforced inside execution, so measured RSS never depends on content.
const RAM_CEILING_FRAC: f64 = 0.70;

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
  bytes_gib: f64,
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
  /// Execute-only mode: the cut charges RECORD BYTES alone against
  /// `cut_used_gib` (a per-worker share of box RAM) — segments exist only
  /// to drop records and keep the fleet resident — and no partition
  /// semantics attach to the boundaries. RAM is bounded at claim
  /// granularity only: a single claim's growth is uninstrumented by
  /// design (Aiur execution carries no RAM tracking), so
  /// pathologically dense content is bounded by worker count, not by
  /// abort.
  exec_only: bool,
}

/// Default blocks per measurement claim; `IX_SCAN_BATCH_BLOCKS`
/// overrides (1 restores per-block claims). Fixed — never adaptive — so
/// the partition stays independent of scheduling. Sized from the
/// measured inflation curve on Init (drift vs one-cold-claim re-priced
/// costs: K=16 +11.6%, K=64 +3.7%, K=128 +0.9%): at 128 the running
/// readout is within the cut's ε margin, so it serves directly as the
/// manifest cost.
const SCAN_BATCH_BLOCKS: usize = 128;

/// Smallest useful per-worker record share, GiB. Typical segments at any
/// realistic cut carry 3–8 GiB of record (measured 4–10% of the combined
/// cut across envs), so a share at this floor still lets normal segments
/// reach their cut untouched.
const MIN_WORKER_SHARE_GIB: f64 = 8.0;

/// Joint worker-count / record-share arithmetic: the fleet plans against
/// `RAM_CEILING_FRAC × box − 10` (decode cache, witness maps, claim
/// trees), split evenly across workers. The share is a PLAN, not an
/// enforced cap — Aiur execution carries no RAM instrumentation, so a
/// worker's record is bounded only at claim boundaries (segments drop
/// records); pathologically dense single claims can exceed the share,
/// and the recourse is fewer workers (`--workers 1` plans the whole
/// allowance). `IX_SCAN_WORKER_SHARE_GIB` overrides for tests. Returns
/// `(workers, share_gib)`.
fn fleet_plan(workers: usize, cut_used_gib: f64) -> (usize, f64) {
  let cores = std::thread::available_parallelism().map_or(4, usize::from);
  let ram = crate::kernel::system_ram_gib().unwrap_or(64.0);
  let usable = ram.mul_add(RAM_CEILING_FRAC, -10.0).max(MIN_WORKER_SHARE_GIB);
  let workers = if workers == 0 {
    let by_ram = format!("{:.0}", (usable / MIN_WORKER_SHARE_GIB).floor())
      .parse::<usize>()
      .unwrap_or(1)
      .max(1);
    cores.saturating_sub(2).max(1).min(by_ram)
  } else {
    workers
  };
  let share_gib = std::env::var("IX_SCAN_WORKER_SHARE_GIB")
    .ok()
    .and_then(|v| v.parse::<f64>().ok())
    .unwrap_or_else(|| (usable / f64_from_usize(workers)).min(cut_used_gib));
  (workers, share_gib)
}

/// The min-cut schedule order, truncated by the `IX_SCAN_LIMIT_BLOCKS`
/// debug knob (a full-pipeline reproducer over a slice of a huge env,
/// without extracting one; the result then does NOT cover the env).
fn ordered_schedule(
  blocks: &[SchedBlock],
  adj: &[Vec<u32>],
  n_chunks: usize,
) -> Vec<u32> {
  let mut order = static_order(blocks, adj, n_chunks.max(16));
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

/// Equal-byte contiguous chunks over the order; edges are forced segment
/// boundaries (the parallelism unit); the scan's merge pass repairs the
/// resulting fragmentation, so chunk count is a pure parallelism knob.
fn make_chunks(
  order: &[u32],
  blocks: &[SchedBlock],
  env_bytes: u64,
  n_chunks: usize,
) -> Vec<Vec<u32>> {
  let per_chunk = (env_bytes / n_chunks as u64).max(1);
  let mut chunks: Vec<Vec<u32>> = Vec::new();
  let mut cur: Vec<u32> = Vec::new();
  let mut acc = 0u64;
  for &b in order {
    cur.push(b);
    acc += blocks[b as usize].size;
    if acc >= per_chunk && chunks.len() + 1 < n_chunks {
      chunks.push(std::mem::take(&mut cur));
      acc = 0;
    }
  }
  if !cur.is_empty() {
    chunks.push(cur);
  }
  // Baseline before any execution: the schedule pass decoded every
  // constant into the shared env's lazy cache, so this RSS is (cache +
  // static structures) — the floor the worker footprints sit on.
  eprintln!("[scan] post-schedule baseline rss {:.0}G", process_rss_gib());
  chunks
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
            Ok((segs, rest)) => {
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
) -> Result<String, String> {
  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  let env_bytes: u64 = blocks.iter().map(|b| b.size).sum();
  let (workers, share_gib) = fleet_plan(workers, f64::INFINITY);
  let batch_blocks = std::env::var("IX_SCAN_BATCH_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .filter(|&k| k >= 1)
    .unwrap_or(SCAN_BATCH_BLOCKS);
  let n_chunks = (workers * 2).min(blocks.len());
  eprintln!(
    "[exec] {} blocks, {workers} workers over {n_chunks} chunks, \
     {share_gib:.1} GiB record share per worker (planned), {batch_blocks} \
     blocks per claim",
    blocks.len()
  );
  let order = ordered_schedule(&blocks, &adj, n_chunks);
  let covered = order.len();
  let chunks = make_chunks(&order, &blocks, env_bytes, n_chunks);
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let abort = std::sync::atomic::AtomicBool::new(false);
  let ctx = ScanCtx {
    toplevel,
    fun_idx,
    env,
    blocks: &blocks,
    cut_used_gib: share_gib,
    n_chunks: chunks.len(),
    fail_fast,
    failed: &failed,
    abort: &abort,
    batch_blocks,
    exec_only: true,
  };
  let segments = run_pool(&ctx, chunks, workers)?;
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
pub fn scan_shards(
  toplevel: &Toplevel,
  fun_idx: usize,
  env: &Arc<IxonEnv>,
  budget_gib: f64,
  eps: f64,
  workers: usize,
  fail_fast: bool,
  out_path: &str,
) -> Result<String, String> {
  let cap_gib = budget_gib * AIUR_RAM_USABLE_FRAC;
  if cap_gib <= AIUR_RAM_BASE_GIB {
    return Err(format!(
      "budget {budget_gib} GiB leaves no headroom over the {AIUR_RAM_BASE_GIB} GiB base"
    ));
  }
  // The ε-discounted headroom above the prove base, in GiB. The cut
  // charges BOTH resource terms against it: slope·fft (trace/FFT RAM)
  // plus the measured record bytes the prove's execute replays into.
  let cut_used_gib = (cap_gib - AIUR_RAM_BASE_GIB) * (1.0 - eps);
  // FFT-equivalent of the headroom, for the worker autoscale estimate.
  let cut_fft = cut_used_gib / AIUR_RAM_GIB_PER_BFFT * 1e9;

  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  let env_bytes: u64 = blocks.iter().map(|b| b.size).sum();
  let (workers, seg_budget_gib) = fleet_plan(workers, cut_used_gib);
  let batch_blocks = std::env::var("IX_SCAN_BATCH_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    .filter(|&k| k >= 1)
    .unwrap_or(SCAN_BATCH_BLOCKS);
  let n_chunks = (workers * 2).min(blocks.len());
  eprintln!(
    "[scan] {} blocks, {workers} workers over {n_chunks} chunks, cut {:.1} \
     GiB combined (≈{:.1} BFFT fft-only), {seg_budget_gib:.1} GiB record \
     share per worker (planned), {batch_blocks} blocks per claim",
    blocks.len(),
    cut_used_gib,
    cut_fft / 1e9
  );
  let order = ordered_schedule(&blocks, &adj, n_chunks);
  let chunks = make_chunks(&order, &blocks, env_bytes, n_chunks);
  let chunk_count = chunks.len();
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
    exec_only: false,
  };
  let segments = run_pool(&ctx, chunks, workers)?;

  // Merge + re-measure to a fixpoint. Merging by FFT sum is always safe
  // (the union's real cost is ≤ the sum: shared deps derive once) but the
  // sum badly overstates a shard assembled from many cold mini-segments —
  // each paid its own frontier unfolding. So every merged shard is
  // re-measured with ONE cold thin-frontier CheckEnv (exactly the claim
  // proving pays), and merging reruns with true costs until nothing
  // merges. This is what lets the chunk count scale with workers without
  // fragmenting the pack or corrupting the cost sidecar.
  let pre_merge = segments.len();
  // Batched claims keep the running readout within a couple percent of
  // the cold cost (per-claim overhead divided by the batch size), so
  // only MERGED shards need a re-measure — their summed costs are the
  // one remaining conservative estimate.
  let mut list: Vec<(Segment, bool)> =
    segments.into_iter().map(|s| (s, false)).collect();
  for round in 0usize.. {
    let used =
      |sg: &Segment| AIUR_RAM_GIB_PER_BFFT * sg.fft / 1e9 + sg.bytes_gib;
    let mut merged: Vec<(Segment, bool)> = Vec::new();
    for (seg, dirty) in list {
      match merged.last_mut() {
        Some((prev, prev_dirty)) if used(prev) + used(&seg) < cut_used_gib => {
          prev.blocks.extend(seg.blocks);
          prev.fft += seg.fft;
          prev.bytes_gib += seg.bytes_gib;
          *prev_dirty = true;
        },
        _ => merged.push((seg, dirty)),
      }
    }
    list = merged;
    let dirty_idx: Vec<usize> = list
      .iter()
      .enumerate()
      .filter_map(|(i, (_, d))| d.then_some(i))
      .collect();
    if dirty_idx.is_empty() {
      break;
    }
    if round >= 3 {
      // Leftover sums are conservative (over-budget never happens); stop
      // refining rather than loop on a pathological pack.
      eprintln!(
        "[scan] {} shard(s) keep conservative summed costs after {round} \
         refine rounds",
        dirty_idx.len()
      );
      break;
    }
    eprintln!(
      "[scan] refine round {round}: re-measuring {} merged shard(s)",
      dirty_idx.len()
    );
    let re_cursor = AtomicUsize::new(0);
    let re_results: Mutex<Vec<Option<Result<(f64, f64), String>>>> =
      Mutex::new((0..dirty_idx.len()).map(|_| None).collect());
    std::thread::scope(|s| {
      for _ in 0..workers.min(dirty_idx.len()) {
        s.spawn(|| {
          loop {
            let j = re_cursor.fetch_add(1, Ordering::Relaxed);
            if j >= dirty_idx.len() {
              break;
            }
            let out = measure_shard(&ctx, &list[dirty_idx[j]].0.blocks);
            re_results.lock().unwrap()[j] = Some(out);
          }
        });
      }
    });
    for (j, slot) in re_results.into_inner().unwrap().into_iter().enumerate() {
      let (seg, dirty) = &mut list[dirty_idx[j]];
      match slot {
        Some(Ok((fft, bytes_gib))) => {
          seg.fft = fft;
          seg.bytes_gib = bytes_gib;
        },
        Some(Err(e)) if !fail_fast => {
          // The conservative fft SUM stands for this shard.
          eprintln!(
            "[scan] re-measure of shard {j} failed ({e}); keeping \
             the summed cost"
          );
        },
        Some(Err(e)) => return Err(format!("re-measure shard {j}: {e}")),
        None => return Err(format!("re-measure shard {j}: never ran")),
      }
      *dirty = false;
    }
  }
  let segments: Vec<Segment> = list.into_iter().map(|(s, _)| s).collect();

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
    let ram = aiur_ram_gib_for_fft(seg.fft) + seg.bytes_gib;
    csv.push_str(&format!(
      "{},{},0,0,0,0,0,0,{:.2},{:.2}\n",
      id,
      own,
      ram,
      aiur_prove_secs_for_fft(seg.fft),
    ));
    max_ram = max_ram.max(ram);
    let used = AIUR_RAM_GIB_PER_BFFT * seg.fft / 1e9 + seg.bytes_gib;
    if used >= cut_used_gib / (1.0 - eps) {
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
     predicted prove RSS {max_ram:.1} GiB (fft line + measured record \
     bytes){note}",
    blocks.len(),
    chunk_count,
    cut_used_gib,
    eps * 100.0,
  ))
}

/// Measure one shard's true cold cost: a single thin-frontier `CheckEnv`
/// over its blocks against a fresh record and lazily-faulted witness —
/// the exact execution a prove of this shard performs.
fn measure_shard(
  ctx: &ScanCtx<'_>,
  block_ids: &[u32],
) -> Result<(f64, f64), String> {
  let owned: Vec<Address> =
    block_ids.iter().map(|&b| ctx.blocks[b as usize].addr.clone()).collect();
  let mut record = QueryRecord::new(ctx.toplevel);
  let mut io = IOBuffer::with_backing(EnvFaultSource::new(ctx.env.clone()));
  let (_claim, input) = seed_shard_check_env_claim(ctx.env, &owned, &mut io)?;
  execute_ixvm_with_record(
    ctx.toplevel,
    ctx.fun_idx,
    &input,
    &mut io,
    &mut record,
  )
  .map_err(|e| format!("re-measure CheckEnv failed: {e}"))?;
  Ok((
    record_fft_cost(ctx.toplevel, &record),
    f64_from_usize(record_retained_bytes(&record)) / GIB,
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
) -> Result<(Vec<Segment>, Vec<u32>), String> {
  let t0 = std::time::Instant::now();
  let chunk_id = origin;
  let n_chunks = ctx.n_chunks;
  let mut segments: Vec<Segment> = Vec::new();
  let mut lo = 0usize;
  // Blocks below this index (and at/after `lo`) execute one per claim:
  // a batch-level event landed in [lo, narrow_until) and needs per-block
  // attribution. Stale values (< hi) are inert.
  let mut narrow_until = 0usize;
  while lo < chunk.len() && segments.len() < RANGE_SEGMENTS {
    let mut record = QueryRecord::new(ctx.toplevel);
    let mut io = IOBuffer::with_backing(EnvFaultSource::new(ctx.env.clone()));
    let mut prev_fft = 0.0f64;
    let mut prev_bytes = 0.0f64;
    let mut hi = lo;
    let mut skip_failed = false;
    let (seg_end, seg_fft, seg_bytes) = loop {
      if hi >= chunk.len() {
        break (hi, prev_fft, prev_bytes);
      }
      if ctx.abort.load(Ordering::Acquire) {
        return Err("aborted after a failure elsewhere".to_string());
      }
      let k = if hi < narrow_until {
        1
      } else {
        ctx.batch_blocks.min(chunk.len() - hi)
      };
      let addrs: Vec<Address> = chunk[hi..hi + k]
        .iter()
        .map(|&b| ctx.blocks[b as usize].addr.clone())
        .collect();
      let out: Result<(), String> =
        seed_shard_check_env_claim(ctx.env, &addrs, &mut io).and_then(
          |(_claim, input)| {
            execute_ixvm_with_record(
              ctx.toplevel,
              ctx.fun_idx,
              &input,
              &mut io,
              &mut record,
            )
            .map(|_| ())
            .map_err(|e| e.to_string())
          },
        );
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
          break (hi, prev_fft, prev_bytes);
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
        break (hi, prev_fft, prev_bytes);
      }
      let fft = record_fft_cost(ctx.toplevel, &record);
      let bytes_gib = f64_from_usize(record_retained_bytes(&record)) / GIB;
      // Execute-only segments exist to bound the live record, so only
      // bytes count against the (per-worker share) cut; the scan's cut
      // charges both prove resources against the budget headroom.
      let used = if ctx.exec_only {
        bytes_gib
      } else {
        AIUR_RAM_GIB_PER_BFFT * fft / 1e9 + bytes_gib
      };
      if used >= ctx.cut_used_gib {
        if hi == lo {
          if k > 1 {
            // The segment's first batch crosses the whole cut: find the
            // culprit at per-block granularity before emitting anything.
            eprintln!(
              "[scan {chunk_id}/{n_chunks}] narrowing batch at block \
               {hi}: first claim crossed the cut"
            );
            narrow_until = hi + k;
            break (hi, prev_fft, prev_bytes);
          }
          // A single block alone reaches the cut: atomically infeasible
          // at this budget — emitted alone with its measured cost.
          break (hi + 1, fft, bytes_gib);
        }
        break (hi, prev_fft, prev_bytes);
      }
      hi += k;
      prev_fft = fft;
      prev_bytes = bytes_gib;
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
        "[scan {chunk_id}/{n_chunks}] segment: {} blocks, {:.2} BFFT + \
         {:.1}G rec, {}/{} blocks done, {:.0}s, rss {:.0}G, arena {}M, \
         iomap {}k, rec {}M",
        seg_end - lo,
        seg_fft / 1e9,
        seg_bytes,
        seg_end,
        chunk.len(),
        t0.elapsed().as_secs_f64(),
        process_rss_gib(),
        arena_g / 1_000_000,
        io.map.len() / 1000,
        rec_e / 1_000_000
      );
      segments.push(Segment {
        blocks: chunk[lo..seg_end].to_vec(),
        fft: seg_fft,
        bytes_gib: seg_bytes,
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
  Ok((segments, chunk[lo..].to_vec()))
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
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
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
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let budget = budget_gib.to_string().parse::<f64>().unwrap_or(0.0);
  if budget <= 0.0 {
    return LeanExcept::error_string("scan: pass a positive RAM budget (GiB)");
  }
  let eps = eps_pct.to_string().parse::<f64>().unwrap_or(5.0) / 100.0;
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let fail_fast = fail_fast.to_string() != "0";
  match scan_shards(
    &toplevel,
    fun_idx,
    &env_handle.get().env,
    budget,
    eps,
    workers,
    fail_fast,
    &out_path.to_string(),
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
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let fail_fast = fail_fast.to_string() != "0";
  match execute_env(&toplevel, fun_idx, &env_handle.get().env, workers, fail_fast)
  {
    Ok(report) => {
      eprintln!("[rs_exec]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => LeanExcept::error_string(&format!("rs_aiur_execute_env: {e}")),
  }
}
