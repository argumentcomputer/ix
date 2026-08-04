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
//! thin-frontier `CheckEnv` over a prefix of the schedule. Each segment
//! grows its owned prefix adaptively — execute `CheckEnv[lo..lo+k]` against
//! a shared `QueryRecord`, checkpoint the FFT, grow `k` while under the
//! cut — so every constant is checked once per segment and dependencies
//! stop at the assumed frontier. (Per-constant `Check{assumptions: None}`
//! claims are NOT usable here: without a frontier the kernel checks the
//! constant's whole dependency closure, which measures 100-1000× the real
//! per-block shard cost and rederives the env spine per segment.) The
//! grown record over-counts slightly — each growth step re-walks its
//! claim's owned/assumption trees, and members assumed at step `i` may be
//! checked at step `i+1` — so the checkpoint is a mild upper bound on the
//! emitted shard's cold cost: the safe direction for packing.
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
    ExecError, IOBuffer, QueryRecord, dump_query_stats, f64_from_usize,
    query_stats_enabled, record_fft_cost, record_retained_bytes,
    set_record_byte_budget,
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

/// GiB → bytes for budget caps, via the same lossless decimal
/// round-trip as [`cost_fft`] (no `as` cast): budgets are small positive
/// magnitudes, exact to the byte at every realistic scale.
fn gib_to_bytes(gib: f64) -> usize {
  format!("{:.0}", (gib * GIB).max(0.0)).parse().unwrap_or(usize::MAX)
}

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
  /// Per-worker segment-record byte cap, enforced INSIDE block execution
  /// via the aiur thread-local budget: a worker's live record can never
  /// exceed it, so the fleet's RAM is bounded by `workers × cap` by
  /// construction — including through dense regions where a single block
  /// grows its record by tens of GiB with no boundary to act on. A block
  /// that crosses the cap alone is skipped and named, like a
  /// kernel-rejected block: its record alone out-sizes a per-worker share
  /// of this box, which at measured byte-per-fft ratios puts its prove
  /// far beyond any single-shard budget. (`--workers 1` grants one worker
  /// the whole allowance when such a block must be measured anyway.)
  seg_byte_budget: usize,
}

/// Smallest useful per-worker record cap, GiB. Typical segments at any
/// realistic cut carry 3–8 GiB of record (measured 4–10% of the combined
/// cut across envs), so a cap at this floor still lets normal segments
/// reach their cut untouched.
const MIN_WORKER_CAP_GIB: f64 = 8.0;

/// Joint worker-count / record-cap arithmetic: the fleet plans against
/// `RAM_CEILING_FRAC × box − 10` (decode cache, witness maps, claim
/// trees), workers split it evenly, and each worker's share IS its
/// enforced record cap — the fleet bound is `workers × cap` by
/// construction, no reactive control. Fewer workers means a bigger cap
/// (`--workers 1` grants the whole allowance). Returns `(workers,
/// cap_gib)`; `IX_SCAN_SEG_BYTE_BUDGET_GIB` overrides the cap for tests.
fn fleet_plan(workers: usize, cut_used_gib: f64) -> (usize, f64) {
  let cores = std::thread::available_parallelism().map_or(4, usize::from);
  let ram = crate::kernel::system_ram_gib().unwrap_or(64.0);
  let usable = ram.mul_add(RAM_CEILING_FRAC, -10.0).max(MIN_WORKER_CAP_GIB);
  let workers = if workers == 0 {
    let by_ram = format!("{:.0}", (usable / MIN_WORKER_CAP_GIB).floor())
      .parse::<usize>()
      .unwrap_or(1)
      .max(1);
    cores.saturating_sub(2).max(1).min(by_ram)
  } else {
    workers
  };
  let cap_gib = std::env::var("IX_SCAN_SEG_BYTE_BUDGET_GIB")
    .ok()
    .and_then(|v| v.parse::<f64>().ok())
    .unwrap_or_else(|| (usable / f64_from_usize(workers)).min(cut_used_gib));
  (workers, cap_gib)
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
  let n_chunks = (workers * 2).min(blocks.len());
  eprintln!(
    "[scan] {} blocks, {workers} workers over {n_chunks} chunks, cut {:.1} \
     GiB combined (≈{:.1} BFFT fft-only), {seg_budget_gib:.1} GiB record \
     cap per worker",
    blocks.len(),
    cut_used_gib,
    cut_fft / 1e9
  );
  let mut order = static_order(&blocks, &adj, n_chunks.max(16));
  // Debug knob: truncate the schedule to its first N blocks — a
  // full-pipeline reproducer over a slice of a huge env, without
  // extracting one. The manifest then does NOT cover the env.
  if let Some(limit) = std::env::var("IX_SCAN_LIMIT_BLOCKS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
    && limit < order.len()
  {
    eprintln!(
      "[scan] IX_SCAN_LIMIT_BLOCKS={limit}: scanning a schedule PREFIX — \
       the manifest will not cover the env"
    );
    order.truncate(limit);
  }

  // Equal-byte contiguous chunks over the order; edges are forced shard
  // boundaries (the parallelism unit); the merge pass below repairs the
  // resulting fragmentation, so chunk count is a pure parallelism knob.
  let per_chunk = (env_bytes / n_chunks as u64).max(1);
  let mut chunks: Vec<Vec<u32>> = Vec::new();
  let mut cur: Vec<u32> = Vec::new();
  let mut acc = 0u64;
  for &b in &order {
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

  // Work-stealing ranges: workers pull `(origin chunk, seq, hint, blocks)`
  // ranges off a shared deque; a range yields at most `RANGE_SEGMENTS`
  // segments, then re-queues its remainder for any idle worker. Dense
  // regions — where one equal-byte chunk can hold hours of sequential
  // measurement — therefore self-parallelize; the extra forced boundaries
  // this creates are repaired by the merge + re-measure pass like any
  // others. The split policy is count-based, not time- or RAM-based, so
  // the resulting partition does not depend on scheduling (governor sheds
  // under RAM pressure excepted — there, safety wins). Segments are
  // tagged `(origin, seq)` and sorted at the end, so the final order is
  // the schedule order.
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let abort = std::sync::atomic::AtomicBool::new(false);
  let ctx = ScanCtx {
    toplevel,
    fun_idx,
    env,
    blocks: &blocks,
    cut_used_gib,
    n_chunks: chunks.len(),
    fail_fast,
    failed: &failed,
    abort: &abort,
    seg_byte_budget: gib_to_bytes(seg_budget_gib),
  };
  type Range = (u32, u32, Vec<u32>);
  let queue: Mutex<std::collections::VecDeque<Range>> = Mutex::new(
    chunks
      .iter()
      .enumerate()
      .map(|(i, c)| {
        (u32::try_from(i).expect("chunk count fits u32"), 0u32, c.clone())
      })
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
          match scan_range(&ctx, &range, origin) {
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

  // Merge + re-measure to a fixpoint. Merging by FFT sum is always safe
  // (the union's real cost is ≤ the sum: shared deps derive once) but the
  // sum badly overstates a shard assembled from many cold mini-segments —
  // each paid its own frontier unfolding. So every merged shard is
  // re-measured with ONE cold thin-frontier CheckEnv (exactly the claim
  // proving pays), and merging reruns with true costs until nothing
  // merges. This is what lets the chunk count scale with workers without
  // fragmenting the pack or corrupting the cost sidecar.
  let pre_merge = segments.len();
  // EVERY segment starts dirty: the incremental scan's running readout
  // carries per-block claim inflation (env_walk re-runs per claim), so
  // each shard is re-priced once with the single cold thin-frontier
  // CheckEnv a prove of it actually executes. Merging then compares true
  // costs — without this, inflated sums block consolidation and the
  // sidecar over-states prove RSS. (Re-measures run `workers`-wide; a
  // shard's record is bounded by the cut, so the fleet bound holds.)
  let mut list: Vec<(Segment, bool)> =
    segments.into_iter().map(|s| (s, true)).collect();
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
    chunks.len(),
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

/// Scan one range: execute per-block thin-frontier `CheckEnv` claims
/// against a shared record and lazily-faulted witness, checkpointing the
/// running FFT after every block and cutting on the exact block boundary
/// where it reaches the cut (the crossing block re-executes as the next
/// segment's first block, so an emitted shard never exceeds the cut —
/// except a single atomically-infeasible block, emitted alone with its
/// measured cost). One claim per block costs ~1ms of plumbing (measured)
/// plus a small per-block assumption-tree inflation that only steers cut
/// placement — the merge + re-measure pass re-prices every shard with
/// ONE real claim — and in exchange the scan is preemptible at BLOCK
/// granularity: no growth attempts, no overshoot re-execution, no cold
/// restarts, and RAM shedding or work-stealing acts between any two
/// blocks instead of stalling behind a multi-minute claim execution.
/// Emits at most [`RANGE_SEGMENTS`] segments, then returns the remaining
/// blocks for any idle worker.
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
  while lo < chunk.len() && segments.len() < RANGE_SEGMENTS {
    let mut record = QueryRecord::new(ctx.toplevel);
    // Arm the per-worker record cap for this fresh record. Worker threads
    // run nothing but scan ranges, and arming resets the charge counter,
    // so per-segment arming with no disarm is sufficient.
    set_record_byte_budget(ctx.seg_byte_budget);
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
      let addr = ctx.blocks[chunk[hi] as usize].addr.clone();
      // `Err(None)` = the record cap tripped mid-block (not a kernel
      // verdict); `Err(Some(e))` = the kernel rejected the block.
      let out: Result<(), Option<String>> = seed_shard_check_env_claim(
        ctx.env,
        std::slice::from_ref(&addr),
        &mut io,
      )
      .map_err(Some)
      .and_then(|(_claim, input)| {
        execute_ixvm_with_record(
          ctx.toplevel,
          ctx.fun_idx,
          &input,
          &mut io,
          &mut record,
        )
        .map(|_| ())
        .map_err(|e| match e {
          ExecError::RecordBudgetExceeded => None,
          other => Some(other.to_string()),
        })
      });
      // A cap trip on a segment that already holds blocks is an early
      // cut, not a failure: cut at the previous block; the crossing
      // block restarts the next segment with a fresh record and full
      // cap, and only counts as over-cap if it then trips ALONE.
      if matches!(out, Err(None)) && hi > lo {
        break (hi, prev_fft, prev_bytes);
      }
      if let Err(err) = out {
        let e = err.unwrap_or_else(|| {
          format!(
            "record bytes crossed the {:.1} GiB per-worker cap alone — \
             resource-infeasible at this box share (--workers 1 grants \
             the whole allowance)",
            f64_from_usize(ctx.seg_byte_budget) / GIB
          )
        });
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
        ctx.failed.lock().unwrap().push((addr, e));
        skip_failed = true;
        break (hi, prev_fft, prev_bytes);
      }
      let fft = record_fft_cost(ctx.toplevel, &record);
      let bytes_gib = f64_from_usize(record_retained_bytes(&record)) / GIB;
      let used = AIUR_RAM_GIB_PER_BFFT * fft / 1e9 + bytes_gib;
      if used >= ctx.cut_used_gib {
        if hi == lo {
          // A single block alone reaches the cut: atomically infeasible
          // at this budget — emitted alone with its measured cost.
          break (hi + 1, fft, bytes_gib);
        }
        break (hi, prev_fft, prev_bytes);
      }
      hi += 1;
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
