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
    query_stats_enabled, record_fft_cost, record_retained_bytes,
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
/// the partition stays independent of scheduling. Sized from the
/// measured inflation curve on Init (drift vs one-cold-claim re-priced
/// costs: K=16 +11.6%, K=64 +3.7%, K=128 +0.9%): at 128 the running
/// readout is within the cut's ε margin, so it serves directly as the
/// manifest cost.
const SCAN_BATCH_BLOCKS: usize = 128;

/// A worker child's non-record residency: lazily-decoded env cache,
/// compiled system, runtime. Reserved under the cap so the soft cut
/// bounds the record and the cap only fires on mid-claim growth.
const WORKER_OVERHEAD_GIB: f64 = 4.0;

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
    if acc >= per_chunk && bounds.len() + 1 < n_chunks {
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

/// The scan worker's stdin/stdout loop: a child process spawned by the
/// process pool, deterministically re-deriving the same schedule as its
/// parent and executing order-index ranges on command. Line protocol
/// (one command per stdin line, replies on stdout):
///
/// - `SCAN <lo> <hi>` — scan `order[lo..hi)` exactly like a thread
///   worker's range: up to [`RANGE_SEGMENTS`] segments, then hand the
///   remainder back. Replies: `SEG <lo> <hi> <fft> <ram_gib>` per
///   emitted segment (absolute order indices), `SKIP <addr-hex>
///   <msg-hex>` per kernel-rejected block, then `END <next>` (`next ==
///   hi` when the range is exhausted). A unit range (`hi == lo+1`)
///   degenerates to a single-block claim — the parent narrows a dying
///   batch by sending unit ranges, no dedicated verb needed.
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
) -> Result<(), String> {
  use std::io::{BufRead, Write};
  let toplevel = system.toplevel();
  let (blocks, adj) = schedule_blocks(env);
  let order = ordered_schedule(&blocks, &adj, pieces);
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let abort = std::sync::atomic::AtomicBool::new(false);
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
    let (Some(lo), Some(hi)) = (lo, hi) else {
      return Err(format!("worker: malformed command {line:?}"));
    };
    if hi > order.len() || lo >= hi {
      return Err(format!("worker: range {lo}..{hi} out of bounds"));
    }
    match verb {
      "SCAN" => {
        let range = &order[lo..hi];
        let (segs, rest) =
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
        writeln!(out, "END {}", hi - rest.len()).map_err(|e| e.to_string())?;
      },
      _ => return Err(format!("worker: unknown verb {verb:?}")),
    }
    out.flush().map_err(|e| e.to_string())?;
  }
  Ok(())
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

/// Per-run cgroup-v2 management under the user-delegated subtree. Every
/// worker gets its own leaf with `memory.max` (the hard cap) and
/// `memory.oom.group=1` (an over-cap worker dies whole, never
/// half-alive). Best-effort: `None` anywhere means caps are unavailable
/// (no delegation) and the pool runs uncapped with a warning.
struct CgroupBase {
  dir: std::path::PathBuf,
}

impl CgroupBase {
  fn create() -> Option<Self> {
    let uid = std::fs::read_to_string("/proc/self/status")
      .ok()?
      .lines()
      .find_map(|l| l.strip_prefix("Uid:"))?
      .split_whitespace()
      .next()?
      .to_string();
    let dir = std::path::PathBuf::from(format!(
      "/sys/fs/cgroup/user.slice/user-{uid}.slice/user@{uid}.service/ix-scan-{}",
      std::process::id()
    ));
    std::fs::create_dir(&dir).ok()?;
    Some(Self { dir })
  }

  fn child(&self, name: &str, cap_bytes: u64) -> Option<std::path::PathBuf> {
    let d = self.dir.join(name);
    // A respawned worker reuses its slot's cgroup: tolerate the existing
    // dir and rewrite the cap, so replacements stay capped.
    match std::fs::create_dir(&d) {
      Ok(()) => {},
      Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {},
      Err(_) => return None,
    }
    std::fs::write(d.join("memory.max"), format!("{cap_bytes}")).ok()?;
    // Best-effort: kill the whole worker on OOM, not one thread.
    let _ = std::fs::write(d.join("memory.oom.group"), "1");
    Some(d)
  }

  fn attach(dir: &std::path::Path, pid: u32) -> bool {
    std::fs::write(dir.join("cgroup.procs"), format!("{pid}")).is_ok()
  }
}

impl Drop for CgroupBase {
  fn drop(&mut self) {
    if let Ok(entries) = std::fs::read_dir(&self.dir) {
      for e in entries.flatten() {
        let _ = std::fs::remove_dir(e.path());
      }
    }
    let _ = std::fs::remove_dir(&self.dir);
  }
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
  /// The whole pool as a cap — the BIG lane for retrying blocks that
  /// outgrow a slot's even share. Serialized by `big_lane`: at most one
  /// big worker exists, so `Σ slot caps + pool_cap` bounds worst-case
  /// fleet RAM only transiently and by design.
  pool_cap_bytes: u64,
  big_lane: Mutex<()>,
  cgroups: Option<CgroupBase>,
  order: &'a [u32],
  blocks: &'a [SchedBlock],
  fail_fast: bool,
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
}

impl ProcPool<'_> {
  fn spawn(&self, slot: usize) -> Result<WorkerHandle, String> {
    self.spawn_capped(slot, self.cap_bytes, &format!("w{slot}"))
  }

  fn spawn_capped(
    &self,
    slot: usize,
    cap_bytes: u64,
    cg_name: &str,
  ) -> Result<WorkerHandle, String> {
    use std::process::{Command, Stdio};
    let mut cmd = Command::new(&self.bin);
    cmd
      .arg("shard-worker")
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
    let mut child = cmd
      .spawn()
      .map_err(|e| format!("spawn worker {slot} ({}): {e}", self.bin))?;
    if let Some(cg) = &self.cgroups {
      match cg.child(cg_name, cap_bytes) {
        Some(dir) if CgroupBase::attach(&dir, child.id()) => {},
        _ => {
          eprintln!("[scan] worker {slot}: cgroup attach failed; UNCAPPED");
        },
      }
    }
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
    let mut reply = ScanReply { segs: Vec::new(), skips: Vec::new(), next: lo };
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
        _ => return Err(reply),
      }
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
/// `ix shard-worker` process under a cgroup memory cap — a worker whose
/// record outgrows its cap mid-claim is OOM-killed ALONE, and the parent
/// recovers: retry the remainder once (transient collisions), then
/// narrow the dying batch with unit ranges to name the exact block as
/// resource-infeasible-at-cap and scan on. The fleet's RAM bound is
/// `Σ caps`, enforced by the kernel, independent of content.
fn run_pool_procs(
  pool: &ProcPool<'_>,
  chunks: Vec<(usize, usize)>,
  workers: usize,
  failed: &Mutex<Vec<(Address, String)>>,
) -> Result<Vec<Segment>, String> {
  type Range = (u32, u32, usize, usize);
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
  let done: Mutex<Vec<((u32, u32), Vec<Segment>)>> = Mutex::new(Vec::new());
  let failure: Mutex<Option<String>> = Mutex::new(None);
  let abort = std::sync::atomic::AtomicBool::new(false);
  std::thread::scope(|s| {
    let (queue, in_flight, done, failure, abort) =
      (&queue, &in_flight, &done, &failure, &abort);
    for slot in 0..workers {
      s.spawn(move || {
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
        'work: loop {
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
          let mut cursor = lo;
          let mut retried_at: Option<usize> = None;
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
          while cursor < hi {
            if abort.load(Ordering::Acquire) {
              break 'work;
            }
            match pool.scan(&mut worker, cursor, hi) {
              Ok(reply) => {
                let Ok(next) = commit(reply, origin, seq) else {
                  abort.store(true, Ordering::Release);
                  break 'work;
                };
                if next < hi {
                  queue.lock().unwrap().push_back((origin, seq + 1, next, hi));
                }
                break;
              },
              Err(partial) => {
                let e = match commit(partial, origin, seq) {
                  Ok(n) => n,
                  Err(()) => {
                    abort.store(true, Ordering::Release);
                    break 'work;
                  },
                };
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
                      break 'work;
                    },
                  },
                )
                .reap();
                eprintln!(
                  "[scan] worker {slot} died ({status}) at index {e}; \
                   respawned"
                );
                if retried_at == Some(e) {
                  // Second death with zero progress: narrow one batch
                  // window with unit ranges to name the culprit.
                  let window = (e + pool.batch_blocks).min(hi);
                  let mut b = e;
                  while b < window {
                    match pool.scan(&mut worker, b, b + 1) {
                      Ok(reply) => {
                        if commit(reply, origin, seq).is_err() {
                          abort.store(true, Ordering::Release);
                          break 'work;
                        }
                      },
                      Err(partial) => {
                        let _ = commit(partial, origin, seq);
                        let addr =
                          pool.blocks[pool.order[b] as usize].addr.clone();
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
                              break 'work;
                            },
                          },
                        )
                        .reap();
                        // BIG-lane retry: one worker at a time gets the
                        // whole pool as its cap, so a block that is
                        // heavy-but-provable measures instead of being
                        // falsely excluded by its slot's even share.
                        let big_reply = {
                          let _lane = pool.big_lane.lock().unwrap();
                          pool
                            .spawn_capped(slot, pool.pool_cap_bytes, "big")
                            .ok()
                            .map(|mut big| {
                              let r = pool.scan(&mut big, b, b + 1);
                              big.reap();
                              r
                            })
                        };
                        match big_reply {
                          Some(Ok(reply)) => {
                            if commit(reply, origin, seq).is_err() {
                              abort.store(true, Ordering::Release);
                              break 'work;
                            }
                            eprintln!(
                              "[scan] block {} exceeded its slot cap \
                               ({status}) but measured on the big lane",
                              addr.hex()
                            );
                          },
                          other => {
                            if let Some(Err(partial2)) = other {
                              let _ = commit(partial2, origin, seq);
                            }
                            eprintln!(
                              "[scan] block {} exceeded the worker memory \
                               cap ({status}) and the big lane — \
                               resource-infeasible; skipped",
                              addr.hex()
                            );
                            failed.lock().unwrap().push((
                              addr,
                              format!(
                                "record outgrew the {:.1} GiB whole-pool \
                                 cap mid-claim (cgroup OOM-kill)",
                                f64_from_usize(
                                  usize::try_from(pool.pool_cap_bytes)
                                    .unwrap_or(usize::MAX)
                                ) / GIB
                              ),
                            ));
                          },
                        }
                      },
                    }
                    b += 1;
                  }
                  cursor = window;
                  retried_at = None;
                } else {
                  retried_at = Some(e);
                  cursor = e;
                }
              },
            }
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
  let ram = crate::kernel::system_ram_gib().unwrap_or(64.0);
  // Thread-mode record drop: each worker's even share of the measured
  // headroom — segments cut (and drop their record) when they reach it.
  let record_cut_gib = (ram.mul_add(0.85, -baseline_gib - 2.0)
    / f64_from_usize(workers))
  .clamp(4.0, 64.0);
  let n_chunks = (workers * 2).min(blocks.len());
  eprintln!(
    "[exec] {} blocks, {workers} workers over {n_chunks} chunks, record \
     drop at {record_cut_gib:.1} GiB, {batch_blocks} blocks per claim",
    blocks.len()
  );
  let bounds = make_chunk_bounds(&order, &blocks, env_bytes, n_chunks);
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
    soft_record_gib: f64::INFINITY,
  };
  let segments = match proc_workers {
    Some((bin, ixe)) => {
      // Fastest wall without OOM: execution has no prove-cut constraint
      // on segment size, so width goes to the core count and the cap is
      // whatever the pool affords per worker — smaller segments cost
      // only a few percent of cold-boundary work.
      let pool_gib = ram.mul_add(0.85, -baseline_gib - 2.0).max(8.0);
      let cap_gib = (pool_gib / f64_from_usize(workers)).clamp(6.0, 64.0);
      let soft_gib = (cap_gib - WORKER_OVERHEAD_GIB).max(cap_gib / 2.0);
      let cgroups = CgroupBase::create();
      if cgroups.is_none() {
        eprintln!(
          "[exec] cgroup delegation unavailable — workers run UNCAPPED"
        );
      }
      eprintln!(
        "[exec] process pool: {workers} workers, {cap_gib:.1} GiB cap \
         each{}",
        if cgroups.is_some() { " (cgroup memory.max)" } else { "" }
      );
      let pool = ProcPool {
        bin: bin.to_string(),
        ixe: ixe.to_string(),
        cut_used_gib: soft_gib,
        batch_blocks,
        soft_record_gib: soft_gib,
        pieces: sched_pieces,
        exec_only: true,
        cap_bytes: gib_to_bytes_u64(cap_gib),
        pool_cap_bytes: gib_to_bytes_u64(
          crate::kernel::system_ram_gib()
            .unwrap_or(64.0)
            .mul_add(0.85, -baseline_gib - 2.0)
            .max(8.0),
        ),
        big_lane: Mutex::new(()),
        cgroups,
        order: &order,
        blocks: &blocks,
        fail_fast,
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
  // Width-first sizing, uniform for every env and budget: full-core
  // width, and each worker's cap is its even share of the pool. Segments
  // cut at the additive soft ceiling below the cap, so the budget only
  // sets the MERGE target — scan wall never depends on the prove budget.
  // Content denser than the cap is a per-block event: the cgroup kill
  // names it, and the big-lane retry (whole-pool cap, serialized) rescues
  // blocks that are heavy but provable.
  let proc_cap_gib = proc_workers.map(|_| {
    let ram = crate::kernel::system_ram_gib().unwrap_or(64.0);
    let pool_gib = ram.mul_add(0.85, -baseline_gib - 2.0).max(8.0);
    std::env::var("IX_SCAN_WORKER_CAP_GIB")
      .ok()
      .and_then(|v| v.parse::<f64>().ok())
      .unwrap_or_else(|| (pool_gib / f64_from_usize(workers)).clamp(6.0, 64.0))
  });
  let n_chunks = (workers * 2).min(blocks.len());
  eprintln!(
    "[scan] {} blocks, {workers} workers over {n_chunks} chunks, cut at \
     {cut_used_gib:.1} GiB predicted prove RSS (margin \
     {:.0}%, ε pre-charged), {batch_blocks} blocks per claim",
    blocks.len(),
    (1.0 - PROVE_RAM_MARGIN) * 100.0
  );
  let bounds = make_chunk_bounds(&order, &blocks, env_bytes, n_chunks);
  let chunk_count = bounds.len();
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
    soft_record_gib: f64::INFINITY,
  };
  let segments = match proc_workers {
    Some((bin, ixe)) => {
      let cap_gib = proc_cap_gib.unwrap_or(16.0);
      let soft_gib = (cap_gib - WORKER_OVERHEAD_GIB).max(cap_gib / 2.0);
      let cgroups = CgroupBase::create();
      if cgroups.is_none() {
        eprintln!(
          "[scan] cgroup delegation unavailable — workers run UNCAPPED"
        );
      }
      eprintln!(
        "[scan] process pool: {workers} workers, {cap_gib:.1} GiB cap \
         each{}, soft record cut {soft_gib:.1} GiB",
        if cgroups.is_some() { " (cgroup memory.max)" } else { "" },
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
        pool_cap_bytes: gib_to_bytes_u64(
          crate::kernel::system_ram_gib()
            .unwrap_or(64.0)
            .mul_add(0.85, -baseline_gib - 2.0)
            .max(8.0),
        ),
        big_lane: Mutex::new(()),
        cgroups,
        order: &order,
        blocks: &blocks,
        fail_fast,
      };
      run_pool_procs(&pool, bounds, workers, &failed)?
    },
    None => {
      let chunks =
        bounds.iter().map(|&(lo, hi)| order[lo..hi].to_vec()).collect();
      run_pool(&ctx, chunks, workers)?
    },
  };

  // Assemble shards by summing adjacent segments up to the cut, to a
  // fixpoint. Sums are conservative for every cost in play: shared
  // dependencies derive once in the union, and padded heights are
  // subadditive — so a summed shard can only OVER-state its prove RSS,
  // never breach the budget. The conservatism (measured ~5-15% extra
  // shards vs a re-measured pack) is the price of planning wall time
  // never depending on the prove budget: segments are scanned at
  // RAM-optimal size and packing is pure arithmetic.
  let pre_merge = segments.len();
  let mut list = segments;
  loop {
    let mut merged: Vec<Segment> = Vec::new();
    let mut any = false;
    for seg in list {
      match merged.last_mut() {
        Some(prev) if prev.ram_gib + seg.ram_gib < cut_used_gib => {
          prev.blocks.extend(seg.blocks);
          prev.fft += seg.fft;
          prev.ram_gib += seg.ram_gib;
          any = true;
        },
        _ => merged.push(seg),
      }
    }
    list = merged;
    if !any {
      break;
    }
  }
  let segments = list;

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
      let k = if hi < narrow_until {
        1
      } else {
        ctx.batch_blocks.min(chunk.len() - hi)
      };
      let addrs: Vec<Address> = chunk[hi..hi + k]
        .iter()
        .map(|&b| ctx.blocks[b as usize].addr.clone())
        .collect();
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
      let rec_gib = f64_from_usize(record_retained_bytes(&record)) / GIB;
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
         iomap {}k, rec {}M",
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
        rec_e / 1_000_000
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
  let fail_fast = fail_fast.to_string() != "0";
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
  let exec_only = exec_only.to_string() == "1";
  match scan_worker(
    system.get(),
    fun_idx,
    &env_handle.get().env,
    cut,
    batch,
    soft,
    pieces,
    exec_only,
  ) {
    Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanExcept::error_string(&format!("rs_aiur_scan_worker: {e}")),
  }
}
