//! Whole-env execution over one shared `QueryRecord`, with record
//! cutting at a MEASURED threshold and direct segment proving.
//!
//! [`execute_env`] runs the env's whole check schedule through the
//! codegen'd circuit kernel: worker threads WARM-execute one
//! `verify_block` per schedule block into a single shared record —
//! per-block checking keyed by address alone, so every shared
//! dependency cone derives once, with the entry's phantom external
//! multiplicity debumped — and each sealed segment then runs ONE
//! `verify_segment` claim over the digest-bound list of its block
//! addresses, whose per-block calls memo-hit (and consume) the warm
//! work. The record balances exactly as if `verify_segment` executed
//! alone. The schedule is a min-cut linearization of the env's
//! reference graph, which keeps closure-overlapping blocks adjacent so
//! memoization absorbs shared work.
//!
//! Record cutting is deliberately SIMPLE: between blocks — the only
//! place a worker can stop — each worker measures the mode's budgeted
//! metric on the record as it stands (exec mode: retained bytes; prove
//! mode: the calibrated peak-prove-RSS model) and flags the cut when it
//! crosses the threshold. Nothing is predicted, projected,
//! or trimmed — segment sizing intentionally lives with the PROVER
//! (post-execution row sharding sizes chunks exactly from known
//! heights; see `docs/segment-sizing-design-space.md` D3), and these
//! coarse executor segments only bound record residency and enable
//! exec/prove pipelining. Sealed segments ARE prover witnesses: with a
//! prove system attached, each proceeds straight to a multi-claim
//! STARK ([`AiurSystem::prove_sealed`]) — no re-execution, no
//! manifest, no partition planning.
//!
//! Witness bytes are served lazily through the run-wide [`SharedIO`]
//! layer (`EnvFaultSource`): claim wires are seeded up front in
//! schedule order, constant/hint/blob bytes materialize into
//! env-canonical preassigned slots on first fault.
//!
//! What crosses a segment boundary: only re-derivation of the thin
//! long-range shared tail (the segment's claims are a contiguous
//! schedule range). Constants are order-independent obligations;
//! cross-segment soundness is per-claim, exactly as executed.

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

use crate::{aiur::toplevel::decode_toplevel, lean::LeanAiurToplevel};
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

/// Fraction of the budget that triggers a cut. The 20% below budget is
/// the design's ONLY slack, and it covers exactly what the metric
/// cannot see at the moment a worker decides to stop: the in-flight
/// block every worker still finishes during the drain (cuts land only
/// between blocks), and the record's hash-table index (a small adjunct
/// of the retained bytes the metric counts).
const CUT_FRAC: f64 = 0.8;

/// Plan-mode cut trigger, as a fraction of the budget. Fine segments
/// are measurement quanta, never proof units: the grouping pass packs
/// them into budget-sized shards, so their one requirement is to be
/// small enough to pack with — a quarter-budget quantum gives the
/// packer 4x resolution. A segment that still seals over budget is
/// flagged and bisected by the manifest fix-up.
const PLAN_TRIGGER_FRAC: f64 = 0.25;

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
  let mut order: Vec<u32> =
    (0..u32::try_from(blocks.len()).expect("block count exceeds u32"))
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

/// Whole-env check schedule through the codegen'd kernel in parallel.
/// `fun_idx` is `verify_segment` (the single per-segment claim run at
/// seal in prove mode), `block_fun_idx` is `verify_block` (the
/// per-block entry the workers warm-execute). Execute-only runs (`None`
/// prove system) skip the segment claims: segments exist only to drop
/// records at the cut threshold, and the report is the check verdict —
/// blocks checked, kernel rejects named, total measured FFT cost. With
/// a prove system, each sealed record proceeds straight to a verified
/// multi-claim STARK.
#[allow(clippy::too_many_arguments)]
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

/// The segment claim: ONE `verify_segment` execution over the digest
/// of the sorted block-address list, run into `record` — its per-block
/// calls memo-hit the warm work, so the claim costs the binding hash
/// plus one bump per block. Returns the claim input on success.
fn run_segment_claim(
  toplevel: &Toplevel,
  fun_idx: usize,
  shared_io: &Arc<aiur::execute::SharedIO>,
  record: &QueryRecord,
  mut addrs: Vec<Address>,
) -> Result<Vec<G>, String> {
  addrs.sort();
  let mut list_bytes: Vec<u8> = Vec::with_capacity(addrs.len() * 32);
  for a in &addrs {
    list_bytes.extend_from_slice(a.as_bytes());
  }
  let digest = Address::hash(&list_bytes);
  let input = addr_key(&digest);
  let mut io = IOBuffer::with_shared(shared_io.clone());
  io.seed(
    G::ZERO,
    input.clone(),
    list_bytes.iter().map(|b| G::from_u8(*b)).collect(),
  );
  execute_ixvm_with_record(toplevel, fun_idx, &input, &mut io, record)
    .map(|_| input)
    .map_err(|e| e.to_string())
}

pub fn execute_env(
  toplevel: &Toplevel,
  fun_idx: usize,
  block_fun_idx: usize,
  env: &Arc<IxonEnv>,
  workers: usize,
  fail_fast: bool,
  dry_run: bool,
  plan_out: Option<&str>,
  prove_system: Option<&AiurSystem>,
  roots: &[Address],
) -> Result<String, String> {
  if plan_out.is_some() && (!dry_run || prove_system.is_none()) {
    return Err("--plan-out requires --prove --dry-run".to_string());
  }
  // Threads sharing ONE QueryRecord: parallelism comes from concurrent
  // claims filling the same memo table. Every shared cone derives once
  // for the whole env, worker width defaults to the machine, and the
  // env decode cache exists once.
  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  // Default: all cores less one (the watcher).
  let workers = if workers == 0 {
    std::thread::available_parallelism()
      .map_or(4, usize::from)
      .saturating_sub(1)
      .max(1)
  } else {
    workers
  };
  // The schedule granularity is fixed by the core count so worker sizing
  // cannot change the block ordering.
  let sched_pieces =
    (std::thread::available_parallelism().map_or(4, usize::from) * 2)
      .min(blocks.len())
      .max(16);
  let order = ordered_schedule(&blocks, &adj, sched_pieces);
  // Closure-rooted execution: restrict the schedule to the blocks
  // reachable from the roots' home blocks over the reference adjacency.
  // Schedule order is preserved, so warm sharing and record cutting
  // behave exactly as a whole-env run over the smaller schedule.
  let order = if roots.is_empty() {
    order
  } else {
    let mut home: FxHashMap<&Address, u32> = FxHashMap::default();
    for (i, b) in blocks.iter().enumerate() {
      let i = u32::try_from(i).expect("block ids fit u32");
      home.insert(&b.addr, i);
      for m in &b.members {
        home.insert(m, i);
      }
    }
    let mut keep = vec![false; blocks.len()];
    let mut stack: Vec<u32> = Vec::new();
    for r in roots {
      let Some(&b) = home.get(r) else {
        return Err(format!("closure root {} not in env schedule", r.hex()));
      };
      if !keep[b as usize] {
        keep[b as usize] = true;
        stack.push(b);
      }
    }
    while let Some(b) = stack.pop() {
      for &r in &adj[b as usize] {
        if !keep[r as usize] {
          keep[r as usize] = true;
          stack.push(r);
        }
      }
    }
    let filtered: Vec<u32> =
      order.into_iter().filter(|&b| keep[b as usize]).collect();
    eprintln!(
      "[exec] closure of {} root(s): {}/{} blocks",
      roots.len(),
      filtered.len(),
      blocks.len()
    );
    filtered
  };
  let covered = order.len();
  // The budget feeds ONLY the cut thresholds and the plan/prove sizing
  // below; there is no RSS enforcement here — running under a watchdog
  // or cgroup is the caller's job.
  let budget_gib = measured_budget_gib()?;
  eprintln!(
    "[exec] {covered} blocks, {workers} threads over one shared record, \
     budget {budget_gib:.0} GiB"
  );
  let mut record = QueryRecord::new(toplevel);
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
  // Record cutting: workers free-run at full width while a watcher
  // polls the record; when the measured metric crosses the target the
  // workers drain their in-flight blocks and stop, the segment seals as
  // a complete self-contained QueryRecord — the witness input, exactly
  // what the prover consumes — and execution continues into a fresh
  // one. Cut points are timing-dependent and machine-local by design:
  // the same machine executes and proves, so segments only need to be
  // sized for its prover, not canonical across machines.
  //
  // One cut threshold, from the measured budget. Workers test it
  // between blocks (the only place a worker can stop) on the mode's own
  // metric — the quantity being budgeted, measured on real state, with
  // no polling gap: prove/plan use the calibrated peak-prove-RSS model,
  // execute-only the record's retained bytes.
  let cut_bytes: usize = usize::try_from(gib_to_bytes_u64(
    budget_gib * if plan_out.is_some() { PLAN_TRIGGER_FRAC } else { CUT_FRAC },
  ))
  .unwrap_or(usize::MAX);
  let cursor = AtomicUsize::new(0);
  let done = AtomicUsize::new(0);
  let abort = std::sync::atomic::AtomicBool::new(false);
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let fatal: Mutex<Option<String>> = Mutex::new(None);
  let t0 = std::time::Instant::now();
  // (seg_start, seg_end, unique entries, fft cost, retained bytes).
  let mut segs: Vec<(usize, usize, usize, f64, usize)> = Vec::new();
  // Plan mode: per fine segment, the measured per-circuit raw heights,
  // retained bytes, exact peak, and cleanliness — the grouping inputs.
  let mut plan_segs: Vec<(Vec<usize>, usize, usize, bool)> = Vec::new();
  // Prove-mode segments sealed unclean (rejects / missing claim) and
  // therefore not proven — a failure the exit status must carry.
  let mut unproven_segs = 0usize;
  let mut seg_start = 0usize;
  while seg_start < covered && !abort.load(Ordering::Acquire) {
    let cut_now = std::sync::atomic::AtomicBool::new(false);
    // Rejects are scoped to the span that contains them: a kernel
    // reject makes THIS segment unprovable (its claim would fail),
    // not the rest of the run. The global list only accumulates for
    // the end-of-run report.
    let seg_failed_base = failed.lock().unwrap().len();
    // Workers still executing this span; the watcher outlives the cut
    // and keeps polling until this hits zero.
    let active_workers = AtomicUsize::new(workers);
    // Per-worker in-flight block (u32::MAX = idle): lets the stall
    // detector NAME the stuck block(s) — the identity a runaway
    // diagnosis needs.
    let in_flight: Vec<AtomicUsize> =
      (0..workers).map(|_| AtomicUsize::new(usize::MAX)).collect();
    std::thread::scope(|sc| {
      {
        let (record, abort) = (&record, &abort);
        let active_workers = &active_workers;
        let done = &done;
        let (in_flight, blocks, order) = (&in_flight, &blocks, &order);
        sc.spawn(move || {
          // Stall detector: the FLT len-runaway ran 40+ minutes with
          // `done` frozen while system time exploded; this names that
          // state within a minute — a climbing open-reservation count
          // alongside a frozen frontier is the runaway signature.
          let mut stall = (usize::MAX, 0u32);
          loop {
            if abort.load(Ordering::Acquire) {
              break;
            }
            let drained = active_workers.load(Ordering::Acquire) == 0;
            let d = done.load(Ordering::Acquire);
            if d != stall.0 {
              stall = (d, 0);
            } else {
              stall.1 += 1;
              if stall.1.is_multiple_of(120) && !drained {
                // Name the top maps: a runaway execution shows up as
                // one map's length exploding — its function index is
                // the bug's address (IX_DUMP_FUN_NAMES resolves it).
                let mut tops: Vec<(usize, usize)> = record
                  .function_queries
                  .iter()
                  .enumerate()
                  .map(|(i, m)| (m.len(), i))
                  .collect();
                tops.sort_unstable_by(|a, b| b.cmp(a));
                let tops: Vec<String> = tops
                  .iter()
                  .take(14)
                  .map(|(l, i)| format!("fn {i}: {l}"))
                  .collect();
                let stuck: Vec<String> = in_flight
                  .iter()
                  .filter_map(|a| {
                    let lo = a.load(Ordering::Relaxed);
                    (lo != usize::MAX).then(|| {
                      format!(
                        "{}@{lo}",
                        blocks[order[lo] as usize].addr.hex()
                      )
                    })
                  })
                  .collect();
                eprintln!(
                  "[watch] STALL: no block completed in {}s; largest \
                   function maps: {}; in-flight: {}",
                  stall.1 / 2,
                  tops.join(", "),
                  stuck.join(" ")
                );
              }
            }
            if drained {
              break;
            }
            std::thread::sleep(std::time::Duration::from_millis(500));
          }
        });
      }
      for w in 0..workers {
        let in_flight = &in_flight;
        let (cursor, done, abort, cut_now) = (&cursor, &done, &abort, &cut_now);
        let (failed, fatal, active_workers) = (&failed, &fatal, &active_workers);
        let (blocks, order, shared_io) = (&blocks, &order, &shared_io);
        let record = &record;
        sc.spawn(move || {
          // WARM execution, one `verify_block` per schedule block: the
          // block's home constant goes through the same
          // shape-dispatched gauntlet the segment claim applies per
          // block, keyed by the address alone — every shared
          // dependency cone derives once for the whole record, and
          // the seal claim memo-hits all of it. The record is an
          // insert-once SET during execution; a warmed entry's
          // multiplicity (its one `verify_segment` consumer) is
          // DERIVED at seal, so no phantom-caller accounting exists.
          let run = |b: u32| -> Result<(), String> {
            let mut io = IOBuffer::with_shared(shared_io.clone());
            let input = addr_key(&blocks[b as usize].addr);
            execute_ixvm_with_record(
              toplevel, block_fun_idx, &input, &mut io, &record,
            )
            .map_err(|e| e.to_string())?;
            Ok(())
          };
          let reject = |b: u32, e: String| {
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
              failed.lock().unwrap().push((blocks[b as usize].addr.clone(), e));
            }
          };
          loop {
            if abort.load(Ordering::Acquire) || cut_now.load(Ordering::Acquire)
            {
              break;
            }
            let lo = cursor.fetch_add(1, Ordering::AcqRel);
            if lo >= covered {
              break;
            }
            in_flight[w].store(lo, Ordering::Relaxed);
            match run(order[lo]) {
              Ok(()) => {
                done.fetch_add(1, Ordering::AcqRel);
              },
              Err(e) => reject(order[lo], e),
            }
            in_flight[w].store(usize::MAX, Ordering::Relaxed);
            // Cut check, between blocks — the only place a worker can
            // stop, so checking here has zero detection gap beyond the
            // drain itself. Lock-free O(#maps): map lens are single
            // atomic loads.
            let bytes = match prove_system {
              Some(s) => s.peak_prove_bytes(record).peak,
              None => record_retained_bytes(record),
            };
            if bytes >= cut_bytes {
              cut_now.store(true, Ordering::Release);
            }
            let d = done.load(Ordering::Acquire);
            if d.is_multiple_of(8192) {
              eprintln!(
                "[exec] {d}/{covered} blocks, rss {:.0}G, {:.0}s",
                process_rss_gib(),
                t0.elapsed().as_secs_f64()
              );
            }
          }
          active_workers.fetch_sub(1, Ordering::AcqRel);
        });
      }
    });
    // Every grabbed block resolved (workers only break between
    // blocks), so the executed prefix is exactly the cursor, capped by
    // the schedule end; racing losers may have bumped it past without
    // executing those grabs.
    let seg_end = cursor.load(Ordering::Acquire).min(covered);
    cursor.store(seg_end, Ordering::Release);
    if abort.load(Ordering::Acquire) {
      break;
    }
    // Segment claim (prove mode): ONE `verify_segment` over the
    // digest-bound, sorted address list of every block the span
    // executed, run into the same record. Its per-block calls memo-hit
    // the warm executions, so the claim's whole cost is the binding
    // hash plus one bump per block — small and uniform.
    let mut seg_claim: Option<Vec<G>> = None;
    if prove_system.is_some()
      && seg_end > seg_start
      && failed.lock().unwrap().len() == seg_failed_base
    {
      let addrs: Vec<Address> = order[seg_start..seg_end]
        .iter()
        .map(|&b| blocks[b as usize].addr.clone())
        .collect();
      match run_segment_claim(toplevel, fun_idx, &shared_io, &record, addrs) {
        Ok(input) => seg_claim = Some(input),
        Err(e) => {
          eprintln!(
            "[prove seg {}] segment claim failed: {e} — the segment \
             will not be proven",
            segs.len()
          );
        },
      }
    }
    let retained = record_retained_bytes(&record);
    let entries: usize =
      record.function_queries.iter().map(|m| m.len()).sum::<usize>()
        + record.memory_queries.iter().map(|(_, m)| m.len()).sum::<usize>();
    let fft = record_fft_cost(toplevel, &record);
    // Padded transform work (prove mode): the raw BFFT is the smooth
    // cross-run diagnostic; the padded figure is what the prover's wall
    // actually tracks.
    let padded_note = prove_system
      .map(|s| {
        format!(" ({:.1} padded)", s.padded_fft_cost_of_record(&record) / 1e9)
      })
      .unwrap_or_default();
    if seg_end < covered || !segs.is_empty() {
      eprintln!(
        "[seg {}] blocks {seg_start}..{seg_end} of {covered}: \
         {entries} unique queries, {:.1}{padded_note} BFFT, {:.1} GiB \
         record, {:.0}s",
        segs.len(),
        fft / 1e9,
        f64_from_usize(retained) / GIB,
        t0.elapsed().as_secs_f64()
      );
    }
    segs.push((seg_start, seg_end, entries, fft, retained));
    if let Some(system) = prove_system {
      // The sealed record IS the witness, and the claim list is ONE
      // claim: `verify_segment` over the digest of the segment's
      // block-address list. The warmed per-block entries are consumed
      // by its in-circuit calls (debumped, never claimed), so the
      // record balances exactly as if `verify_segment` had executed
      // every block itself. A segment with rejected blocks or a
      // failed segment claim has partial or unconsumed work in its
      // record, so it is skipped rather than mis-proven.
      let mut claims: Vec<Vec<G>> = Vec::with_capacity(1);
      let mut missing = 0usize;
      match &seg_claim {
        Some(inp) => match record.function_queries[fun_idx].get(inp) {
          Some(q) => {
            claims
              .push(aiur::synthesis::function_claim(fun_idx, inp, q.output));
          },
          None => missing += 1,
        },
        None => missing += 1,
      }
      let clean =
        missing == 0 && failed.lock().unwrap().len() == seg_failed_base;
      // Seal accounting: the record was filled as an insert-once SET;
      // every multiplicity (function, memory, byte gadgets) is DERIVED
      // here from the unique-query set + the segment claim, then
      // written into the record for witness generation. This is the
      // step that makes duplicate speculative execution by racing
      // workers sound — nothing accumulated at runtime enters the
      // witness.
      // Plan mode measures only — the fine segments are never proven,
      // so multiplicity derivation (the seal's prove-side step) is
      // skipped; the grouped shards derive at THEIR seal in the prove
      // pass. The segment claim still ran above, so its rows are in
      // the measured raws — summing per-segment claims over-counts the
      // group's single claim, which is the conservative direction.
      if clean && plan_out.is_none() {
        let t = std::time::Instant::now();
        let dio = IOBuffer::with_shared(shared_io.clone());
        let claim_list: Vec<(usize, Vec<G>)> =
          seg_claim.iter().map(|inp| (fun_idx, inp.clone())).collect();
        aiur::trace::derive_multiplicities_into(
          toplevel,
          &record,
          &dio,
          &claim_list,
        );
        eprintln!(
          "[seg {}] multiplicities derived in {:.1}s",
          segs.len() - 1,
          t.elapsed().as_secs_f64()
        );
      }
      if let Some(system) = prove_system
        && plan_out.is_some()
      {
        plan_segs.push((
          system.circuit_raws(&record),
          aiur::execute::record_retained_bytes(&record),
          system.peak_prove_bytes(&record).peak,
          clean,
        ));
      }
      if !clean {
        eprintln!(
          "[prove seg {}] SKIPPED: {missing} unavailable claim(s) and/or \
           rejected blocks — partial records are not proven",
          segs.len() - 1
        );
        if !dry_run && plan_out.is_none() {
          unproven_segs += 1;
        }
        drop(std::mem::replace(&mut record, QueryRecord::new(toplevel)));
      } else if dry_run {
        // Geometry dry run: everything real — the cut, the segment
        // claim, claims assembly — except the STARK itself.
        let sealed = std::mem::replace(&mut record, QueryRecord::new(toplevel));
        let predicted = system.peak_prove_bytes(&sealed);
        eprintln!(
          "[prove seg {}] DRY: {} claims, predicted peak prove RSS \
           {:.1} GiB — STARK skipped",
          segs.len() - 1,
          claims.len(),
          f64_from_usize(predicted.peak) / GIB
        );
      } else {
        let sealed = std::mem::replace(&mut record, QueryRecord::new(toplevel));
        let predicted = system.peak_prove_bytes(&sealed);
        eprintln!(
          "[prove seg {}] predicted peak prove RSS {:.1} GiB",
          segs.len() - 1,
          f64_from_usize(predicted.peak) / GIB
        );
        let io = IOBuffer::with_shared(shared_io.clone());
        let pt = std::time::Instant::now();
        let proof = system.prove_sealed(sealed, &io, &claims);
        let prove_s = pt.elapsed().as_secs_f64();
        let vt = std::time::Instant::now();
        system
          .verify_sealed(&claims, &proof)
          .map_err(|e| format!("segment proof failed verification: {e:?}"))?;
        eprintln!(
          "[prove seg {}] {} claims: prove {:.0}s, verify {:.1}s, proof \
           {:.1} MiB, rss {:.0}G",
          segs.len() - 1,
          claims.len(),
          prove_s,
          vt.elapsed().as_secs_f64(),
          f64_from_usize(proof.to_bytes().map_or(0, |b| b.len()))
            / (1024.0 * 1024.0),
          process_rss_gib(),
        );
      }
    } else if seg_end < covered {
      // Fresh record for the next segment. The SharedIO persists: its
      // layout is env-canonical plus schedule-ordered claim seeds, so
      // every record couples to the same io coordinates and the io
      // outlives them all.
      record = QueryRecord::new(toplevel);
    }
    seg_start = seg_end;
  }
  if let Some(e) = fatal.into_inner().unwrap() {
    return Err(e);
  }
  // MEASURED-MANIFEST planning: group consecutive fine segments into
  // shard-sized proof units under the exact model's from-raws bound.
  // A shard is a union of segments; union heights are at most summed
  // heights per circuit (dedup only removes), and the model is
  // monotone in every height — so grouping while
  // `model(Σ measured heights) <= budget` GUARANTEES every emitted
  // shard proves under budget. Arithmetic on measured integers: no
  // prediction, no repair rounds, no way to emit an over-budget shard.
  // (Byte-gadget circuits have FIXED table heights, so they pin at
  // their constant instead of summing; per-segment claim rows over-
  // count the group's single claim — both in the conservative
  // direction.)
  if let Some(out) = plan_out {
    if covered != blocks.len() {
      return Err(
        "--plan-out requires the full schedule (no IX_SCAN window)".into(),
      );
    }
    let system = prove_system.expect("plan mode requires --prove");
    let budget_bytes: usize =
      usize::try_from(gib_to_bytes_u64(budget_gib)).unwrap_or(usize::MAX);
    assert_eq!(plan_segs.len(), segs.len(), "plan data per sealed segment");
    let n_circ = plan_segs.first().map_or(0, |p| p.0.len());
    // Bytes1 + Bytes2 sit last in canonical circuit order.
    let fixed_tail = 2usize;
    let bound = |raws: &[usize], rb: usize| -> usize {
      system.peak_prove_bytes_from_raws(raws, rb).peak
    };
    let mut groups: Vec<(usize, usize, usize, bool)> = Vec::new();
    let mut i = 0usize;
    while i < plan_segs.len() {
      if !plan_segs[i].3 {
        // Rejected segment: its own flagged shard (never provable).
        groups.push((i, i + 1, plan_segs[i].2, false));
        i += 1;
        continue;
      }
      let mut raws = plan_segs[i].0.clone();
      let mut rb = plan_segs[i].1;
      let mut j = i + 1;
      while j < plan_segs.len() && plan_segs[j].3 {
        let mut cand = raws.clone();
        for (k, v) in cand.iter_mut().enumerate() {
          if k + fixed_tail >= n_circ {
            *v = (*v).max(plan_segs[j].0[k]);
          } else {
            *v += plan_segs[j].0[k];
          }
        }
        let cand_rb = rb + plan_segs[j].1;
        if bound(&cand, cand_rb) > budget_bytes {
          break;
        }
        raws = cand;
        rb = cand_rb;
        j += 1;
      }
      groups.push((i, j, bound(&raws, rb), true));
      i = j;
    }
    // Manifest: one shard per group over the groups' contiguous block
    // ranges.
    let profile = {
      let mut b = ProfileBuilder::new();
      for blk in &blocks {
        let ops = OpCounts { intern_nodes: blk.size, ..OpCounts::default() };
        b.block(
          blk.addr.clone(),
          0,
          u32::try_from(blk.size).expect("block size exceeds u32"),
          u32::try_from(blk.members.len()).expect("member count exceeds u32"),
          ops,
        );
      }
      for (bi, row) in adj.iter().enumerate() {
        for &r in row {
          b.delta_edge(
            blocks[bi].addr.clone(),
            blocks[r as usize].addr.clone(),
          );
        }
      }
      b.finish()
    };
    let mut shard_of: Vec<u32> = vec![0; blocks.len()];
    for (gi, &(a, b, _, _)) in groups.iter().enumerate() {
      let lo = segs[a].0;
      let hi = segs[b - 1].1;
      for &blk in &order[lo..hi] {
        shard_of[blk as usize] =
          u32::try_from(gi).expect("group count fits u32");
      }
    }
    let manifest = ShardManifest::build(&profile, &shard_of, groups.len());
    std::fs::write(out, manifest.to_bytes())
      .map_err(|e| format!("{out}: {e}"))?;
    for (gi, &(a, b, bnd, clean)) in groups.iter().enumerate() {
      eprintln!(
        "[plan] shard {gi}: segments {a}..{b}, bound {:.1} GiB ({:.0}% of          budget){}",
        f64_from_usize(bnd) / GIB,
        100.0 * f64_from_usize(bnd) / f64_from_usize(budget_bytes),
        if clean { "" } else { " [REJECTED — not provable]" },
      );
    }
    let over =
      groups.iter().filter(|&&(_, _, b, c)| c && b > budget_bytes).count();
    eprintln!(
      "[plan] {} fine segment(s) -> {} shard(s), {} over budget, written        to {out}",
      plan_segs.len(),
      groups.len(),
      over
    );
  }
  // Differential determinism debugging: dump every map's unique count
  // so two runs can be diffed down to the exact functions whose keys
  // are layout-sensitive.
  if let Ok(path) = std::env::var("IX_EXEC_DUMP_COUNTS") {
    let mut out = String::new();
    for (i, m) in record.function_queries.iter().enumerate() {
      if !m.is_empty() {
        out.push_str(&format!("fn {i} {}\n", m.len()));
      }
    }
    for (w, m) in &record.memory_queries {
      out.push_str(&format!("mem {w} {}\n", m.len()));
    }
    let _ = std::fs::write(&path, out);
  }
  let failed = failed.into_inner().unwrap();
  let checked = done.load(Ordering::Acquire);
  let entries: usize = segs.iter().map(|s| s.2).sum();
  let total_fft: f64 = segs.iter().map(|s| s.3).sum();
  let mut report = if segs.len() <= 1 {
    format!(
      "execute: {checked}/{covered} blocks checked into one shared record \
       ({workers} threads), total measured {:.1} BFFT\n{entries} unique \
       queries, record {:.1} GiB retained, {:.0}s",
      total_fft / 1e9,
      f64_from_usize(segs.last().map_or(0, |s| s.4)) / GIB,
      t0.elapsed().as_secs_f64()
    )
  } else {
    // Cut mode: entries sum per-segment uniques, so cross-segment
    // re-derivation is counted per segment — that duplication against
    // the whole-env count IS the price of cutting; report it honestly.
    let max_retained = segs.iter().map(|s| s.4).max().unwrap_or(0);
    format!(
      "execute: {checked}/{covered} blocks checked into {} record \
       segments ({workers} threads), total measured {:.1} BFFT\n\
       {entries} unique queries (per-segment sum), largest segment \
       {:.1} GiB, {:.0}s",
      segs.len(),
      total_fft / 1e9,
      f64_from_usize(max_retained) / GIB,
      t0.elapsed().as_secs_f64()
    )
  };
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
  // unproven segment fails the run, keep-going or not. The report
  // (with the full reject inventory) rides in the error.
  if !failed.is_empty() || unproven_segs > 0 {
    return Err(format!(
      "{report}\nFAILED: {} kernel-rejected block(s), {unproven_segs} \
       segment(s) not proven",
      failed.len()
    ));
  }
  Ok(report)
}

/// Manifest-driven execution: measure (dry) or prove the shards of a
/// PR-550 `.ixes` manifest, one shared warm record per shard, with the
/// EXACT post-execution RAM model gating every prove. This is the
/// "plan statically -> verify exactly -> fix up -> prove" pipeline's
/// engine:
///
/// - Each selected shard executes its OWNED block list in parallel into
///   a fresh record (fixed list, no cutting, drain = pool completion),
///   runs one `verify_segment` claim over the sorted list, derives
///   multiplicities, and evaluates `peak_prove_bytes` — the calibrated
///   exact model — on the sealed record.
/// - Dry mode reports every shard's exact peak against the budget; with
///   `fixup_out`, it then rewrites the manifest: shards measuring OVER
///   budget are split in two with the same hypergraph partitioner on
///   their own subgraph; consecutive under-budget shards are greedily
///   merged while the SUM of their measured peaks stays under budget
///   (sound: the model is subadditive in circuit heights — a union
///   record only dedups — so the sum is a conservative bound, and the
///   next measure round re-verifies exactly anyway).
/// - Prove mode proves each shard whose exact peak fits; a shard that
///   measures over budget self-heals — split in place with the same
///   partitioner the fixup uses, halves re-measured and proven
///   recursively. Only a single block over budget is irreducible.
///
/// An all-shards run first proves exact cover (every schedule block
/// owned exactly once) — the whole-env soundness condition — and the
/// returned status carries any rejection or unproven unit as an error.
/// Every decision is made on a measurement; the static planner's cost
/// model only has to land NEAR the budget for the fix-up to converge in
/// a round or two.
#[allow(clippy::too_many_arguments)]
pub fn execute_manifest(
  toplevel: &Toplevel,
  fun_idx: usize,
  block_fun_idx: usize,
  env: &Arc<IxonEnv>,
  workers: usize,
  manifest_path: &str,
  shard_sel: Option<usize>,
  dry_run: bool,
  fixup_out: Option<&str>,
  prove_system: Option<&AiurSystem>,
) -> Result<String, String> {
  let system = prove_system.ok_or("manifest mode requires --prove")?;
  let (blocks, adj) = schedule_blocks(env);
  if blocks.is_empty() {
    return Err("empty environment".to_string());
  }
  let id_of: FxHashMap<&Address, u32> = blocks
    .iter()
    .enumerate()
    .map(|(i, b)| (&b.addr, u32::try_from(i).expect("block ids fit u32")))
    .collect();
  let manifest_bytes =
    std::fs::read(manifest_path).map_err(|e| format!("{manifest_path}: {e}"))?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)?;
  let workers = if workers == 0 {
    std::thread::available_parallelism()
      .map_or(4, usize::from)
      .saturating_sub(1)
      .max(1)
  } else {
    workers
  };
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
  eprintln!(
    "[manifest] {} shard(s) of {}, {workers} threads, budget      {budget_gib:.0} GiB",
    selected.len(),
    manifest.shards.len(),
  );
  // One shared io for the whole run, exactly as in whole-env mode.
  let shared_io =
    Arc::new(aiur::execute::SharedIO::new(EnvFaultSource::new(env.clone())));
  preassign_canonical_io(env, &shared_io);
  let t0 = std::time::Instant::now();
  // (shard index, measured exact peak, rejected?) per selected shard.
  let mut measured: Vec<(usize, usize, bool)> = Vec::new();
  let mut report = String::new();
  let mut healed = 0usize;
  // Work queue: manifest shards in order; prove-mode self-heal splits
  // push their halves depth-first right behind the parent. Halves carry
  // no manifest index, so `measured` (the fixup input) stays one entry
  // per manifest shard — the parent keeps its over-budget measurement.
  let mut work: std::collections::VecDeque<(String, Vec<u32>, Option<usize>)> =
    std::collections::VecDeque::new();
  for &si in &selected {
    let ids: Vec<u32> = manifest.shards[si]
      .blocks
      .iter()
      .map(|a| {
        id_of.get(a).copied().ok_or_else(|| {
          format!("manifest block {} not in env schedule", a.hex())
        })
      })
      .collect::<Result<_, _>>()?;
    work.push_back((si.to_string(), ids, Some(si)));
  }
  // Whole-env soundness gate: an all-shards run claims "every env
  // constant checked", so the manifest must own every schedule block
  // exactly once — missing and duplicated blocks both void the claim.
  // (Blocks foreign to the schedule already failed id resolution
  // above.) A single-shard run is inherently partial and says so.
  if manifest.shards.is_empty() {
    return Err("manifest has no shards".to_string());
  }
  match shard_sel {
    None => {
      let mut owners = vec![0u32; blocks.len()];
      for (_, ids, _) in &work {
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
        "[manifest] exact cover: {} schedule blocks owned exactly once",
        blocks.len()
      );
    },
    Some(k) => {
      eprintln!("[manifest] PARTIAL: shard {k} only — no coverage claim");
    },
  }
  let mut failures = 0usize;
  while let Some((label, ids, mi)) = work.pop_front() {
    let record = QueryRecord::new(toplevel);
    let cursor = AtomicUsize::new(0);
    let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
    let ts = std::time::Instant::now();
    std::thread::scope(|sc| {
      for _ in 0..workers.min(ids.len().max(1)) {
        sc.spawn(|| {
          loop {
            let lo = cursor.fetch_add(1, Ordering::AcqRel);
            if lo >= ids.len() {
              break;
            }
            let b = ids[lo];
            let mut io = IOBuffer::with_shared(shared_io.clone());
            let input = addr_key(&blocks[b as usize].addr);
            if let Err(e) = execute_ixvm_with_record(
              toplevel, block_fun_idx, &input, &mut io, &record,
            ) {
              eprintln!(
                "[shard {label}] SKIPPING block {}: {e}",
                blocks[b as usize].addr.hex()
              );
              failed
                .lock()
                .unwrap()
                .push((blocks[b as usize].addr.clone(), e.to_string()));
            }
          }
        });
      }
    });
    let rejects = failed.into_inner().unwrap();
    // Seal: one verify_segment claim over the sorted owned list.
    let mut seg_claim: Option<Vec<G>> = None;
    if rejects.is_empty() {
      let addrs: Vec<Address> =
        ids.iter().map(|&b| blocks[b as usize].addr.clone()).collect();
      match run_segment_claim(toplevel, fun_idx, &shared_io, &record, addrs) {
        Ok(input) => seg_claim = Some(input),
        Err(e) => {
          eprintln!("[shard {label}] segment claim failed: {e}");
        },
      }
    }
    let clean = rejects.is_empty() && seg_claim.is_some();
    if !clean {
      failures += 1;
    }
    if clean {
      let dio = IOBuffer::with_shared(shared_io.clone());
      let claim_list: Vec<(usize, Vec<G>)> =
        seg_claim.iter().map(|inp| (fun_idx, inp.clone())).collect();
      aiur::trace::derive_multiplicities_into(
        toplevel, &record, &dio, &claim_list,
      );
    }
    let peak = system.peak_prove_bytes(&record).peak;
    let fits = peak <= budget_bytes;
    let line = format!(
      "[shard {label}] {} blocks, exact peak {:.1} GiB {} budget        {budget_gib:.0} GiB{}, {:.0}s",
      ids.len(),
      f64_from_usize(peak) / GIB,
      if fits { "<=" } else { "OVER" },
      if clean { "" } else { " [REJECTED BLOCKS — not provable]" },
      ts.elapsed().as_secs_f64(),
    );
    eprintln!("{line}");
    report.push_str(&line);
    report.push('\n');
    if let Some(si) = mi {
      measured.push((si, peak, !clean));
    }
    if !dry_run && clean && fits {
      let mut claims: Vec<Vec<G>> = Vec::with_capacity(1);
      if let Some(inp) = &seg_claim
        && let Some(q) = record.function_queries[fun_idx].get(inp)
      {
        claims.push(aiur::synthesis::function_claim(fun_idx, inp, q.output));
      }
      let io = IOBuffer::with_shared(shared_io.clone());
      let pt = std::time::Instant::now();
      let proof = system.prove_sealed(record, &io, &claims);
      system
        .verify_sealed(&claims, &proof)
        .map_err(|e| format!("shard {label} proof failed verification: {e:?}"))?;
      let pline = format!(
        "[shard {label}] proved+verified in {:.0}s, proof {:.1} MiB, rss {:.0}G",
        pt.elapsed().as_secs_f64(),
        f64_from_usize(proof.to_bytes().map_or(0, |b| b.len()))
          / (1024.0 * 1024.0),
        process_rss_gib(),
      );
      eprintln!("{pline}");
      report.push_str(&pline);
      report.push('\n');
    } else if !dry_run && clean && !fits {
      if ids.len() > 1 {
        // Self-heal: this shard was just MEASURED over budget on its
        // real sealed record, so split it here with the same
        // partitioner the fixup uses and prove the halves — no
        // separate measure round, no trusting the manifest. Halves
        // that still measure over split again; a single block that
        // cannot fit is irreducible.
        let (ha, hb) = bisect_shard_ids(&blocks, &adj, &ids);
        let l = format!(
          "[shard {label}] exact peak over budget — self-healing split          into {label}a ({} blocks) + {label}b ({} blocks)",
          ha.len(),
          hb.len(),
        );
        eprintln!("{l}");
        report.push_str(&l);
        report.push('\n');
        healed += 1;
        work.push_front((format!("{label}b"), hb, None));
        work.push_front((format!("{label}a"), ha, None));
      } else {
        failures += 1;
        let l = format!(
          "[shard {label}] NOT PROVEN: single block over budget — needs          a bigger box"
        );
        eprintln!("{l}");
        report.push_str(&l);
        report.push('\n');
      }
    }
  }
  // Fix-up: split measured violators, merge consecutive underfilled
  // shards while the sum of exact peaks stays under budget. Whole-
  // manifest scope only (a partial measure can't safely rewrite rows it
  // did not measure).
  if let Some(out) = fixup_out {
    if shard_sel.is_some() {
      return Err("--fixup-out requires measuring ALL shards".into());
    }
    let profile = {
      let mut b = ProfileBuilder::new();
      for blk in &blocks {
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
      b.finish()
    };
    assert_eq!(profile.num_blocks(), blocks.len());
    let mut shard_of: Vec<u32> = vec![u32::MAX; blocks.len()];
    let mut next_id: u32 = 0;
    let mut splits = 0usize;
    let mut merges = 0usize;
    let mut i = 0usize;
    while i < measured.len() {
      let (si, peak, rejected) = measured[i];
      let owned_ids = |si: usize| -> Vec<u32> {
        manifest.shards[si].blocks.iter().map(|a| id_of[a]).collect()
      };
      if !rejected && peak > budget_bytes {
        // SPLIT: bisect this shard's own subgraph with the same
        // partitioner the plan used.
        let (ha, hb) = bisect_shard_ids(&blocks, &adj, &owned_ids(si));
        let (a_id, b_id) = (next_id, next_id + 1);
        next_id += 2;
        for &b in &ha {
          shard_of[b as usize] = a_id;
        }
        for &b in &hb {
          shard_of[b as usize] = b_id;
        }
        splits += 1;
        i += 1;
      } else {
        // MERGE run: greedily absorb consecutive clean shards while the
        // sum of measured peaks stays under budget (conservative by
        // subadditivity; the next measure round re-verifies exactly).
        let mut sum = peak;
        let mut group = vec![si];
        let mut j = i + 1;
        while j < measured.len() {
          let (sj, pj, rj) = measured[j];
          if rejected || rj || pj > budget_bytes || sum + pj > budget_bytes {
            break;
          }
          sum += pj;
          group.push(sj);
          j += 1;
        }
        if group.len() > 1 {
          merges += group.len() - 1;
        }
        let gid = next_id;
        next_id += 1;
        for &sj in &group {
          for b in owned_ids(sj) {
            shard_of[b as usize] = gid;
          }
        }
        i = j.max(i + 1);
      }
    }
    // Blocks not owned by any manifest shard (foreign-only refs) keep a
    // catch-all id so the profile-wide rebuild stays total.
    let catch_all = next_id;
    let mut orphans = false;
    for s in shard_of.iter_mut() {
      if *s == u32::MAX {
        *s = catch_all;
        orphans = true;
      }
    }
    let n = usize::try_from(next_id).expect("shard count fits usize")
      + usize::from(orphans);
    let new_manifest = ShardManifest::build(&profile, &shard_of, n);
    std::fs::write(out, new_manifest.to_bytes())
      .map_err(|e| format!("{out}: {e}"))?;
    let l = format!(
      "[fixup] {splits} split(s), {merges} merge(s) -> {n} shard(s)        written to {out}{}",
      if splits == 0 && merges == 0 { " (stable)" } else { "" }
    );
    eprintln!("{l}");
    report.push_str(&l);
    report.push('\n');
  }
  report.push_str(&format!(
    "manifest: {} shard(s) measured{}, {:.0}s total",
    measured.len(),
    if healed > 0 {
      format!(", {healed} self-healed split(s)")
    } else {
      String::new()
    },
    t0.elapsed().as_secs_f64()
  ));
  // Exit status is the verdict: rejected shards and units that could
  // not be proven fail the run (over-budget MEASUREMENTS in dry mode
  // do not — they are the output the fixup consumes).
  if failures > 0 {
    return Err(format!(
      "{report}\nFAILED: {failures} shard(s) rejected or not proven"
    ));
  }
  Ok(report)
}

/// Bisect a shard's block-id set with the plan's partitioner on its own
/// subgraph (edges restricted to the set), returning the two halves.
/// Sub-profile positions are address-sorted over the set, mirroring
/// [`ShardManifest::build`]. Degenerate partitions (an empty side) fall
/// back to an id-ordered halving so a split always makes progress.
fn bisect_shard_ids(
  blocks: &[SchedBlock],
  adj: &[Vec<u32>],
  ids: &[u32],
) -> (Vec<u32>, Vec<u32>) {
  let mut sb = ProfileBuilder::new();
  let idset: FxHashMap<u32, ()> = ids.iter().map(|&b| (b, ())).collect();
  for &b in ids {
    let blk = &blocks[b as usize];
    let ops = OpCounts { intern_nodes: blk.size, ..OpCounts::default() };
    sb.block(
      blk.addr.clone(),
      0,
      u32::try_from(blk.size).expect("size fits"),
      u32::try_from(blk.members.len()).expect("members fit"),
      ops,
    );
  }
  for &b in ids {
    for &r in &adj[b as usize] {
      if idset.contains_key(&r) {
        sb.delta_edge(
          blocks[b as usize].addr.clone(),
          blocks[r as usize].addr.clone(),
        );
      }
    }
  }
  let sub = sb.finish();
  let half = Hypergraph::from_profile(&sub).partition(2, 0.05);
  // Sub-profile ids are address-sorted over the shard's blocks.
  let mut sorted: Vec<u32> = ids.to_vec();
  sorted
    .sort_by(|&a, &b| blocks[a as usize].addr.cmp(&blocks[b as usize].addr));
  let (mut ha, mut hb) = (Vec::new(), Vec::new());
  for (pos, &b) in sorted.iter().enumerate() {
    if half[pos] == 0 { &mut ha } else { &mut hb }.push(b);
  }
  if ha.is_empty() || hb.is_empty() {
    let mut s = ids.to_vec();
    s.sort_unstable();
    let mid = s.len() / 2;
    return (s[..mid].to_vec(), s[mid..].to_vec());
  }
  (ha, hb)
}

/// GiB → whole bytes via the decimal round-trip (no `as` cast); caps are
/// small positive magnitudes.
fn gib_to_bytes_u64(gib: f64) -> u64 {
  format!("{:.0}", (gib * GIB).max(0.0)).parse().unwrap_or(u64::MAX)
}

/// `Bytecode.Toplevel.executeEnvWithEnv`: execute-only check of the
/// whole env, or of a closure when `roots` is non-empty — no partition,
/// no manifest (see [`execute_env`]). Params are ABI-simple strings:
/// `workers` (`0` = default width), `fail_fast` (`0` records and skips
/// kernel-rejected blocks instead of aborting), `roots` (comma-separated
/// 64-char hex constant addresses; `""` = whole env).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_execute_env_with_env(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  block_fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  workers: LeanString<LeanBorrowed<'_>>,
  fail_fast: LeanString<LeanBorrowed<'_>>,
  roots: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let block_fun_idx =
    crate::aiur::lean_unbox_nat_as_usize(block_fun_idx.inner());
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let fail_fast = fail_fast.to_string() != "0";
  let roots_s = roots.to_string();
  let mut roots: Vec<Address> = Vec::new();
  for h in roots_s.split(',').filter(|h| !h.is_empty()) {
    match Address::from_hex(h) {
      Some(a) => roots.push(a),
      None => {
        return LeanExcept::error_string(&format!(
          "rs_aiur_execute_env: bad root address hex {h}"
        ));
      },
    }
  }
  match execute_env(
    &toplevel,
    fun_idx,
    block_fun_idx,
    &env_handle.get().env,
    workers,
    fail_fast,
    false,
    None,
    None,
    &roots,
  ) {
    Ok(report) => {
      eprintln!("[rs_exec]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => LeanExcept::error_string(&format!("rs_aiur_execute_env: {e}")),
  }
}

/// `Aiur.AiurSystem.executeEnvProveWithEnv`: cut-mode whole-env
/// execution where each sealed segment record proceeds straight to
/// the STARK and is verified (see [`execute_env`]'s prove path). The
/// record is the witness — no per-shard re-execution.
/// `Aiur.AiurSystem.executeManifestProveWithEnv`: manifest-driven
/// measure/prove (see [`execute_manifest`]). String params (ABI-simple):
/// `shard_sel` — decimal index or "" for all shards; `dry_run` — "1"
/// measures only; `fixup_out` — path to write the split/merged manifest
/// ("" disables; requires all-shards dry measure).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_execute_manifest_prove_with_env(
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
  fixup_out: LeanString<LeanBorrowed<'_>>,
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
  let fixup_out = {
    let s = fixup_out.to_string();
    if s.is_empty() { None } else { Some(s) }
  };
  match execute_manifest(
    system.toplevel(),
    fun_idx,
    block_fun_idx,
    &env_handle.get().env,
    workers,
    &manifest_path,
    shard_sel,
    dry_run,
    fixup_out.as_deref(),
    Some(system),
  ) {
    Ok(report) => {
      eprintln!("[rs_manifest]\n{report}");
      LeanExcept::ok(LeanOwned::box_usize(0))
    },
    Err(e) => {
      LeanExcept::error_string(&format!("rs_aiur_execute_manifest_prove: {e}"))
    },
  }
}

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
  plan_out: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let system = aiur_system_obj.get();
  let fun_idx = crate::aiur::lean_unbox_nat_as_usize(fun_idx.inner());
  let block_fun_idx =
    crate::aiur::lean_unbox_nat_as_usize(block_fun_idx.inner());
  let workers = workers.to_string().parse::<usize>().unwrap_or(0);
  let fail_fast = fail_fast.to_string() != "0";
  let dry_run = dry_run.to_string() != "0";
  let plan_out = {
    let s = plan_out.to_string();
    if s.is_empty() { None } else { Some(s) }
  };
  match execute_env(
    system.toplevel(),
    fun_idx,
    block_fun_idx,
    &env_handle.get().env,
    workers,
    fail_fast,
    dry_run,
    plan_out.as_deref(),
    Some(system),
    &[],
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
