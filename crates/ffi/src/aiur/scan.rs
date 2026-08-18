//! Whole-env execution over one shared `QueryRecord`, with record
//! cutting at a MEASURED threshold and direct segment proving.
//!
//! [`execute_env`] runs the env's whole check schedule through the
//! codegen'd circuit kernel: worker threads WARM-execute one
//! `verify_block` per schedule block into a single shared record —
//! per-block checking keyed by address alone, so every shared
//! dependency cone derives once, with the entry's phantom external
//! multiplicity debumped — and each sealed segment then runs ONE
//! seal claim — the span's canonical `CheckEnv` claim (owned-set root +
//! thin-frontier assumption root) — whose per-node checks memo-hit
//! (and consume) the warm work. The record balances exactly as if the
//! seal claim executed alone. The schedule is a min-cut linearization of the env's
//! reference graph, which keeps closure-overlapping blocks adjacent so
//! memoization absorbs shared work.
//!
//! Two prove entrypoints share the engine, and neither adapts in-run:
//!
//! - [`execute_shards`] is the CLUSTER path: each `.ixes` shard of the
//!   static min-cut planner (`ix shard`) is an immutable work unit a
//!   box runs whole — execute the shard's owned blocks warm, seal ONE
//!   CheckEnv claim, derive multiplicities, measure the witness
//!   EXACTLY, and prove behind the measured gate. A shard that
//!   measures over the box's budget fails with the stable code
//!   `AIUR_SHARD_OVER_BUDGET` so a scheduler can re-partition it
//!   statically (claim composition makes any re-split sound); the box
//!   itself never splits, probes, or heals.
//! - Whole-env mode cuts execution spans on the record's retained
//!   bytes — a smooth, small quantity where the racing cut's slop
//!   costs a few harmless GiB of record — sized conservatively so
//!   each span is ONE proof, sealed and gated exactly the same way.
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

/// Whole-env check schedule through the codegen'd kernel in parallel.
/// `fun_idx` is `verify_claim` (the single per-span seal claim run at
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
  // One cut threshold on the record's retained bytes, from the
  // measured budget: spans are RAM containers sized by
  // [`EXEC_RETAINED_FRAC`] so each one's sealed witness fits the
  // budget.
  let cut_bytes: usize =
    usize::try_from(gib_to_bytes_u64(budget_gib * EXEC_RETAINED_FRAC))
      .unwrap_or(usize::MAX);
  let budget_bytes: usize =
    usize::try_from(gib_to_bytes_u64(budget_gib)).unwrap_or(usize::MAX);
  let cursor = AtomicUsize::new(0);
  let done = AtomicUsize::new(0);
  let abort = std::sync::atomic::AtomicBool::new(false);
  let failed: Mutex<Vec<(Address, String)>> = Mutex::new(Vec::new());
  let fatal: Mutex<Option<String>> = Mutex::new(None);
  let t0 = std::time::Instant::now();
  // (seg_start, seg_end, unique entries, fft cost, retained bytes).
  let mut segs: Vec<(usize, usize, usize, f64, usize)> = Vec::new();
  // Prove-mode segments sealed unclean (rejects / missing claim) and
  // therefore not proven — a failure the exit status must carry.
  let mut unproven_segs = 0usize;
  // Spans sealed, measured, and proven (or DRY-measured) so far.
  let mut spans_proven = 0usize;
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
                      format!("{}@{lo}", blocks[order[lo] as usize].addr.hex())
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
        let (failed, fatal, active_workers) =
          (&failed, &fatal, &active_workers);
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
          // multiplicity (its one seal-claim consumer) is
          // DERIVED at seal, so no phantom-caller accounting exists.
          let run = |b: u32| -> Result<(), String> {
            let mut io = IOBuffer::with_shared(shared_io.clone());
            let input = addr_key(&blocks[b as usize].addr);
            execute_ixvm_with_record(
              toplevel,
              block_fun_idx,
              &input,
              &mut io,
              &record,
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
            // drain itself. Both modes cut on the record's RETAINED
            // bytes — the only thing an execution span must bound.
            // Proof sizing does NOT happen here: it happens at the
            // derivation layer after the span seals, where measurement
            // is exact and stopping is per-block, so the sloppiness of
            // a racing cut (drain window, in-flight stragglers) costs
            // a few harmless GiB of record, never a proof's RAM.
            if record_retained_bytes(record) >= cut_bytes {
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
    let retained = record_retained_bytes(&record);
    let entries: usize =
      record.function_queries.iter().map(|m| m.len()).sum::<usize>()
        + record.memory_queries.iter().map(|(_, m)| m.len()).sum::<usize>();
    let fft = record_fft_cost(toplevel, &record);
    // Padded transform work (prove mode): the raw BFFT is the smooth
    // cross-run diagnostic; the padded figure is what the prover's wall
    // actually tracks.
    let padded_note = format!(
      " ({:.1} padded)",
      system.padded_fft_cost_of_record(&record) / 1e9
    );
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
    {
      if failed.lock().unwrap().len() != seg_failed_base {
        eprintln!(
          "[prove span {}] SKIPPED: rejected block(s) — partial records \
           are not proven",
          segs.len() - 1
        );
        if !dry_run {
          unproven_segs += 1;
        }
      } else if seg_end > seg_start {
        // ONE proof per span: seal the span's canonical CheckEnv
        // claim into the warm record, derive multiplicities, measure
        // the witness EXACTLY, and prove behind the measured gate.
        // Spans are sized conservatively ([`EXEC_RETAINED_FRAC`]) so
        // their witnesses fit the budget; a span that still measures
        // over is refused with a stable code — nothing over-budget
        // ever reaches a STARK, and sizing work to a box precisely is
        // the cluster pipeline's job, not in-run splitting.
        let gi = spans_proven + unproven_segs;
        let dio = IOBuffer::with_shared(shared_io.clone());
        let owned: Vec<Address> = order[seg_start..seg_end]
          .iter()
          .flat_map(|&b| blocks[b as usize].members.iter().cloned())
          .collect();
        match run_check_env_claim(
          toplevel, fun_idx, &shared_io, &record, env, &owned,
        ) {
          Ok((ixon_claim, input)) => {
            let dt = std::time::Instant::now();
            aiur::trace::derive_multiplicities_into(
              toplevel,
              &record,
              &dio,
              &[(fun_idx, input.clone())],
            );
            let exact = system.peak_prove_bytes(&record).peak;
            eprintln!(
              "[span {gi}] multiplicities derived in {:.1}s, measured \
               witness peak {:.1} GiB",
              dt.elapsed().as_secs_f64(),
              f64_from_usize(exact) / GIB,
            );
            match record.function_queries[fun_idx].get(&input) {
              Some(q) => {
                let claims = vec![aiur::synthesis::function_claim(
                  fun_idx, &input, q.output,
                )];
                if dry_run {
                  eprintln!(
                    "[prove span {gi}] DRY: blocks \
                     {seg_start}..{seg_end}, measured witness peak \
                     {:.1} GiB — STARK skipped",
                    f64_from_usize(exact) / GIB,
                  );
                  spans_proven += 1;
                } else if exact > budget_bytes {
                  // The EXACT gate: an over-budget span is not proven
                  // (an OOM is not a verdict) — it is reported with a
                  // stable code and fails the run.
                  eprintln!(
                    "[prove span {gi}] REFUSED: \
                     AIUR_SPAN_OVER_BUDGET span={gi} blocks={} \
                     peak_bytes={exact} budget_bytes={budget_bytes}",
                    seg_end - seg_start,
                  );
                  unproven_segs += 1;
                } else {
                  let io = IOBuffer::with_shared(shared_io.clone());
                  let sealed =
                    std::mem::replace(&mut record, QueryRecord::new(toplevel));
                  let st = std::time::Instant::now();
                  let proof = system.prove_sealed(sealed, &io, &claims);
                  let prove_s = st.elapsed().as_secs_f64();
                  let vt = std::time::Instant::now();
                  system.verify_sealed(&claims, &proof).map_err(|e| {
                    format!("span proof failed verification: {e:?}")
                  })?;
                  let verify_s = vt.elapsed().as_secs_f64();
                  let proof_bytes = proof
                    .to_bytes()
                    .map_err(|e| format!("proof encode: {e:?}"))?;
                  let proof_len = proof_bytes.len();
                  let stored = store_proof(&ixon_claim, proof_bytes)?;
                  eprintln!(
                    "[prove span {gi}] prove {:.0}s, verify {:.1}s, \
                     proof {:.1} MiB, rss {:.0}G, stored {}",
                    prove_s,
                    verify_s,
                    f64_from_usize(proof_len) / (1024.0 * 1024.0),
                    process_rss_gib(),
                    stored.hex(),
                  );
                  spans_proven += 1;
                }
              },
              None => {
                eprintln!(
                  "[prove span {gi}] SKIPPED: seal claim entry missing \
                   from record"
                );
                if !dry_run {
                  unproven_segs += 1;
                }
              },
            }
          },
          Err(e) => {
            eprintln!("[prove span {gi}] SKIPPED: seal claim failed: {e}");
            if !dry_run {
              unproven_segs += 1;
            }
          },
        }
      }
      // The span's record served every group; the next span starts
      // fresh (SharedIO persists).
      // The span's record served its proof; the next span starts
      // fresh. The SharedIO persists: its layout is env-canonical plus
      // schedule-ordered claim seeds, so every record couples to the
      // same io coordinates and the io outlives them all.
      drop(std::mem::replace(&mut record, QueryRecord::new(toplevel)));
    }
    seg_start = seg_end;
  }
  if let Some(e) = fatal.into_inner().unwrap() {
    return Err(e);
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
    "[shards] {} of {}, {workers} threads, budget {budget_gib:.0} GiB",
    work.len(),
    manifest.shards.len(),
  );
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
    // Seal: the shard's canonical CheckEnv claim over its owned
    // constants — the claim the shard's proof commits to.
    let mut seg_claim: Option<(ixon::proof::Claim, Vec<G>)> = None;
    if rejects.is_empty() {
      let owned: Vec<Address> = ids
        .iter()
        .flat_map(|&b| blocks[b as usize].members.iter().cloned())
        .collect();
      match run_check_env_claim(
        toplevel, fun_idx, &shared_io, &record, env, &owned,
      ) {
        Ok(pair) => seg_claim = Some(pair),
        Err(e) => {
          eprintln!("[shard {si}] seal claim failed: {e}");
        },
      }
    }
    let clean = rejects.is_empty() && seg_claim.is_some();
    if clean {
      let dio = IOBuffer::with_shared(shared_io.clone());
      let claim_list: Vec<(usize, Vec<G>)> =
        seg_claim.iter().map(|(_, inp)| (fun_idx, inp.clone())).collect();
      aiur::trace::derive_multiplicities_into(
        toplevel,
        &record,
        &dio,
        &claim_list,
      );
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
      if let Some((_, inp)) = &seg_claim
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
      let stored = match &seg_claim {
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
