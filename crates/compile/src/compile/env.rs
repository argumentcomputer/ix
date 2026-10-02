//! Top-level environment compilation with work-stealing parallelism.
//!
//! Extracted from `compile.rs` to keep the scheduler independently readable.
//!
//! # Memory
//!
//! Peak RSS is kept a small multiple of the environment's serialized
//! size (Mathlib: ~19 GB for a 3 GB `.ixe`) by holding compact
//! representations everywhere the structured forms aren't actually
//! read: the Lean environment decodes on demand behind a bounded cache
//! (`decode_env_lazy` in the ffi crate) rather than as a whole-env
//! owned copy, accumulator constants and named metadata live as their
//! serialized bytes rather than ~20×-larger structured forms, worker
//! kernel contexts are fresh per block (canonicity §10.5), the setup
//! scan reads the Lean objects without decoding them (a
//! [`ConstScanner`] from the ffi crate), and the `.ixe` streams to disk
//! from Rust rather than crossing the FFI as an env-sized ByteArray.
//! All of it is always on, and every mode produces a bit-identical
//! `.ixe`.
//!
//! Three knobs:
//! - `IX_COMPILE_WORKERS=N` — scheduler worker ceiling (default: all
//!   cores). Adaptive admission controls the active count under memory
//!   pressure; set `IX_COMPILE_ADAPTIVE=0` for fixed parallelism.
//! - `IX_COMPILE_DEMOTE=0` — keep materialized caches next to the
//!   accumulator's bytes instead of demoting to bytes-only. Spends
//!   RAM to make post-compile structural reads free, which only pays
//!   in flows that re-read the compiled env in-process (`ix check` /
//!   `ix validate`); `ix compile` itself never reads them back.
//! - `IX_COMPILE_EAGER=1` — decode the whole Lean environment up
//!   front instead of on demand. Spends the single largest memory
//!   term (Mathlib: peak 38–44 GB against 18–19 GB, for about 15%
//!   less user CPU) on hardware with RAM to spare; see
//!   `decode_env_for_compile` in the ffi crate.
//!
//! And one validation knob: `IX_SETUP_SCAN_CHECK=1` also runs the
//! decoding setup scan and fails the compile unless the scanner's
//! outputs are identical to it.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::{
  Arc, LazyLock, Mutex,
  atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering},
};
use std::thread;
use std::time::{Duration, Instant};

use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

use super::admission::Admission;
use crate::compile::{
  BlockCache, CompileOptions, CompileState,
  aux_gen::nested::validate_ind_groups, compile_const, compile_const_no_aux,
};
use crate::condense::compute_sccs;
use crate::graph::{
  ConstScanner, NameSet, compare_setup_scans, setup_scan, setup_scan_with,
};
use crate::ground::proliferate_ungrounded;
use ix_common::address::Address;
use ix_common::env::{Env as LeanEnv, Name};
use ixon::CompileError;

// ===========================================================================
// Progress + diagnostic logging
// ===========================================================================

/// Enable progress output. Quiet by default; set `IX_VERBOSE=1` to see
/// per-phase timings and scheduler progress. `IX_COMPILE_DBG=1` (the
/// Lean driver's phase-attribution knob) is accepted as an alias so one
/// flag lights up both sides of the pipeline.
pub(crate) static IX_VERBOSE: LazyLock<bool> = LazyLock::new(|| {
  std::env::var("IX_VERBOSE").is_ok() || std::env::var("IX_COMPILE_DBG").is_ok()
});

/// Log every block start + finish. Set `IX_LOG_BLOCKS=1` for deep debugging.
/// Very verbose — only useful when you need to pin a panic to a specific block.
static IX_LOG_BLOCKS: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_LOG_BLOCKS").is_ok());

/// Periodic progress update interval in milliseconds (default 2000ms).
/// Set `IX_PROGRESS_MS=0` to disable periodic updates.
static IX_PROGRESS_MS: LazyLock<u64> = LazyLock::new(|| {
  std::env::var("IX_PROGRESS_MS")
    .ok()
    .and_then(|s| s.parse().ok())
    .unwrap_or(2000)
});

/// Recover a short string description from a panic payload.
fn panic_message(panic: &(dyn std::any::Any + Send)) -> String {
  panic
    .downcast_ref::<String>()
    .cloned()
    .or_else(|| panic.downcast_ref::<&'static str>().map(|s| (*s).to_string()))
    .unwrap_or_else(|| "<non-string panic payload>".to_string())
}

/// Run `f` catching any panic and converting it to a `CompileError` tagged
/// with `block_name` (and `caller` to distinguish which compile function
/// panicked). This keeps a single bad block from aborting the whole
/// compilation and preserves enough context to find the culprit — a raw
/// panic from deep inside aux_gen has no indication of which SCC it was
/// working on.
///
/// When `IX_LOG_BLOCKS` is set, panics also emit an immediate eprintln so
/// they appear in log order alongside block BEGIN/END markers.
fn run_compile_catching_panic<F>(
  block_name: &Name,
  caller: &'static str,
  f: F,
) -> Result<Address, CompileError>
where
  F: FnOnce() -> Result<Address, CompileError>,
{
  match catch_unwind(AssertUnwindSafe(f)) {
    Ok(res) => res,
    Err(panic) => {
      let msg = panic_message(&*panic);
      if *IX_LOG_BLOCKS {
        eprintln!(
          "[compile_env] PANIC in {caller} for {}: {msg}",
          block_name.pretty()
        );
      }
      Err(CompileError::UnsupportedExpr {
        desc: format!(
          "{caller} panicked while compiling block {}: {msg}",
          block_name.pretty()
        ),
      })
    },
  }
}

/// Compile an entire Lean environment to Ixon format.
/// Work-stealing compilation using crossbeam channels.
///
/// Instead of processing blocks in waves (which underutilizes cores when wave sizes vary),
/// we use a work queue. When a block completes, it immediately unlocks dependent blocks.
pub fn compile_env(
  lean_env: &Arc<LeanEnv>,
) -> Result<CompileState, CompileError> {
  compile_env_with_options(lean_env, CompileOptions::default())
}

/// Compile an entire Lean environment with explicit resource/correctness
/// options. See [`CompileOptions`] for the intended call-site split between
/// trusted Lean environments and adversarial raw-constant tests.
pub fn compile_env_with_options(
  lean_env: &Arc<LeanEnv>,
  options: CompileOptions,
) -> Result<CompileState, CompileError> {
  compile_env_with_profile(lean_env, options, None)
}

/// Compile semantic input with an explicit profile, or the built-in profile
/// when omitted. No annotated result can bypass combined validation.
pub fn compile_env_with_profile(
  lean_env: &Arc<LeanEnv>,
  options: CompileOptions,
  profile: Option<&ixon::resource::addressed::Profile>,
) -> Result<CompileState, CompileError> {
  compile_env_with_scanner(lean_env, options, profile, None)
}

/// `IX_SETUP_SCAN_CHECK=1`: when the compile runs its setup scan through
/// a [`ConstScanner`], also run the decoding [`setup_scan`] and fail the
/// compile unless every output is identical. A validation knob: the
/// second scan decodes the whole environment.
static IX_SETUP_SCAN_CHECK: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_SETUP_SCAN_CHECK").as_deref() == Ok("1"));

/// [`compile_env_with_profile`] whose setup scan reads each constant
/// through `scanner` (see [`setup_scan_with`]) instead of decoding it.
/// The ffi crate passes a scanner that walks the Lean objects directly.
pub fn compile_env_with_scanner(
  lean_env: &Arc<LeanEnv>,
  options: CompileOptions,
  profile: Option<&ixon::resource::addressed::Profile>,
  scanner: Option<&dyn ConstScanner>,
) -> Result<CompileState, CompileError> {
  let _memory_sampler = crate::diag::memory_sampler("compile_env");
  // The sharing limits of the whole run, read once: an invalid
  // `IX_SHARING_LIMITS` fails the compile here, before any block is
  // scheduled (Lean `compileEnvParallelAux` does the same).
  let sharing_limits = crate::compile::compiler_sharing_limits()
    .map_err(|reason| CompileError::SharingConstruction { reason })?;
  let setup_start = Instant::now();
  // Whole-env scan: ref graph + immediate groundedness + inductive
  // groups in one pass per constant — the env decodes lazily, so each
  // additional full sweep would decode every constant again. A scanner
  // reads the source objects without decoding them at all.
  let phase_start = Instant::now();
  let scan = match scanner {
    Some(scanner) => {
      let scan = setup_scan_with(lean_env.as_ref(), scanner);
      if *IX_SETUP_SCAN_CHECK {
        let check_start = Instant::now();
        let reference = setup_scan(lean_env.as_ref());
        compare_setup_scans(&scan, &reference).map_err(|diff| {
          CompileError::UnsupportedExpr {
            desc: format!("IX_SETUP_SCAN_CHECK: setup scans differ: {diff}"),
          }
        })?;
        eprintln!(
          "[compile_env] IX_SETUP_SCAN_CHECK: identical to the decoding scan \
           ({} out_refs, {} in_refs, {} edges, {} ungrounded, {} groups, \
           {} source contracts, semantic {:?}; reference scan {:.2}s)",
          scan.graph.out_refs.len(),
          scan.graph.in_refs.len(),
          scan.graph.out_refs.values().map(NameSet::len).sum::<usize>(),
          scan.immediate_ungrounded.len(),
          scan.ind_groups.len(),
          scan.source_contracts.len(),
          scan.semantic_sources.as_ref().map(Vec::len),
          check_start.elapsed().as_secs_f32(),
        );
      }
      scanner.release();
      scan
    },
    None => setup_scan(lean_env.as_ref()),
  };
  let semantic_sources = scan.semantic_sources?;
  if let Some(name) =
    scan.source_contracts.iter().min_by_key(|name| name.pretty())
  {
    return Err(CompileError::UnsupportedExpr {
      desc: format!("unresolved source binder contracts: {}", name.pretty()),
    });
  }
  let graph = scan.graph;
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 1/7 setup_scan (graph+ground+groups): {:.2}s{}",
      phase_start.elapsed().as_secs_f32(),
      crate::diag::rss_log_suffix(),
    );
  }

  // Grounding: constants whose transitive Const-refs can't all be
  // resolved are collected into `stt.ungrounded` and filtered from the
  // SCC input so they don't clog the scheduler. Callers (e.g. the
  // kernel check FFI) inspect `stt.ungrounded` per-constant to report
  // them as compile-side rejections without aborting the whole batch.
  let phase_start = Instant::now();
  let ungrounded =
    proliferate_ungrounded(scan.immediate_ungrounded, &graph.in_refs);
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 2/7 proliferate_ungrounded: {:.2}s{}",
      phase_start.elapsed().as_secs_f32(),
      crate::diag::rss_log_suffix(),
    );
  }
  // Pin the highest-in-degree constants in the lazy env: the ref
  // graph gives exact reference counts, and the distribution is
  // heavily skewed, so a small never-evicted set absorbs repeat
  // decodes of foundational constants that otherwise churn through
  // the bounded cache. At this size the overlay costs ≤0.3 GiB on
  // every measured env and wall time is Lean −15 %, FLT −4 %,
  // InitStd/Mathlib neutral (24-core box); larger sets bought RAM,
  // not speed, on the same sweep.
  const PIN_HOT_CONSTANTS: usize = 16384;
  if !graph.in_refs.is_empty() {
    let mut by_deg: Vec<(&Name, usize)> =
      graph.in_refs.iter().map(|(n, refs)| (n, refs.len())).collect();
    let k = PIN_HOT_CONSTANTS.min(by_deg.len());
    by_deg.select_nth_unstable_by(k - 1, |a, b| b.1.cmp(&a.1));
    lean_env.pin(by_deg[..k].iter().map(|(n, _)| (*n).clone()));
  }

  let ungrounded_map: crate::compile::FxDashMap<Name, String> =
    ungrounded.iter().map(|(n, e)| (n.clone(), format!("{e:?}"))).collect();
  if !ungrounded.is_empty() && *IX_VERBOSE {
    eprintln!(
      "[compile_env] {} ungrounded constants filtered from graph",
      ungrounded.len()
    );
    for (n, e) in ungrounded.iter().take(5) {
      eprintln!("  ungrounded: {} ({:?})", n.pretty(), e);
    }
    if ungrounded.len() > 5 {
      eprintln!("  ... and {} more", ungrounded.len() - 5);
    }
  }

  // Filter ungrounded names from the ref graph before SCC computation so
  // condensed blocks only contain constants we can actually compile.
  let grounded_out_refs: crate::graph::RefMap = if ungrounded_map.is_empty() {
    graph.out_refs
  } else {
    graph
      .out_refs
      .into_iter()
      .filter(|(name, _)| !ungrounded_map.contains_key(name))
      .map(|(k, refs)| {
        let filtered: FxHashSet<Name> = refs
          .into_iter()
          .filter(|r| !ungrounded_map.contains_key(r))
          .collect();
        (k, filtered)
      })
      .collect()
  };

  let phase_start = Instant::now();
  let condensed = compute_sccs(&grounded_out_refs);
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 3/7 compute_sccs ({} blocks): {:.2}s{}",
      condensed.blocks.len(),
      phase_start.elapsed().as_secs_f32(),
      crate::diag::rss_log_suffix(),
    );
  }

  // Domain restriction: reject environments with non-canonical inductive
  // flags. Groups come from the fused scan; only inductive families are
  // re-read here.
  let phase_start = Instant::now();
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 4/7 validate_ind_flags BEGIN ({} groups, {} Rayon threads){}",
      scan.ind_groups.len(),
      rayon::current_num_threads(),
      crate::diag::rss_log_suffix(),
    );
  }
  validate_ind_groups(&scan.ind_groups, lean_env.as_ref())?;
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 4/7 validate_ind_flags: {:.2}s{}",
      phase_start.elapsed().as_secs_f32(),
      crate::diag::rss_log_suffix(),
    );
  }

  let stt = CompileState {
    lean_env: Some(lean_env.clone()),
    ungrounded: ungrounded_map,
    // `setup_scan` inspected every constant and `semantic_sources?` above
    // stopped on any malformed annotation.
    contract_sources: Some(semantic_sources.iter().cloned().collect()),
    sharing_limits,
    ..Default::default()
  };

  // The (canonical) kenv is populated on-demand via ensure_in_kenv as
  // constants are compiled. Precompiles (PUnit, PProd, Eq, True) are
  // added below.

  // Pre-compile the builtins that aux_gen is known to reference, so the
  // scheduler has their addresses in `aux_name_to_addr` before any block
  // with `.below` / `.brecOn` / `.brecOn.eq` regeneration fires.
  //
  // Rationale: `build_ref_graph` scans only the *original* Lean env, so
  // refs that aux_gen introduces (e.g., `.brecOn.eq` using `Eq.symm`)
  // aren't visible to the scheduler's topological ordering. Without
  // these pre-compiles, a block's aux_gen could run before the
  // dep's own SCC does, producing a nondeterministic `MissingConstant`
  // error (race depends on work-stealing order).
  //
  // Seed names (exact Const refs aux_gen emits — grep `mk_const` in
  // `src/ix/compile/aux_gen/**`):
  //   - `.below` (Type-level): PUnit, PProd (+ ctors via SCC)
  //   - `.brecOn.eq`: Eq, Eq.refl, Eq.symm, Eq.ndrec, HEq, HEq.refl, True
  //
  // From these seeds we compute the **transitive SCC closure** using
  // `condensed.block_refs` (each SCC's out-edges) and compile the closure
  // in reverse topological order — so every SCC's deps are already in
  // `aux_name_to_addr` by the time its own compilation runs.
  //
  // Any pre-compile failure is a hard error: silent fallback would leave
  // the name unresolved and race with the main scheduler, reintroducing
  // the bug this exists to prevent.
  //
  // Names absent from `lean_env` (e.g., unit-test fixtures) are silently
  // skipped at seeding time — the initial `condensed.low_links.get` is
  // optional. Transitive deps of surviving seeds are assumed present.
  let phase_start = Instant::now();
  precompile_aux_gen_prereqs(&condensed, lean_env, &stt)?;
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 5/7 precompile_aux_gen_prereqs: {:.2}s{}",
      phase_start.elapsed().as_secs_f32(),
      crate::diag::rss_log_suffix(),
    );
  }

  // Build work-stealing data structures
  let total_blocks = condensed.blocks.len();
  let phase_start = Instant::now();

  // Blocks are numbered by their position in `condensed.blocks` and
  // borrow their leader, members and dependency names from `condensed`.
  // A block becomes ready when every one of its dependency names is
  // resolved: a name resolves when the block containing it completes or
  // when aux_gen compiled it early (`aux_gen_pending`), whichever comes
  // first, and only its first resolution counts (`resolved`), so each
  // (dependency name, dependent block) edge decrements the dependent's
  // `remaining` count exactly once — the same release rule as removing
  // the name from a per-block set of remaining names, which this replaces.
  let block_entries: Vec<(&Name, &NameSet)> = condensed.blocks.iter().collect();
  let block_info: Vec<SchedBlock<'_>> = block_entries
    .par_iter()
    .map(|&(lo, all)| {
      let deps = condensed.block_refs.get(lo).ok_or(
        CompileError::InvalidMutualBlock {
          reason: "missing block refs".into(),
        },
      )?;
      Ok(SchedBlock { lo, all, deps, remaining: AtomicUsize::new(deps.len()) })
    })
    .collect::<Result<_, CompileError>>()?;
  drop(block_entries);
  let reverse_deps = SchedDeps::new(&block_info);

  // Shared ready queue: blocks that are ready to compile
  let ready_queue: Mutex<Vec<u32>> = Mutex::new(Vec::new());

  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 6/7 block_info init ({} names, {} edges): {:.2}s",
      reverse_deps.resolved.len(),
      reverse_deps.dependents.len(),
      phase_start.elapsed().as_secs_f32()
    );
  }
  let phase_start = Instant::now();

  // Initialize with blocks that have zero remaining dependencies
  {
    let mut queue = ready_queue.lock().unwrap();
    for (id, block) in block_info.iter().enumerate() {
      if block.deps.is_empty() {
        queue.push(dense(id));
      }
    }
  }
  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] setup 7/7 ready_queue init: {:.2}s (total pre-scheduler: {:.2}s){}",
      phase_start.elapsed().as_secs_f32(),
      setup_start.elapsed().as_secs_f32(),
      crate::diag::rss_log_suffix(),
    );
  }

  // Track completed count for termination
  let completed = Arc::new(AtomicUsize::new(0));

  // Guard against duplicate processing: a block that's already been
  // handled is skipped. This prevents infinite loops from double-enqueuing.
  let processed: Vec<AtomicBool> =
    (0..total_blocks).map(|_| AtomicBool::new(false)).collect();

  // Error storage for propagating errors from workers
  let error: Mutex<Option<CompileError>> = Mutex::new(None);

  // Condvar for signaling workers when new work is available or completion
  let work_available = std::sync::Condvar::new();

  // Use scoped threads to borrow from parent scope. `IX_COMPILE_WORKERS`
  // gives large-env callers a simple peak-memory/speed tradeoff knob.
  let available_threads =
    thread::available_parallelism().map_or(4, |n| n.get());
  let requested_threads = options.max_workers.or_else(|| {
    std::env::var("IX_COMPILE_WORKERS")
      .ok()
      .and_then(|s| s.parse::<usize>().ok())
      .filter(|&n| n > 0)
  });
  let num_threads = requested_threads
    .unwrap_or(available_threads)
    .min(available_threads)
    .max(1);
  let admission = Admission::new(num_threads)?;

  // Progress tracking. `active` holds currently-compiling blocks per worker
  // so the reporter thread can show blocks that are still in-flight (useful
  // when a slow block is stuck or about to crash — those are the ones you
  // can't see otherwise). `stop_progress` signals the reporter to terminate.
  let compile_start = Instant::now();
  let active: Arc<Mutex<Vec<(Name, Instant)>>> =
    Arc::new(Mutex::new(Vec::new()));
  let stop_progress = Arc::new(AtomicBool::new(false));

  if *IX_VERBOSE {
    eprintln!(
      "[compile_env] starting: {total_blocks} blocks, {num_threads} workers"
    );
  }

  // Take references to shared data outside the loop
  let error_ref = &error;
  let stt_ref = &stt;
  let reverse_deps_ref = &reverse_deps;
  let block_info_ref = &block_info;
  let completed_ref = &completed;
  let processed_ref = &processed;
  let ready_queue_ref = &ready_queue;
  let condvar_ref = &work_available;
  let active_ref = &active;
  let stop_progress_ref = &stop_progress;
  let admission_ref = &admission;

  thread::scope(|s| {
    // Periodic progress reporter. Wakes every IX_PROGRESS_MS to print
    // completed/total and the oldest in-flight blocks. Exits when
    // stop_progress is set (after all workers have finished).
    //
    // Skipped entirely unless IX_VERBOSE is set, and also when
    // IX_PROGRESS_MS=0 — both imply "don't print periodic updates"
    // (one-shot errors still print).
    if *IX_VERBOSE && *IX_PROGRESS_MS > 0 {
      let interval = Duration::from_millis(*IX_PROGRESS_MS);
      // Shorter internal check so shutdown latency is bounded (otherwise the
      // scheduler waits up to `interval` for the reporter to wake and see
      // stop_progress). Cap at 250ms — shorter is wasted cycles, longer is
      // noticeable lag on fast compilations.
      let check_interval = interval.min(Duration::from_millis(250));
      let total = total_blocks;
      let completed_p = Arc::clone(completed_ref);
      let active_p = Arc::clone(active_ref);
      let stop_p = Arc::clone(stop_progress_ref);
      let start = compile_start;
      s.spawn(move || {
        let mut last_completed = 0usize;
        let mut last_print = Instant::now();
        let mut last_progress = Instant::now();
        while !stop_p.load(AtomicOrdering::Relaxed) {
          thread::sleep(check_interval);
          if stop_p.load(AtomicOrdering::Relaxed) {
            break;
          }
          // Only emit a progress line every `interval` — the sub-interval
          // poll exists purely for fast shutdown.
          if last_print.elapsed() < interval {
            continue;
          }
          let print_interval = last_print.elapsed().as_secs_f64();
          last_print = Instant::now();
          let done = completed_p.load(AtomicOrdering::SeqCst);
          // No new completion is not a deadlock signal: report how long
          // current blocks have been running, with their active count.
          let changed = done != last_completed;
          let delta = done.saturating_sub(last_completed);
          if changed { last_progress = Instant::now(); }
          last_completed = done;
          let pct = if total == 0 {
            100.0
          } else {
            (done as f64 / total as f64) * 100.0
          };
          let elapsed = start.elapsed().as_secs_f64();

          // Oldest in-flight blocks (up to 3) for visibility into
          // slow/stuck compilations. Sort by start time ascending.
          let (active_count, in_flight): (usize, Vec<String>) = {
            let mut entries: Vec<(Name, Instant)> =
              active_p.lock().unwrap().clone();
            entries.sort_by_key(|(_, t)| *t);
            let names = entries
              .iter()
              .take(3)
              .map(|(n, t)| {
                format!("{} ({:.0}s)", n.pretty(), t.elapsed().as_secs_f64())
              })
              .collect();
            (entries.len(), names)
          };
          let suffix = if in_flight.is_empty() {
            String::new()
          } else {
            format!(" · in-flight: {}", in_flight.join(", "))
          };

          // A lifetime-average ETA is misleading when a fast prefix is
          // followed by a handful of expensive blocks. Show recent work.
          if changed || done == 0 {
            eprintln!(
              "[compile_env] {done}/{total} ({pct:.1}%) · {elapsed:.0}s · +{delta} blocks/{print_interval:.1}s · active={active_count}{suffix}{}",
              crate::diag::rss_log_suffix(),
            );
          } else {
            eprintln!(
              "[compile_env] {done}/{total} ({pct:.1}%) · waiting: no completed blocks for {:.0}s · active={active_count}{suffix}",
              last_progress.elapsed().as_secs_f64(),
            );
          }
        }
      });
    }

    // Spawn worker threads.
    //
    // Each compile_const/compile_const_no_aux invocation gets a fresh
    // KernelCtx: kernel caches key on name-erased content addresses, so a
    // context surviving across blocks can replay a display name recorded
    // for an alias from an unrelated block into this block's synthesized
    // expressions — schedule-dependently, since which worker compiled what
    // first is a race (canonicity §10.5). Metadata display names must be a
    // deterministic function of the block, so no kernel-cache state may
    // outlive the block that populated it. The kenv is a pure cache
    // (`ensure_in_kenv` re-ingresses on demand), so starting cold is
    // semantics-free, and full clears at block boundaries measured at zero
    // wall-clock cost on Mathlib-scale envs.
    for _ in 0..num_threads {
      s.spawn(move || {
        loop {
          // Wait without holding a ready-queue lock or any block scratch.
          // A permit covers compilation, publication, and dependency release.
          let permit = match admission_ref.acquire() {
            Ok(Some(permit)) => permit,
            Ok(None) => return,
            Err(failure) => {
              error_ref.lock().unwrap().get_or_insert(failure);
              condvar_ref.notify_all();
              return;
            },
          };
          // Try to get work from the ready queue
          let work = {
            let mut queue = ready_queue_ref.lock().unwrap();
            queue.pop()
          };

          match work {
            Some(id) => {
              let block = &block_info_ref[id as usize];
              let (lo, all): (&Name, &NameSet) = (block.lo, block.all);
              // Check if we should stop due to error
              if error_ref.lock().unwrap().is_some() {
                return;
              }

              // Skip if already processed (prevents double-counting from
              // duplicate enqueuing)
              if processed_ref[id as usize].swap(true, AtomicOrdering::Relaxed)
              {
                continue;
              }

              // Track time for slow block detection
              let block_start = Instant::now();

              // Register as in-flight for the progress reporter. Remove on
              // every exit path (panic converted to error, graceful error,
              // success).
              active_ref.lock().unwrap().push((lo.clone(), block_start));

              if *IX_LOG_BLOCKS {
                eprintln!(
                  "[compile_env] BEGIN {} ({} members)",
                  lo.pretty(),
                  all.len()
                );
              }

              // Check if this block was pre-compiled into aux_name_to_addr.
              // Promote to name_to_addr without re-compiling.
              let _cc_start = Instant::now();
              let _is_precompiled = stt_ref.resolve_addr(lo).is_some();
              if _is_precompiled {
                // Check if any names in this block are aux_gen-rewritten.
                let any_aux_gen =
                  all.iter().any(|n| stt_ref.aux_gen_extra_names.contains(n));

                // Compile cross-SCC unresolved names FIRST so they're in
                // name_to_addr before compile_const_no_aux runs.
                // Only compile — don't promote other names yet (promote_aux
                // inside compile_const_no_aux needs names to still be in
                // aux_name_to_addr, not yet in name_to_addr).
                let mut aux_precompile_incomplete = false;
                {
                  let mut unresolved_names = Vec::new();
                  for name in all {
                    if stt_ref.name_to_addr.contains_key(name) {
                      continue;
                    }
                    if stt_ref.resolve_addr(name).is_some() {
                      // In aux_name_to_addr — will be promoted later.
                      continue;
                    }
                    unresolved_names.push(name.clone());
                  }
                  if !unresolved_names.is_empty() {
                    if any_aux_gen {
                      aux_precompile_incomplete = true;
                      let missing = unresolved_names
                        .iter()
                        .map(|n| n.pretty())
                        .collect::<Vec<_>>()
                        .join(", ");
                      let msg = format!(
                        "aux_gen precompile incomplete for {}; missing canonical aliases: {}",
                        lo.pretty(),
                        missing,
                      );
                      eprintln!(
                        "[compile_env] block FAILED {} ({} members): {}",
                        lo.pretty(),
                        all.len(),
                        msg,
                      );
                      for member in all {
                        stt_ref.ungrounded.insert(member.clone(), msg.clone());
                      }
                    } else {
                      let unresolved_set: NameSet =
                        unresolved_names.iter().cloned().collect();
                      let mut cache = BlockCache::default();
                      let cross_name = unresolved_names[0].clone();
                      let res = run_compile_catching_panic(
                        &cross_name,
                        "compile_const(cross-SCC)",
                        || {
                          compile_const(
                            &cross_name,
                            &unresolved_set,
                            lean_env,
                            &mut cache,
                            stt_ref,
                            &mut crate::compile::KernelCtx::new(),
                          )
                        },
                      );
                      if let Err(e) = res {
                        eprintln!(
                          "[compile_env] cross-SCC compile failed for {}: {}",
                          unresolved_names[0].pretty(),
                          e,
                        );
                        // Don't register failed names — downstream blocks
                        // will get MissingConstant rather than silently
                        // referencing broken data.
                      } else {
                        for name in &unresolved_names {
                          stt_ref.aux_gen_extra_names.insert(name.clone());
                        }
                        stt_ref
                          .aux_gen_pending
                          .lock()
                          .unwrap()
                          .extend(unresolved_names);
                      }
                    }
                  }
                }

                if any_aux_gen && !aux_precompile_incomplete {
                  // Compile the original Lean form (without aux_gen).
                  // compile_mutual with aux=false calls promote_aux for
                  // each constant, setting Named.original with the
                  // original (addr, meta) for decompilation roundtrip.
                  let mut orig_cache = BlockCache::default();
                  let res = run_compile_catching_panic(
                    lo,
                    "compile_const_no_aux",
                    || {
                      compile_const_no_aux(
                        lo,
                        all,
                        lean_env,
                        &mut orig_cache,
                        stt_ref,
                        &mut crate::compile::KernelCtx::new(),
                      )
                    },
                  );
                  if let Err(e) = res {
                    // Record the failure per-member and fall through. The
                    // scheduler keeps running so other constants can still
                    // compile; dependents of this block will hit
                    // MissingConstant and be recorded here too. Callers
                    // inspect `stt.ungrounded` to report per-constant
                    // compile-side rejections.
                    let msg = format!("{e}");
                    for member in all {
                      stt_ref.ungrounded.insert(member.clone(), msg.clone());
                    }
                    if *IX_LOG_BLOCKS {
                      eprintln!(
                        "[compile_env] compile_const_no_aux failed for {}: {}",
                        lo.pretty(),
                        msg,
                      );
                    }
                  }
                }

                if !aux_precompile_incomplete {
                  // Promote remaining names from aux_name_to_addr.
                  for name in all {
                    if stt_ref.name_to_addr.contains_key(name) {
                      continue;
                    }
                    if let Some(addr) = stt_ref.resolve_addr(name) {
                      stt_ref.name_to_addr.insert(name.clone(), addr);
                    }
                  }
                }
              } else {
                // Compile this block
                let mut cache = BlockCache::default();
                // The block's dependency names come from the reference
                // graph of its members' expressions; with the members
                // themselves they cover every constant the plan-head audit
                // can meet.
                cache.exempt_from_plan_audit(
                  stt_ref,
                  block.deps.iter().chain(all.iter()),
                );
                let res = run_compile_catching_panic(
                  lo,
                  "compile_const",
                  || {
                    compile_const(
                      lo,
                      all,
                      lean_env,
                      &mut cache,
                      stt_ref,
                      &mut crate::compile::KernelCtx::new(),
                    )
                  },
                );
                if let Err(e) = res {
                  // Record the failure per-member and fall through. The
                  // scheduler keeps running so other constants can still
                  // compile; dependents of this block will hit
                  // MissingConstant and be recorded here too. Callers
                  // inspect `stt.ungrounded` to report per-constant
                  // compile-side rejections.
                  let msg = format!("{e}");
                  for member in all {
                    stt_ref.ungrounded.insert(member.clone(), msg.clone());
                  }
                  // The first time we fail on a given block, log a brief
                  // line. Full dep-status diagnostics are gated on
                  // IX_LOG_BLOCKS to avoid log spam on cascading failures.
                  eprintln!(
                    "[compile_env] block FAILED {} ({} members): {}",
                    lo.pretty(),
                    all.len(),
                    msg,
                  );
                  if *IX_LOG_BLOCKS {
                    for member in all {
                      eprintln!("    member: {}", member.pretty());
                    }
                    if let CompileError::MissingConstant {
                      ref name,
                      ref caller,
                    } = e
                    {
                      eprintln!(
                        "[compile_env] MissingConstant: {name} (from {caller})"
                      );
                      for member in all {
                        let in_main = stt_ref.name_to_addr.contains_key(member);
                        let in_aux =
                          stt_ref.aux_name_to_addr.contains_key(member);
                        let in_ungr =
                          stt_ref.ungrounded.contains_key(member);
                        let status = if in_main {
                          "name_to_addr"
                        } else if in_aux {
                          "aux_name_to_addr"
                        } else if in_ungr {
                          "ungrounded"
                        } else {
                          "pending"
                        };
                        eprintln!("    {} [{}]", member.pretty(), status);
                      }
                      {
                        let orig_deps = block.deps;
                        eprintln!("  deps ({}):", orig_deps.len());
                        for d in orig_deps.iter() {
                          let in_main = stt_ref.name_to_addr.contains_key(d);
                          let in_aux = stt_ref.aux_name_to_addr.contains_key(d);
                          let in_ungr = stt_ref.ungrounded.contains_key(d);
                          let status = if in_main {
                            "name_to_addr"
                          } else if in_aux {
                            "aux_name_to_addr"
                          } else if in_ungr {
                            "ungrounded"
                          } else {
                            "UNRESOLVED"
                          };
                          eprintln!("    {} [{}]", d.pretty(), status);
                        }
                        let rem = reverse_deps_ref.unresolved(block.deps);
                        if !rem.is_empty() {
                          eprintln!("  unsatisfied ({}):", rem.len());
                          for d in rem {
                            eprintln!("    {}", d.pretty());
                          }
                        }
                      }
                    }
                  }
                }
              }

              // Block completed successfully: drop in-flight entry and
              // log to BEGIN/END if requested. Don't touch active_ref
              // after completed counter bump — if the reporter happens
              // to wake right after bump and before this cleanup, it
              // might show a completed block as in-flight, but the
              // numbers still reconcile on the next tick.
              active_ref.lock().unwrap().retain(|(n, _)| n != lo);

              // Check for slow blocks
              let elapsed = block_start.elapsed();
              if *crate::compile::IX_TIMING && elapsed.as_secs_f32() > 1.0 {
                let cc_time = _cc_start.elapsed().as_secs_f32();
                eprintln!(
                  "Slow block {:?} ({} consts): {:.2}s path={} cc={:.2}s",
                  lo.pretty(),
                  all.len(),
                  elapsed.as_secs_f32(),
                  if _is_precompiled { "precompiled" } else { "compile" },
                  cc_time,
                );
              }
              if *IX_LOG_BLOCKS {
                eprintln!(
                  "[compile_env] END   {} ({:.2}s)",
                  lo.pretty(),
                  elapsed.as_secs_f32(),
                );
              }

              // Collect newly-ready blocks by resolving this block's names.
              // Only a name's first resolution decrements its dependents,
              // so there is no double-decrement risk.
              let mut newly_ready = Vec::new();

              // For each name in this block, resolve deps
              for name in all {
                reverse_deps_ref.resolve(name, block_info_ref, &mut newly_ready);
              }

              // Drain pending aux_gen names and resolve their deps.
              // Only processes names added since the last drain, not the
              // full accumulated set (which is kept in aux_gen_extra_names
              // for persistent membership checks).
              {
                let extra: Vec<Name> =
                  std::mem::take(&mut *stt_ref.aux_gen_pending.lock().unwrap());
                for name in &extra {
                  reverse_deps_ref.resolve(
                    name,
                    block_info_ref,
                    &mut newly_ready,
                  );
                }
              }

              // Add newly-ready blocks to the queue and notify waiting workers
              if !newly_ready.is_empty() {
                let mut queue = ready_queue_ref.lock().unwrap();
                queue.extend(newly_ready);
                condvar_ref.notify_all();
              }

              let done = completed_ref.fetch_add(1, AtomicOrdering::SeqCst) + 1;
              // Wake all workers only when all blocks are done (so they
              // can exit), otherwise just wake one to avoid thundering herd.
              if done == total_blocks {
                condvar_ref.notify_all();
              } else {
                condvar_ref.notify_one();
              }
              permit.complete();

            },
            None => {
              drop(permit);
              // No work available - check if we're done
              if completed_ref.load(AtomicOrdering::SeqCst) == total_blocks {
                return;
              }
              // Check for errors
              if error_ref.lock().unwrap().is_some() {
                return;
              }
              // Wait for new work to become available
              let queue = ready_queue_ref.lock().unwrap();
              let _ = condvar_ref
                .wait_timeout(queue, Duration::from_millis(10))
                .unwrap();
            },
          }
        }
      });
    }

    // Wait for workers to drain, then stop the progress reporter. Scoped
    // threads join implicitly at the end of the scope, so we signal stop
    // before exiting — the reporter's sleep may keep it alive past worker
    // exit otherwise.
    //
    // Workers only exit via `None => ...` which requires either
    // all-completed or an error flag set, so by the time we reach here
    // (after the explicit join below), the scheduler is truly done.
    //
    // We can't `join()` scoped worker handles from outside their creation,
    // so instead we poll completion/error and only then stop progress.
    // The poll is cheap (one atomic + one mutex lock per iteration) and
    // bounded by the slowest worker.
    while completed_ref.load(AtomicOrdering::SeqCst) < total_blocks
      && error_ref.lock().unwrap().is_none()
    {
      if let Err(failure) = admission_ref.check() {
        error_ref.lock().unwrap().get_or_insert(failure);
        break;
      }
      thread::sleep(Duration::from_millis(25));
    }
    admission_ref.stop();
    stop_progress_ref.store(true, AtomicOrdering::Relaxed);
  });
  admission.check()?;

  if *IX_VERBOSE {
    let scheduler_elapsed = compile_start.elapsed().as_secs_f64();
    eprintln!(
      "[compile_env] scheduler drained: {}/{} blocks in {scheduler_elapsed:.1}s{}",
      completed.load(AtomicOrdering::SeqCst),
      total_blocks,
      crate::diag::rss_log_suffix(),
    );
  }

  // Check for errors
  if let Some(e) = error.into_inner().unwrap() {
    return Err(e);
  }

  // Verify completion
  let final_completed = completed.load(AtomicOrdering::SeqCst);
  if final_completed != total_blocks {
    // Find what's still blocked
    let mut blocked_count = 0;
    for block in &block_info {
      let deps = reverse_deps.unresolved(block.deps);
      if !deps.is_empty() {
        blocked_count += 1;
        if blocked_count <= 5 {
          eprintln!(
            "Still blocked: {:?} with {} deps remaining: {:?}",
            block.lo.pretty(),
            deps.len(),
            deps.iter().map(|n| n.pretty()).collect::<Vec<_>>()
          );
        }
      }
    }
    return Err(CompileError::InvalidMutualBlock {
      reason: "circular dependency or missing constant".into(),
    });
  }

  stt.finalize_hints();

  if !semantic_sources.is_empty() || profile.is_some() {
    if !stt.ungrounded.is_empty() {
      return Err(CompileError::UnsupportedExpr {
        desc: "resource compilation requires the complete requested closure"
          .into(),
      });
    }
    for source in &semantic_sources {
      if stt.aux_gen_extra_names.contains(source) {
        return Err(CompileError::UnsupportedExpr {
          desc: format!(
            "resource contract source was replaced by auxiliary generation: {}",
            source.pretty()
          ),
        });
      }
    }
    let default_profile;
    let profile = match profile {
      Some(profile) => profile,
      None => {
        default_profile = ix_kernel::resource::standard_profile(&stt.env);
        &default_profile
      },
    };
    ix_kernel::resource::validate(&stt.env, profile)
      .map_err(|desc| CompileError::UnsupportedExpr { desc })?;
  }

  if *IX_VERBOSE {
    let total_elapsed = compile_start.elapsed().as_secs_f64();
    eprintln!(
      "[compile_env] complete in {total_elapsed:.1}s · \
       env: {} consts, {} named, {} names, {} blobs, {} comms{}",
      stt.env.const_count(),
      stt.env.named_count(),
      stt.env.name_count(),
      stt.env.blob_count(),
      stt.env.comm_count(),
      crate::diag::rss_log_suffix(),
    );
  }

  Ok(stt)
}

/// A block of the scheduler, borrowed from the SCC condensation. Blocks are
/// identified by their index in the scheduler's block list (a `u32` in the
/// ready queue).
struct SchedBlock<'a> {
  /// The block's leader (its SCC representative).
  lo: &'a Name,
  /// The block's members.
  all: &'a NameSet,
  /// The names outside the block that its members reference.
  deps: &'a NameSet,
  /// How many of `deps` are not resolved yet; the block is ready at zero.
  remaining: AtomicUsize,
}

/// A dense index as stored in the scheduler's `u32` tables.
fn dense(i: usize) -> u32 {
  u32::try_from(i).expect("scheduler index exceeds u32")
}

/// The scheduler's reverse dependency index: for each member or dependency
/// name, the blocks that depend on it, and whether it has been resolved.
struct SchedDeps<'a> {
  /// Index of every member name and dependency name.
  ids: FxHashMap<&'a Name, u32>,
  /// `dependents[offsets[i]..offsets[i + 1]]` are the blocks that depend
  /// on name `i`, in block order.
  offsets: Vec<usize>,
  dependents: Vec<u32>,
  /// Whether name `i` has been resolved.
  resolved: Vec<AtomicBool>,
}

impl<'a> SchedDeps<'a> {
  fn new(blocks: &[SchedBlock<'a>]) -> Self {
    let n_members: usize = blocks.iter().map(|b| b.all.len()).sum();
    let mut ids: FxHashMap<&'a Name, u32> =
      FxHashMap::with_capacity_and_hasher(n_members, Default::default());
    for block in blocks {
      for name in block.all {
        let next = dense(ids.len());
        ids.entry(name).or_insert(next);
      }
    }
    // Every (dependency name, dependent block) edge as `name << 32 | block`.
    // A name without an index (`u32::MAX`) is outside every block, which
    // a dependency name, being a graph node, never is; such names get
    // indices too, and resolve exactly when they did with per-block name
    // sets (only if aux_gen queues them).
    let edge_list = |ids: &FxHashMap<&'a Name, u32>| -> Vec<u64> {
      blocks
        .par_iter()
        .enumerate()
        .flat_map_iter(|(b, block)| {
          let b = u64::from(dense(b));
          block.deps.iter().map(move |d| {
            (u64::from(ids.get(d).copied().unwrap_or(u32::MAX)) << 32) | b
          })
        })
        .collect()
    };
    let mut edges = edge_list(&ids);
    if edges.par_iter().any(|&e| e >> 32 == u64::from(u32::MAX)) {
      for block in blocks {
        for dep in block.deps {
          let next = dense(ids.len());
          ids.entry(dep).or_insert(next);
        }
      }
      edges = edge_list(&ids);
    }
    // Sorted by name, then block: the dependents of each name in block
    // order.
    edges.par_sort_unstable();
    let n_names = ids.len();
    let mut offsets = vec![0usize; n_names + 1];
    for &e in &edges {
      offsets[(e >> 32) as usize + 1] += 1;
    }
    for i in 0..n_names {
      offsets[i + 1] += offsets[i];
    }
    #[allow(clippy::cast_possible_truncation)]
    let dependents: Vec<u32> = edges.par_iter().map(|&e| e as u32).collect();
    drop(edges);
    let resolved = (0..n_names).map(|_| AtomicBool::new(false)).collect();
    SchedDeps { ids, offsets, dependents, resolved }
  }

  /// Resolve `name`: on its first resolution, count it off every block that
  /// depends on it and push the blocks that become ready onto
  /// `newly_ready`. Later resolutions of the same name do nothing.
  fn resolve(
    &self,
    name: &Name,
    blocks: &[SchedBlock<'_>],
    newly_ready: &mut Vec<u32>,
  ) {
    let Some(&i) = self.ids.get(name) else {
      return;
    };
    let i = i as usize;
    // The read-modify-writes below carry each releasing thread's work
    // (its compiled constants) to the thread that queues the dependent.
    if self.resolved[i].swap(true, AtomicOrdering::AcqRel) {
      return;
    }
    for &b in &self.dependents[self.offsets[i]..self.offsets[i + 1]] {
      if blocks[b as usize].remaining.fetch_sub(1, AtomicOrdering::AcqRel) == 1
      {
        newly_ready.push(b);
      }
    }
  }

  /// The names of `deps` not resolved yet, in `deps` iteration order.
  fn unresolved<'d>(&self, deps: &'d NameSet) -> Vec<&'d Name> {
    deps
      .iter()
      .filter(|d| {
        self.ids.get(*d).is_none_or(|&i| {
          !self.resolved[i as usize].load(AtomicOrdering::Acquire)
        })
      })
      .collect()
  }
}

/// Seed names for the aux_gen prereq closure.
///
/// These are the exact `Const` refs that `aux_gen` emits in generated
/// `.below` / `.brecOn` / `.brecOn.eq` bodies — grep for `mk_const` in
/// `src/ix/compile/aux_gen/**` to verify. They must all be compiled and
/// registered in `aux_name_to_addr` before any block's aux_gen runs, or
/// else `compile_expr` raises `MissingConstant`.
fn aux_gen_seed_names() -> Vec<Name> {
  let root = Name::anon();
  let eq = Name::str(root.clone(), "Eq".into());
  let heq = Name::str(root.clone(), "HEq".into());
  vec![
    // .below (Type-level): PUnit, PProd — ctors in same SCC
    Name::str(root.clone(), "PUnit".into()),
    Name::str(root.clone(), "PProd".into()),
    // .brecOn.eq — Eq family
    eq.clone(),
    Name::str(eq.clone(), "refl".into()),
    Name::str(eq.clone(), "symm".into()),
    Name::str(eq.clone(), "ndrec".into()),
    // `rfl` is a separate constant (`def rfl : a = a := Eq.refl a` in
    // Init.Prelude), used by `Eq.symm`'s body. The transitive-closure
    // walker should find it via Eq.symm's block_refs, but listing it
    // explicitly guards against ref-graph regressions.
    Name::str(root.clone(), "rfl".into()),
    // .brecOn.eq — HEq family
    heq.clone(),
    Name::str(heq, "refl".into()),
    // .brecOn.eq — heterogeneous-to-homogeneous coercion
    // (used in the indexed-eq path's major-continuation discharge)
    Name::str(root.clone(), "eq_of_heq".into()),
    // .brecOn.eq dummy motive
    Name::str(root, "True".into()),
  ]
}

/// Build the transitive SCC closure of `seeds` using `condensed.block_refs`,
/// then compile each SCC in **reverse topological order** (deps first) into
/// `aux_name_to_addr`. Fails immediately if any SCC fails to compile.
///
/// The reverse-topo order is computed via iterative DFS post-order on the
/// condensed graph. `block_refs` maps each SCC-rep to the names it
/// references; we resolve each referenced name back to its own SCC-rep via
/// `condensed.low_links`.
fn precompile_aux_gen_prereqs(
  condensed: &crate::condense::CondensedBlocks,
  lean_env: &Arc<LeanEnv>,
  stt: &CompileState,
) -> Result<(), CompileError> {
  // Resolve seeds to their SCC reps. Silently skip seeds not in the env
  // (unit-test fixtures, minimal test envs).
  let seed_reps: Vec<Name> = aux_gen_seed_names()
    .into_iter()
    .filter_map(|n| condensed.low_links.get(&n).cloned())
    .collect();

  if seed_reps.is_empty() {
    return Ok(());
  }

  // Iterative DFS post-order: visit each SCC exactly once, emitting after
  // all its dependencies have been emitted. Result is a reverse-topo
  // (dep-first) order.
  let mut order: Vec<Name> = Vec::new();
  let mut visited: FxHashSet<Name> = FxHashSet::default();

  enum Frame {
    Enter(Name),
    Exit(Name),
  }
  let mut stack: Vec<Frame> = seed_reps.into_iter().map(Frame::Enter).collect();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Enter(rep) => {
        if !visited.insert(rep.clone()) {
          continue;
        }
        // Push Exit *before* neighbor Enters so Exit fires after them.
        stack.push(Frame::Exit(rep.clone()));
        // Enqueue SCC deps (the external refs of this SCC, resolved to
        // their SCC reps).
        if let Some(out_refs) = condensed.block_refs.get(&rep) {
          for referenced in out_refs {
            if let Some(dep_rep) = condensed.low_links.get(referenced)
              && !visited.contains(dep_rep)
            {
              stack.push(Frame::Enter(dep_rep.clone()));
            }
          }
        }
      },
      Frame::Exit(rep) => {
        order.push(rep);
      },
    }
  }

  // Compile each SCC in dep-first order, moving compiled names to
  // `aux_name_to_addr` so later SCCs can resolve their Const refs.
  for rep in order {
    if stt.aux_name_to_addr.contains_key(&rep) {
      continue; // Already compiled (e.g., via a prior prereq run).
    }
    let all = match condensed.blocks.get(&rep) {
      Some(a) => a.clone(),
      None => continue,
    };
    let mut cache = BlockCache::default();
    let mut prereq_kctx = crate::compile::KernelCtx::new();
    compile_const(&rep, &all, lean_env, &mut cache, stt, &mut prereq_kctx)
      .map_err(|e| match e {
        // A sharing failure is about this block, not the dependency
        // order: keep its category (and the limit to raise) and name the
        // block.
        CompileError::ResourceLimit { reason } => CompileError::ResourceLimit {
          reason: format!("aux_gen prereq '{}': {reason}", rep.pretty()),
        },
        CompileError::SharingConstruction { reason } => {
          CompileError::SharingConstruction {
            reason: format!("aux_gen prereq '{}': {reason}", rep.pretty()),
          }
        },
        e => CompileError::InvalidMutualBlock {
          reason: format!(
            "aux_gen prereq pre-compile failed for SCC '{}' ({} members): \
             {:?}. The SCC closure is traversed in reverse-topological \
             order starting from the aux_gen seed names (see \
             `aux_gen_seed_names`), so all transitive deps *should* be \
             compiled before this — if you're hitting this, a dep \
             relationship isn't captured in the ref graph, or the source \
             env is inconsistent.",
            rep.pretty(),
            all.len(),
            e,
          ),
        },
      })?;
    // Move compiled names → aux_name_to_addr. The scheduler can still
    // re-encounter this SCC later; the entries will just be no-ops.
    let just_compiled: Vec<(Name, Address)> = stt
      .name_to_addr
      .iter()
      .map(|e| (e.key().clone(), e.value().clone()))
      .collect();
    for (n, addr) in just_compiled {
      stt.name_to_addr.remove(&n);
      stt.aux_name_to_addr.insert(n, addr);
    }
    // Defensive: move any aux_gen extras generated during pre-compile.
    let extras: Vec<Name> =
      stt.aux_gen_extra_names.iter().map(|r| r.clone()).collect();
    for name in extras {
      if let Some((n, addr)) = stt.name_to_addr.remove(&name) {
        stt.aux_name_to_addr.insert(n, addr);
      }
    }
  }

  Ok(())
}
