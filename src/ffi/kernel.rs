//! Kernel constant checking FFI.
//!
//! Exposes `rs_kernel_check_consts` (production, used by `lake exe ix check`
//! and `Tests/Ix/Kernel/Tutorial.lean`) plus a pair of test-only roundtrip
//! probes (`rs_kernel_roundtrip` / `rs_kernel_roundtrip_no_compile`).
//!
//! `rs_kernel_check_consts` runs the full pipeline `Lean env → Ixon compile
//! → kernel ingress → typecheck` against a batch of requested constant names.
//! Pipeline:
//!
//! 1. Decode the Lean environment into the Rust `Env` type.
//! 2. Run `compile_env` to obtain the Ixon environment.
//! 3. Run `ixon_ingress::<Meta>` to ingress into the kernel.
//! 4. For each requested name, construct a `TypeChecker` sharing the
//!    `Arc<KEnv>` (so whnf / infer / def_eq caches accumulate across the
//!    batch) and call `check_const`.
//! 5. Return a Lean `Array (Option CheckError)` reporting per-name
//!    results, where `some (.kernelException msg)` signals a rejection.
//!
//! The `CheckError` ABI (tag 0 = `kernelException`, tag 1 = `compileError`)
//! lives in `Ix/KernelCheck.lean`; see `KERNEL_EXCEPTION_TAG` below.
//!
//! The roundtrip helpers below `rs_kernel_check_consts` are test-only
//! (cfg-gated to `feature = "test-ffi"`) — they import `egress` /
//! `decompile_env` to compare against the original env, which is dead
//! weight in production builds.

use std::sync::{
  Arc, Mutex, OnceLock,
  atomic::{AtomicBool, AtomicUsize, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;

use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanCtor, LeanIOResult, LeanList,
  LeanOwned, LeanRef, LeanString,
};

use crate::ffi::lean_env::{decode_env, decode_name_array};
use crate::ix::compile::{CompileOptions, compile_env_with_options};
#[cfg(feature = "test-ffi")]
use crate::ix::decompile::decompile_env;
use crate::ix::env::Name;
#[cfg(feature = "test-ffi")]
use crate::ix::kernel::egress::{ixon_egress, lean_egress};
use crate::ix::kernel::env::KEnv;
use crate::ix::kernel::error::TcError;
use crate::ix::kernel::id::KId;
use crate::ix::kernel::ingress::ixon_ingress;
#[cfg(feature = "test-ffi")]
use crate::ix::kernel::ingress::lean_ingress;
use crate::ix::kernel::mode::Meta;
use crate::ix::kernel::tc::TypeChecker;

/// Lean-side `CheckError` constructor tags.
///
/// Defined in `Ix/KernelCheck.lean`:
/// ```lean
/// inductive CheckError where
///   | kernelException (msg : String)    -- tag 0
///   | compileError    (msg : String)    -- tag 1
///   deriving Repr
/// ```
/// Tags follow Lean's declaration order (top-to-bottom, starting at 0).
///
/// The second variant exists for two reasons: (1) to disambiguate compile-
/// side rejections from kernel-side rejections at the Lean call site, and
/// (2) to prevent Lean's LCNF "trivial structure" optimization from
/// elididing a single-ctor-single-field inductive into its field type
/// (`hasTrivialStructure?` in `Lean/Compiler/LCNF/MonoTypes.lean`). Without
/// that, the runtime representation of `CheckError` would be identical to
/// `String`, and the heap ctor we allocate here would be read as if it
/// were a string header — `INTERNAL PANIC: out of memory` on decode.
const KERNEL_EXCEPTION_TAG: u8 = 0;
const COMPILE_ERROR_TAG: u8 = 1;

/// FFI: type-check a batch of constants through the full pipeline.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_kernel_check_consts"]
/// opaque rsCheckConstsFFI :
///     @& List (Lean.Name × Lean.ConstantInfo) →
///     @& Array Lean.Name →
///     @& Array Bool →
///     @& Bool →
///     IO (Array (Option CheckError))
/// ```
///
/// Results come back in input order — the caller pairs each with its
/// `names[i]`. This was previously `Array (String × Option CheckError)`
/// with the Lean side round-tripping names through `Name.toString` (which
/// adds `«»` escaping for non-identifier components) and Rust reparsing
/// them back into a `Name`. That round-trip was brittle: Lean's escaped
/// `Lean.Order.«term_⊑_»` didn't match the kernel's unescaped
/// `Lean.Order.term_⊑_` key and logged `? not found`. Structural pass-
/// through via `decode_name_array` is the canonical form.
///
/// `expect_pass[i]` is a hint: `true` means "good" (checker expected to
/// accept), `false` means "bad" (checker expected to reject). It only
/// influences per-constant progress logging; the actual pass/fail logic
/// lives on the Lean side.
///
/// `quiet` toggles the progress-output style:
/// - `false` (verbose): every constant is printed with its elapsed time,
///   matching the original line-per-constant behaviour.
/// - `true` (ephemeral): the current `[i/N] name ...` label is written
///   over itself each iteration, and *only* slow constants (>=7s by default),
///   unexpected passes/failures, not-found names, and ungrounded compile
///   failures are promoted to persistent lines. Suitable for full-env
///   runs where the vast majority of constants are expected to pass
///   quickly.
///
/// Parallel quiet-mode progress is persistent and compiler-like: periodic
/// `done/total`, rate, ETA, and oldest in-flight constants. Useful knobs:
/// `IX_KERNEL_CHECK_PROGRESS_MS`, `IX_KERNEL_CHECK_SLOW_MS`,
/// `IX_KERNEL_CHECK_ACTIVE_SLOW_MS`, `IX_KERNEL_CHECK_INFLIGHT`, and
/// `IX_KERNEL_CHECK_NAME_CHARS`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_check_consts(
  env_consts: LeanList<LeanBorrowed<'_>>,
  names: LeanArray<LeanBorrowed<'_>>,
  expect_pass: LeanArray<LeanBorrowed<'_>>,
  quiet: LeanBool<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();
  let quiet = quiet.to_bool();

  // ---------------------------------------------------------------------
  // Decode inputs
  // ---------------------------------------------------------------------
  let t0 = Instant::now();
  let rust_env = decode_env(env_consts);
  // Decode names structurally — no `Name.toString` / `parse_name` dance.
  // The resulting `Name`s are byte-for-byte the same as the kernel's
  // stored names (same component strings, same content hash).
  let names_vec: Vec<Name> = decode_name_array(&names);
  // `Array Bool` elements are boxed tagged scalars:
  // `lean_box(n) = (n << 1) | 1`, so `Bool.false` has raw value 1 and
  // `Bool.true` has raw value 3. `unbox_usize()` (= `as_raw() >> 1`)
  // recovers the ctor tag (0 = false, 1 = true).
  let expect_pass_vec: Vec<bool> =
    expect_pass.map(|b| b.unbox_usize() == 1).into_iter().collect();
  eprintln!("[rs_kernel_check] read env:   {:>8.1?}", t0.elapsed());

  // ---------------------------------------------------------------------
  // Compile Lean → Ixon
  // ---------------------------------------------------------------------
  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let check_originals = expect_pass_vec.iter().any(|pass| !*pass);
  let compile_state = match compile_env_with_options(
    &rust_env_arc,
    CompileOptions { check_originals, ..Default::default() },
  ) {
    Ok(s) => s,
    Err(e) => {
      return build_uniform_error(names_vec.len(), &format!("[compile] {e:?}"));
    },
  };
  eprintln!("[rs_kernel_check] compile:    {:>8.1?}", t1.elapsed());

  // Snapshot per-constant compile failures (ill-formed inductives,
  // cascading MissingConstant, etc.) keyed by `Name` so the check loop
  // can skip the kernel and report them as compile-side rejections.
  // `compile_env` no longer aborts on per-block failure; it populates
  // `CompileState.ungrounded` and continues, letting good constants still
  // compile cleanly.
  let ungrounded: FxHashMap<Name, String> = compile_state
    .ungrounded
    .iter()
    .map(|e| (e.key().clone(), e.value().clone()))
    .collect();
  if !ungrounded.is_empty() {
    eprintln!(
      "[rs_kernel_check] {} constants failed to compile (will report as rejected without kernel check):",
      ungrounded.len()
    );
    // Sort for deterministic output — `FxHashMap` iteration order is
    // platform-defined. Sort by pretty-form once up front rather than in
    // the comparator to avoid repeated `format!` allocations.
    let mut ordered: Vec<(String, &String)> =
      ungrounded.iter().map(|(k, v)| (k.pretty(), v)).collect();
    ordered.sort_by(|a, b| a.0.cmp(&b.0));
    for (name, msg) in &ordered {
      // `msg` from `compile_env` can be multi-line; collapse internal
      // newlines so each constant occupies one log line.
      let flat = msg.replace('\n', " ");
      eprintln!("  [ungrounded] {name}: {flat}");
    }
  }

  // ---------------------------------------------------------------------
  // Ingress Ixon → kernel
  // ---------------------------------------------------------------------
  let t2 = Instant::now();
  let (mut kenv, intern) = match ixon_ingress::<Meta>(&compile_state.env) {
    Ok(v) => v,
    Err(msg) => {
      return build_uniform_error(names_vec.len(), &format!("[ingress] {msg}"));
    },
  };
  // FIXME: `ixon_ingress` returns a populated `InternTable` separately from
  // the fresh, empty one inside `KEnv::new()`. The TypeChecker reads
  // `env.intern`, so we have to swap. When ingress is refactored to populate
  // `kenv.intern` directly, this line goes away.
  kenv.intern = intern;
  eprintln!(
    "[rs_kernel_check] ingress:    {:>8.1?} ({} consts)",
    t2.elapsed(),
    kenv.len()
  );

  // Release decoded-env + compile state before the heavy check loop runs.
  drop(compile_state);
  drop(rust_env_arc);

  let kenv = Arc::new(kenv);

  // Build `Name → KId` map by iterating `kenv` itself. This guarantees we
  // look up by the exact KIds that ingress inserted, sidestepping any
  // risk of reconstruction mismatch (e.g. Muts-block member naming vs
  // `named` map keys). Keyed by `Name` directly (hash-based equality)
  // rather than by `format!("{}", name)` — pure structural lookup.
  let mut name_to_id: FxHashMap<Name, KId<Meta>> = FxHashMap::default();
  for (kid, _kconst) in kenv.iter() {
    name_to_id.insert(kid.name.clone(), kid);
  }
  let total = names_vec.len();
  let t3 = Instant::now();

  // ---------------------------------------------------------------------
  // Per-constant checking on a 256 MB stack
  // ---------------------------------------------------------------------
  // Deep recursor expansions push the Rust stack. A dedicated thread with a
  // large stack matches the old ix_old pattern.
  let results = match run_checks_on_large_stack(
    kenv.clone(),
    name_to_id,
    names_vec.clone(),
    expect_pass_vec,
    ungrounded,
    quiet,
  ) {
    Ok(r) => r,
    Err(msg) => {
      return build_uniform_error(names_vec.len(), &format!("[thread] {msg}"));
    },
  };

  let passed = results.iter().filter(|r| r.is_ok()).count();
  let failed = results.iter().filter(|r| r.is_err()).count();
  eprintln!(
    "[rs_kernel_check] {passed}/{total} passed, {failed} failed ({:.1?})",
    t3.elapsed()
  );
  eprintln!("[rs_kernel_check] total:      {:>8.1?}", total_start.elapsed());

  build_result_array(&results)
}

// =============================================================================
// Checking runners (large-stack workers)
// =============================================================================

/// Kind of per-constant error — selects which `CheckError` ctor to build on
/// the Lean side. See tag constants at the top of the module.
#[derive(Clone, Copy)]
enum ErrKind {
  Kernel,
  Compile,
}

impl ErrKind {
  fn tag(self) -> u8 {
    match self {
      ErrKind::Kernel => KERNEL_EXCEPTION_TAG,
      ErrKind::Compile => COMPILE_ERROR_TAG,
    }
  }
}

/// Per-constant result: `Ok(())` on pass, `Err((kind, msg))` on rejection.
type CheckRes = Result<(), (ErrKind, String)>;

const KERNEL_CHECK_STACK_SIZE: usize = 256 * 1024 * 1024;

fn run_checks_on_large_stack(
  kenv: Arc<KEnv<Meta>>,
  name_to_id: FxHashMap<Name, KId<Meta>>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  quiet: bool,
) -> Result<Vec<CheckRes>, String> {
  if names.is_empty() {
    eprintln!("[rs_kernel_check] checking 0 constants...");
    return Ok(Vec::new());
  }

  let worker_count = resolve_kernel_check_workers(names.len(), quiet);
  if worker_count == 1 {
    eprintln!("[rs_kernel_check] checking {} constants...", names.len());
    return run_checks_serial_on_large_stack(
      kenv,
      name_to_id,
      names,
      expect_pass,
      ungrounded,
      quiet,
    );
  }

  run_checks_parallel_on_large_stacks(
    kenv,
    name_to_id,
    names,
    expect_pass,
    ungrounded,
    quiet,
    worker_count,
  )
}

fn run_checks_serial_on_large_stack(
  kenv: Arc<KEnv<Meta>>,
  name_to_id: FxHashMap<Name, KId<Meta>>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  quiet: bool,
) -> Result<Vec<CheckRes>, String> {
  thread::Builder::new()
    .stack_size(KERNEL_CHECK_STACK_SIZE)
    .spawn(move || {
      check_consts_loop(kenv, name_to_id, names, expect_pass, ungrounded, quiet)
    })
    .map_err(|e| format!("failed to spawn kernel-check thread: {e}"))?
    .join()
    .map_err(|_| "kernel-check thread panicked".to_string())
}

fn run_checks_parallel_on_large_stacks(
  kenv: Arc<KEnv<Meta>>,
  name_to_id: FxHashMap<Name, KId<Meta>>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  quiet: bool,
  worker_count: usize,
) -> Result<Vec<CheckRes>, String> {
  let total = names.len();
  eprintln!(
    "[rs_kernel_check] checking {total} constants with {worker_count} workers..."
  );

  let name_to_id = Arc::new(name_to_id);
  let names = Arc::new(names);
  let expect_pass = Arc::new(expect_pass);
  let ungrounded = Arc::new(ungrounded);
  let tasks = Arc::new(build_parallel_check_tasks(
    &kenv,
    &name_to_id,
    &names,
    &ungrounded,
  ));
  let next_task = Arc::new(AtomicUsize::new(0));
  let results: Arc<Vec<OnceLock<CheckRes>>> =
    Arc::new((0..total).map(|_| OnceLock::new()).collect());
  let progress = Arc::new(ParallelProgress::new(total, worker_count, quiet));
  let mut reporter = ParallelProgress::spawn_reporter(Arc::clone(&progress));

  let mut handles: Vec<thread::JoinHandle<()>> =
    Vec::with_capacity(worker_count);
  for worker_idx in 0..worker_count {
    let kenv = Arc::clone(&kenv);
    let name_to_id = Arc::clone(&name_to_id);
    let names = Arc::clone(&names);
    let expect_pass = Arc::clone(&expect_pass);
    let ungrounded = Arc::clone(&ungrounded);
    let tasks = Arc::clone(&tasks);
    let next_task = Arc::clone(&next_task);
    let results = Arc::clone(&results);
    let progress_worker = Arc::clone(&progress);

    let handle = match thread::Builder::new()
      .name(format!("ix-kernel-check-{worker_idx}"))
      .stack_size(KERNEL_CHECK_STACK_SIZE)
      .spawn(move || {
        loop {
          let task_idx = next_task.fetch_add(1, Ordering::Relaxed);
          let Some(task) = tasks.get(task_idx) else {
            break;
          };

          for outcome in check_task(
            task,
            total,
            &kenv,
            name_to_id.as_ref(),
            names.as_slice(),
            expect_pass.as_slice(),
            ungrounded.as_ref(),
            |prefix| progress_worker.begin(worker_idx, prefix),
          ) {
            progress_worker.finish(worker_idx, &outcome);
            let _ = results[outcome.index].set(outcome.result);
          }
        }
      }) {
      Ok(handle) => handle,
      Err(e) => {
        progress.stop_reporter();
        if let Some(reporter) = reporter.take() {
          let _ = reporter.join();
        }
        for handle in handles {
          let _ = handle.join();
        }
        return Err(format!("failed to spawn kernel-check worker: {e}"));
      },
    };
    handles.push(handle);
  }

  let mut panicked = false;
  for handle in handles {
    if handle.join().is_err() {
      panicked = true;
    }
  }
  progress.stop_reporter();
  if let Some(reporter) = reporter {
    let _ = reporter.join();
  }
  if panicked {
    return Err("kernel-check worker panicked".to_string());
  }

  let mut ordered = Vec::with_capacity(total);
  for i in 0..total {
    match results[i].get() {
      Some(result) => ordered.push(result.clone()),
      None => {
        return Err(format!("kernel-check worker missed result index {i}"));
      },
    }
  }
  Ok(ordered)
}

#[derive(Clone, Debug)]
enum CheckTask {
  Standalone { index: usize },
  Block { indices: Vec<usize> },
}

fn build_parallel_check_tasks(
  kenv: &Arc<KEnv<Meta>>,
  name_to_id: &FxHashMap<Name, KId<Meta>>,
  names: &[Name],
  ungrounded: &FxHashMap<Name, String>,
) -> Vec<CheckTask> {
  // Collapse requested members of a coordinated kernel block into one work
  // unit. The owner checks the block once and later emits per-request results.
  let mut tasks = Vec::with_capacity(names.len());
  let mut block_tasks: FxHashMap<KId<Meta>, usize> = FxHashMap::default();
  let tc = TypeChecker::new(kenv.clone());

  for (index, name) in names.iter().enumerate() {
    if ungrounded.contains_key(name) {
      tasks.push(CheckTask::Standalone { index });
      continue;
    }

    let Some(kid) = name_to_id.get(name) else {
      tasks.push(CheckTask::Standalone { index });
      continue;
    };

    let Some(block) = tc.coordinated_check_block_for_const(kid) else {
      tasks.push(CheckTask::Standalone { index });
      continue;
    };

    if let Some(task_index) = block_tasks.get(&block).copied() {
      match &mut tasks[task_index] {
        CheckTask::Block { indices } => indices.push(index),
        CheckTask::Standalone { .. } => unreachable!(
          "block task index must refer to a block-shaped check task"
        ),
      }
    } else {
      block_tasks.insert(block, tasks.len());
      tasks.push(CheckTask::Block { indices: vec![index] });
    }
  }

  tasks
}

fn resolve_kernel_check_workers(total: usize, quiet: bool) -> usize {
  let env_workers = std::env::var("IX_KERNEL_CHECK_WORKERS").ok();
  let no_par = std::env::var("IX_NO_PAR").ok().as_deref() == Some("1");
  let available = thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
  resolve_kernel_check_workers_from(
    total,
    quiet,
    env_workers.as_deref(),
    no_par,
    available,
  )
}

fn resolve_kernel_check_workers_from(
  total: usize,
  quiet: bool,
  env_workers: Option<&str>,
  no_par: bool,
  available_parallelism: usize,
) -> usize {
  if let Some(n) =
    env_workers.and_then(|s| s.parse::<usize>().ok()).filter(|&n| n > 0)
  {
    return n;
  }
  if no_par || !quiet {
    return 1;
  }
  if total == 0 { 1 } else { available_parallelism.max(1).min(total) }
}

#[cfg(test)]
mod tests {
  use super::{compact_in_flight_label, resolve_kernel_check_workers_from};

  #[test]
  fn explicit_kernel_check_workers_wins_when_positive() {
    assert_eq!(
      resolve_kernel_check_workers_from(3, false, Some("8"), true, 2),
      8
    );
  }

  #[test]
  fn zero_or_invalid_worker_override_falls_through() {
    assert_eq!(
      resolve_kernel_check_workers_from(10, true, Some("0"), false, 4),
      4
    );
    assert_eq!(
      resolve_kernel_check_workers_from(10, true, Some("nope"), false, 4),
      4
    );
  }

  #[test]
  fn no_par_and_verbose_force_serial_without_override() {
    assert_eq!(resolve_kernel_check_workers_from(10, true, None, true, 4), 1);
    assert_eq!(resolve_kernel_check_workers_from(10, false, None, false, 4), 1);
  }

  #[test]
  fn default_parallelism_is_clamped_to_total() {
    assert_eq!(resolve_kernel_check_workers_from(3, true, None, false, 16), 3);
    assert_eq!(resolve_kernel_check_workers_from(10, true, None, false, 0), 1);
    assert_eq!(resolve_kernel_check_workers_from(0, true, None, false, 16), 1);
  }

  #[test]
  fn compact_in_flight_label_preserves_index_and_tail() {
    let label =
      "[123/456] _private.Std.Tactic.BVDecide.LRAT.Internal.Formula.Proof";
    let compact = compact_in_flight_label(label, 40);
    assert!(compact.starts_with("[123/456] ..."));
    assert!(compact.ends_with("Internal.Formula.Proof"));
    assert!(compact.chars().count() <= 40);
  }

  #[test]
  fn compact_in_flight_label_handles_tiny_limits() {
    assert_eq!(compact_in_flight_label("[1/2] Very.Long.Name", 0), "");
    assert_eq!(compact_in_flight_label("[1/2] Very.Long.Name", 2), "[1");
  }
}

/// Default threshold at and above which a completed check is "slow" enough to
/// keep a persistent line in quiet mode. Override with
/// `IX_KERNEL_CHECK_SLOW_MS`.
const DEFAULT_SLOW_THRESHOLD: Duration = Duration::from_secs(7);

/// Default threshold for a one-shot "still checking ..." line when an active
/// parallel check has been in-flight for a long time. Override with
/// `IX_KERNEL_CHECK_ACTIVE_SLOW_MS`; set it to `0` to disable the notice.
const DEFAULT_ACTIVE_SLOW_THRESHOLD: Duration = Duration::from_secs(30);

const DEFAULT_IN_FLIGHT_LIMIT: usize = 3;
const DEFAULT_IN_FLIGHT_LABEL_CHARS: usize = 120;

fn env_duration_ms(var: &str, default: Duration) -> Duration {
  std::env::var(var)
    .ok()
    .and_then(|s| s.parse::<u64>().ok())
    .map(Duration::from_millis)
    .unwrap_or(default)
}

fn env_duration_ms_optional(var: &str, default: Duration) -> Option<Duration> {
  let ms = std::env::var(var)
    .ok()
    .and_then(|s| s.parse::<u64>().ok())
    .unwrap_or(default.as_millis() as u64);
  if ms == 0 { None } else { Some(Duration::from_millis(ms)) }
}

fn env_usize(var: &str, default: usize) -> usize {
  std::env::var(var)
    .ok()
    .and_then(|s| s.parse::<usize>().ok())
    .unwrap_or(default)
}

fn kernel_check_slow_threshold() -> Duration {
  env_duration_ms("IX_KERNEL_CHECK_SLOW_MS", DEFAULT_SLOW_THRESHOLD)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CheckStatus {
  Checked,
  CompileFailed,
  NotFound,
}

#[derive(Clone)]
struct CheckOutcome {
  index: usize,
  total: usize,
  display: String,
  should_pass: bool,
  result: CheckRes,
  status: CheckStatus,
  elapsed: Option<Duration>,
  peak: Option<u32>,
}

impl CheckOutcome {
  fn prefix(&self) -> String {
    format!("  [{}/{}] {}", self.index + 1, self.total, self.display)
  }

  fn err_msg(&self) -> &str {
    match &self.result {
      Ok(()) => "",
      Err((_kind, msg)) => msg,
    }
  }

  fn is_expected(&self) -> bool {
    self.result.is_ok() == self.should_pass
  }

  fn is_slow(&self, slow_threshold: Duration) -> bool {
    self.elapsed.is_some_and(|elapsed| elapsed >= slow_threshold)
  }

  fn checked_suffix(&self, slow_threshold: Duration) -> String {
    let elapsed = self.elapsed.unwrap_or_default();
    let peak = self.peak.unwrap_or_default();
    let suffix = match (&self.result, self.should_pass) {
      (Ok(()), true) => format!("ok ({elapsed:.1?}, depth={peak})"),
      (Ok(()), false) => {
        format!("UNEXPECTED PASS ({elapsed:.1?}, depth={peak})")
      },
      (Err((_kind, msg)), false) => {
        format!("REJECTED ({elapsed:.1?}): {msg}")
      },
      (Err((_kind, msg)), true) => {
        format!("FAIL ({elapsed:.1?}, depth={peak}): {msg}")
      },
    };

    if self.is_slow(slow_threshold) && self.is_expected() {
      format!("{suffix} [slow]")
    } else {
      suffix
    }
  }
}

fn check_one_const<F>(
  i: usize,
  total: usize,
  kenv: &Arc<KEnv<Meta>>,
  name_to_id: &FxHashMap<Name, KId<Meta>>,
  names: &[Name],
  expect_pass: &[bool],
  ungrounded: &FxHashMap<Name, String>,
  mut before_kernel_check: F,
) -> CheckOutcome
where
  F: FnMut(&str),
{
  let name = &names[i];
  let should_pass = expect_pass.get(i).copied().unwrap_or(true);
  let display = name.pretty();

  if let Some(msg) = ungrounded.get(name) {
    return CheckOutcome {
      index: i,
      total,
      display,
      should_pass,
      result: Err((ErrKind::Compile, msg.clone())),
      status: CheckStatus::CompileFailed,
      elapsed: None,
      peak: None,
    };
  }

  let kid = match name_to_id.get(name) {
    Some(id) => id.clone(),
    None => {
      return CheckOutcome {
        index: i,
        total,
        display: display.clone(),
        should_pass,
        result: Err((ErrKind::Kernel, format!("not found: {display}"))),
        status: CheckStatus::NotFound,
        elapsed: None,
        peak: None,
      };
    },
  };

  let prefix = format!("  [{}/{}] {display}", i + 1, total);
  before_kernel_check(&prefix);

  let tc_start = Instant::now();
  let mut tc = TypeChecker::new(kenv.clone());
  tc.set_debug_label(display.clone());
  let result: Result<(), String> =
    tc.check_const(&kid).map_err(|e| format_tc_error(&e));
  let elapsed = tc_start.elapsed();
  let peak = tc.def_eq_peak;

  CheckOutcome {
    index: i,
    total,
    display,
    should_pass,
    result: result.map_err(|msg| (ErrKind::Kernel, msg)),
    status: CheckStatus::Checked,
    elapsed: Some(elapsed),
    peak: Some(peak),
  }
}

fn check_task<F>(
  task: &CheckTask,
  total: usize,
  kenv: &Arc<KEnv<Meta>>,
  name_to_id: &FxHashMap<Name, KId<Meta>>,
  names: &[Name],
  expect_pass: &[bool],
  ungrounded: &FxHashMap<Name, String>,
  before_kernel_check: F,
) -> Vec<CheckOutcome>
where
  F: FnMut(&str),
{
  match task {
    CheckTask::Standalone { index } => {
      vec![check_one_const(
        *index,
        total,
        kenv,
        name_to_id,
        names,
        expect_pass,
        ungrounded,
        before_kernel_check,
      )]
    },
    CheckTask::Block { indices } => {
      let Some((&owner_index, rest)) = indices.split_first() else {
        return Vec::new();
      };
      let owner = check_one_const(
        owner_index,
        total,
        kenv,
        name_to_id,
        names,
        expect_pass,
        ungrounded,
        before_kernel_check,
      );
      let mut outcomes = Vec::with_capacity(indices.len());
      outcomes.push(owner.clone());
      for index in rest {
        outcomes.push(block_member_outcome(
          *index,
          total,
          names,
          expect_pass,
          &owner,
        ));
      }
      outcomes
    },
  }
}

fn block_member_outcome(
  index: usize,
  total: usize,
  names: &[Name],
  expect_pass: &[bool],
  owner: &CheckOutcome,
) -> CheckOutcome {
  CheckOutcome {
    index,
    total,
    display: names[index].pretty(),
    should_pass: expect_pass.get(index).copied().unwrap_or(true),
    result: owner.result.clone(),
    status: CheckStatus::Checked,
    elapsed: owner.elapsed,
    peak: owner.peak,
  }
}

fn check_consts_loop(
  kenv: Arc<KEnv<Meta>>,
  name_to_id: FxHashMap<Name, KId<Meta>>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  quiet: bool,
) -> Vec<CheckRes> {
  let total = names.len();
  let mut results: Vec<CheckRes> = Vec::with_capacity(total);
  let slow_threshold = kernel_check_slow_threshold();

  // Terminal width is only needed for ephemeral clearing in quiet mode. In
  // verbose mode we never rewrite, so the value is ignored.
  let mut progress = Progress::new(quiet);

  for i in 0..total {
    let outcome = check_one_const(
      i,
      total,
      &kenv,
      &name_to_id,
      &names,
      &expect_pass,
      &ungrounded,
      |prefix| progress.start(prefix),
    );
    let prefix = outcome.prefix();

    match outcome.status {
      CheckStatus::CompileFailed => {
        // Unexpected compile failure (should_pass=true) is a real problem and
        // must persist. Expected rejections (should_pass=false) only persist in
        // verbose mode; quiet mode drops them since they're part of the
        // tutorial's bad-constant coverage, not user-visible failures.
        if outcome.should_pass {
          progress.persist(&format!(
            "{prefix} ... FAIL (compile): {}",
            outcome.err_msg()
          ));
        } else if !quiet {
          progress.persist(&format!(
            "{prefix} ... REJECTED (compile): {}",
            outcome.err_msg()
          ));
        }
      },
      CheckStatus::NotFound => {
        // Not-found is always unexpected — the Lean side asked for a name
        // that compile+ingress didn't produce. Always persist.
        progress.persist(&format!("{prefix} ? not found"));
      },
      CheckStatus::Checked => {
        // Outcomes that must persist in quiet mode:
        //   - Unexpected pass / unexpected failure: user cares about these.
        //   - Slow runs with the expected outcome: useful for bisecting perf.
        //
        // Fast runs with the expected outcome stay ephemeral and are
        // overwritten on the next iteration.
        let must_persist =
          !outcome.is_expected() || outcome.is_slow(slow_threshold);
        progress.finish(
          &prefix,
          &outcome.checked_suffix(slow_threshold),
          must_persist,
        );
      },
    }

    results.push(outcome.result);
  }

  // Clear any trailing ephemeral label before the summary lines print.
  progress.flush();

  results
}

// =============================================================================
// Parallel progress output
// =============================================================================

struct InFlightCheck {
  label: String,
  started: Instant,
  reported_active_slow: bool,
}

struct ParallelProgress {
  total: usize,
  quiet: bool,
  started: Instant,
  slow_threshold: Duration,
  active_slow_threshold: Option<Duration>,
  in_flight_limit: usize,
  in_flight_label_chars: usize,
  done: AtomicUsize,
  active: Mutex<Vec<Option<InFlightCheck>>>,
  stop: AtomicBool,
  print_lock: Mutex<()>,
}

impl ParallelProgress {
  fn new(total: usize, worker_count: usize, quiet: bool) -> Self {
    let active = std::iter::repeat_with(|| None).take(worker_count).collect();
    Self {
      total,
      quiet,
      started: Instant::now(),
      slow_threshold: kernel_check_slow_threshold(),
      active_slow_threshold: env_duration_ms_optional(
        "IX_KERNEL_CHECK_ACTIVE_SLOW_MS",
        DEFAULT_ACTIVE_SLOW_THRESHOLD,
      ),
      in_flight_limit: env_usize(
        "IX_KERNEL_CHECK_INFLIGHT",
        DEFAULT_IN_FLIGHT_LIMIT,
      ),
      in_flight_label_chars: env_usize(
        "IX_KERNEL_CHECK_NAME_CHARS",
        DEFAULT_IN_FLIGHT_LABEL_CHARS,
      ),
      done: AtomicUsize::new(0),
      active: Mutex::new(active),
      stop: AtomicBool::new(false),
      print_lock: Mutex::new(()),
    }
  }

  fn spawn_reporter(progress: Arc<Self>) -> Option<thread::JoinHandle<()>> {
    let interval = kernel_check_progress_interval()?;
    Some(thread::spawn(move || {
      let check_interval = interval.min(Duration::from_millis(250));
      let mut last_print = Instant::now();
      while !progress.stop.load(Ordering::Relaxed) {
        thread::sleep(check_interval);
        if progress.stop.load(Ordering::Relaxed) {
          break;
        }
        if last_print.elapsed() < interval {
          continue;
        }
        last_print = Instant::now();
        progress.report();
      }
    }))
  }

  fn begin(&self, worker_idx: usize, prefix: &str) {
    if let Some(slot) = self.active.lock().unwrap().get_mut(worker_idx) {
      *slot = Some(InFlightCheck {
        label: prefix.trim().to_string(),
        started: Instant::now(),
        reported_active_slow: false,
      });
    }
  }

  fn finish(&self, worker_idx: usize, outcome: &CheckOutcome) {
    if let Some(slot) = self.active.lock().unwrap().get_mut(worker_idx) {
      *slot = None;
    }
    self.done.fetch_add(1, Ordering::SeqCst);
    if let Some(line) = self.persistent_line(outcome) {
      self.log(&line);
    }
  }

  fn stop_reporter(&self) {
    self.stop.store(true, Ordering::Relaxed);
  }

  fn persistent_line(&self, outcome: &CheckOutcome) -> Option<String> {
    let prefix = outcome.prefix();
    match outcome.status {
      CheckStatus::CompileFailed => {
        let label = if outcome.should_pass {
          "FAIL (compile)"
        } else {
          "REJECTED (compile)"
        };
        Some(format!("{prefix} ... {label}: {}", outcome.err_msg()))
      },
      CheckStatus::NotFound => Some(format!("{prefix} ? not found")),
      CheckStatus::Checked => {
        let must_persist = !self.quiet
          || !outcome.is_expected()
          || outcome.is_slow(self.slow_threshold);
        if must_persist {
          Some(format!(
            "{prefix} ... {}",
            outcome.checked_suffix(self.slow_threshold)
          ))
        } else {
          None
        }
      },
    }
  }

  fn report(&self) {
    let done = self.done.load(Ordering::SeqCst);
    let pct = if self.total == 0 {
      100.0
    } else {
      (done as f64 / self.total as f64) * 100.0
    };
    let elapsed = self.started.elapsed().as_secs_f64();
    let rate = if elapsed > 0.0 { done as f64 / elapsed } else { 0.0 };
    let eta = if rate > 0.0 && done < self.total {
      format!(" · eta {:.0}s", (self.total - done) as f64 / rate)
    } else {
      String::new()
    };

    let (in_flight, active_slow_lines) = {
      let mut active = self.active.lock().unwrap();
      let mut active_slow_lines = Vec::new();
      if let Some(active_slow_threshold) = self.active_slow_threshold {
        for slot in active.iter_mut() {
          if let Some(check) = slot.as_mut() {
            let age = check.started.elapsed();
            if !check.reported_active_slow && age >= active_slow_threshold {
              check.reported_active_slow = true;
              active_slow_lines.push(format!(
                "[rs_kernel_check] still checking {} after {:.0}s",
                compact_in_flight_label(
                  &check.label,
                  self.in_flight_label_chars
                ),
                age.as_secs_f64()
              ));
            }
          }
        }
      }

      let mut entries: Vec<_> = active
        .iter()
        .filter_map(|slot| {
          slot.as_ref().map(|check| (check.started, check.label.clone()))
        })
        .collect();
      entries.sort_by_key(|(started, _)| *started);
      let in_flight = entries
        .into_iter()
        .take(self.in_flight_limit)
        .map(|(started, label)| {
          format!(
            "{} ({:.0}s)",
            compact_in_flight_label(&label, self.in_flight_label_chars),
            started.elapsed().as_secs_f64()
          )
        })
        .collect::<Vec<_>>();
      (in_flight, active_slow_lines)
    };
    let active_suffix = if in_flight.is_empty() {
      String::new()
    } else {
      format!(" · in-flight: {}", in_flight.join(", "))
    };

    self.log(&format!(
      "[rs_kernel_check] {done}/{} ({pct:.1}%) · {:.1}/s · elapsed {:.0}s{eta}{active_suffix}",
      self.total,
      rate,
      elapsed,
    ));
    for line in active_slow_lines {
      self.log(&line);
    }
  }

  fn log(&self, line: &str) {
    let _guard = self.print_lock.lock().unwrap();
    eprintln!("{line}");
  }
}

fn kernel_check_progress_interval() -> Option<Duration> {
  let ms = std::env::var("IX_KERNEL_CHECK_PROGRESS_MS")
    .ok()
    .or_else(|| std::env::var("IX_PROGRESS_MS").ok())
    .and_then(|s| s.parse::<u64>().ok())
    .unwrap_or(2000);
  if ms == 0 { None } else { Some(Duration::from_millis(ms)) }
}

fn compact_in_flight_label(label: &str, max_chars: usize) -> String {
  if max_chars == 0 {
    return String::new();
  }

  let label = label.trim();
  if label.chars().count() <= max_chars {
    return label.to_string();
  }

  const ELLIPSIS: &str = "...";
  if max_chars <= ELLIPSIS.len() {
    return label.chars().take(max_chars).collect();
  }

  if let Some((head, tail)) = label.split_once("] ") {
    let head = format!("{head}] ");
    let head_chars = head.chars().count();
    if head_chars + ELLIPSIS.len() < max_chars {
      let tail_chars = max_chars - head_chars - ELLIPSIS.len();
      return format!("{head}{ELLIPSIS}{}", last_chars(tail, tail_chars));
    }
  }

  format!("{ELLIPSIS}{}", last_chars(label, max_chars - ELLIPSIS.len()))
}

fn last_chars(s: &str, count: usize) -> String {
  let chars: Vec<char> = s.chars().collect();
  if chars.len() <= count {
    return s.to_string();
  }
  chars[chars.len() - count..].iter().collect()
}

// =============================================================================
// Progress output (ephemeral + verbose)
// =============================================================================
//
// Quiet mode rewrites the "[i/N] name ..." line in place and only promotes a
// constant to a persistent log line when it's slow, unexpected, or otherwise
// interesting. Verbose mode keeps the original behaviour: every constant
// lives on its own line.
//
// The ANSI escape sequences used are a minimal subset supported by every
// terminal the test suite has been exercised on:
//   \x1b[2K — clear entire current line
//   \x1b[A  — move cursor up one line
//   \r      — move cursor to column 0
//
// Ported from ix_old's `rs_zero_check_env_impl` (see
// `ix_old/src/lean/ffi/check.rs` around line 1798).

/// Progress reporter used by `check_consts_loop`. In verbose mode it simply
/// emits one line per constant; in quiet mode it rewrites the current line in
/// place and persists only the ones we explicitly ask it to.
struct Progress {
  quiet: bool,
  term_cols: usize,
  /// Number of terminal lines the current ephemeral label occupies. Zero
  /// means there's nothing to clear on the next `start`/`persist`.
  ephemeral_lines: usize,
}

impl Progress {
  fn new(quiet: bool) -> Self {
    let term_cols = if quiet { term_cols_stderr() } else { 0 };
    Self { quiet, term_cols, ephemeral_lines: 0 }
  }

  /// Begin the progress indicator for a new constant. Quiet mode writes
  /// `{prefix} ...` as an ephemeral label; verbose mode writes it as the
  /// start of a line that will be completed by `finish`.
  fn start(&mut self, prefix: &str) {
    if self.quiet {
      self.clear_ephemeral();
      let label = format!("{prefix} ...");
      eprint!("{label}");
      self.ephemeral_lines = lines_occupied(&label, self.term_cols);
    } else {
      eprint!("{prefix} ... ");
    }
  }

  /// Complete the current constant's progress line. `persist=true` always
  /// prints a `{prefix} ... {suffix}` line; `persist=false` means quiet mode
  /// leaves the ephemeral label to be overwritten on the next `start`.
  /// Verbose mode always prints the suffix (continuing the line `start`
  /// opened).
  fn finish(&mut self, prefix: &str, suffix: &str, persist: bool) {
    if self.quiet {
      if persist {
        self.clear_ephemeral();
        eprintln!("{prefix} ... {suffix}");
      }
      // else: ephemeral label stays, overwritten on next `start`
    } else {
      eprintln!("{suffix}");
    }
  }

  /// Print a persistent line that is NOT preceded by a `start`, e.g. the
  /// not-found / ungrounded branches where we don't call `check_const`.
  fn persist(&mut self, line: &str) {
    if self.quiet {
      self.clear_ephemeral();
    }
    eprintln!("{line}");
  }

  /// Clear any trailing ephemeral output so subsequent prints start on a
  /// fresh line. Safe to call when nothing is buffered.
  fn flush(&mut self) {
    if self.quiet {
      self.clear_ephemeral();
    }
  }

  /// Rewind over the currently-buffered ephemeral label (if any) so the next
  /// write lands in column 0 of the topmost affected row.
  fn clear_ephemeral(&mut self) {
    let n = self.ephemeral_lines;
    if n == 0 {
      return;
    }
    if n == 1 {
      eprint!("\x1b[2K\r");
    } else {
      // Clear current line, then move up and clear each line above.
      eprint!("\x1b[2K");
      for _ in 1..n {
        eprint!("\x1b[A\x1b[2K");
      }
      eprint!("\r");
    }
    self.ephemeral_lines = 0;
  }
}

/// How many terminal rows a single `text` occupies in a `cols`-wide terminal.
///
/// Uses byte length as a proxy for display width — good enough for ASCII
/// constant names; Unicode-heavy names may under-count, but the resulting
/// clear is at worst missing a trailing byte which the next label overwrites
/// anyway.
#[inline]
fn lines_occupied(text: &str, cols: usize) -> usize {
  if cols == 0 {
    return 1;
  }
  let len = text.len();
  if len == 0 { 1 } else { len.div_ceil(cols) }
}

/// Terminal width of stderr via `ioctl(TIOCGWINSZ)`. Falls back to 80 when
/// stderr isn't a TTY (e.g. piped to `tee` or `less`) or the syscall fails.
fn term_cols_stderr() -> usize {
  // `winsize` layout: [ws_row, ws_col, ws_xpixel, ws_ypixel].
  let mut ws = [0u16; 4];
  #[cfg(target_os = "linux")]
  const TIOCGWINSZ: std::ffi::c_ulong = 0x5413;
  #[cfg(target_os = "macos")]
  const TIOCGWINSZ: std::ffi::c_ulong = 0x40087468;
  #[cfg(any(target_os = "linux", target_os = "macos"))]
  {
    unsafe extern "C" {
      fn ioctl(fd: i32, request: std::ffi::c_ulong, ...) -> i32;
    }
    let ret = unsafe { ioctl(2, TIOCGWINSZ, ws.as_mut_ptr()) };
    if ret == 0 && ws[1] > 0 { ws[1] as usize } else { 80 }
  }
  #[cfg(not(any(target_os = "linux", target_os = "macos")))]
  {
    80
  }
}

/// Format a `TcError` for user-facing Lean-side display. For the two cases we
/// hit most often we emit a human-tuned multi-line message; everything else
/// falls through to `Debug`.
fn format_tc_error(e: &TcError<Meta>) -> String {
  match e {
    TcError::AppTypeMismatch { depth, .. } => {
      format!("AppTypeMismatch at depth={depth}")
    },
    TcError::FunExpected { .. } => "FunExpected".to_string(),
    // Everything else has a hand-written `Display` impl in
    // `src/ix/kernel/error.rs` — prefer it over `{:?}` which dumps raw
    // KExpr internals.
    other => format!("{other}"),
  }
}

// =============================================================================
// Lean-side result construction
// =============================================================================

/// Build an `IO (Array (Option CheckError))` from Rust results.
///
/// The Lean caller pairs each slot with `names[i]` (the input array) for
/// display, so there's no name in the returned tuple.
///
/// - `Ok(())`              → `none`
/// - `Err((Kernel, msg))`  → `some (CheckError.kernelException msg)`
/// - `Err((Compile, msg))` → `some (CheckError.compileError msg)`
fn build_result_array(results: &[CheckRes]) -> LeanIOResult<LeanOwned> {
  let arr = LeanArray::alloc(results.len());
  for (i, result) in results.iter().enumerate() {
    let option_obj: LeanOwned = match result {
      Ok(()) => {
        // `Option.none` — tag 0, zero fields, zero scalars.
        LeanCtor::alloc(0, 0, 0).into()
      },
      Err((kind, msg)) => {
        // `CheckError.<variant> msg` — tag comes from ErrKind, one object
        // field. Lean's inductive has 2 ctors (kernelException,
        // compileError) so it's NOT eligible for the LCNF trivial-structure
        // optimization — the heap wrapper is required.
        let err_ctor = LeanCtor::alloc(kind.tag(), 1, 0);
        err_ctor.set(0, LeanString::new(msg));
        // `Option.some err` — tag 1, one object field.
        let some_ctor = LeanCtor::alloc(1, 1, 0);
        some_ctor.set(0, err_ctor);
        some_ctor.into()
      },
    };
    arr.set(i, option_obj);
  }
  LeanIOResult::ok(arr)
}

/// Build a result array of length `count` where every slot is the same
/// compile-kind error. Used when compile/ingress/thread setup fails
/// before per-constant checking can begin — the error arose before the
/// kernel was consulted, so `Compile` is the honest tag.
fn build_uniform_error(count: usize, msg: &str) -> LeanIOResult<LeanOwned> {
  let results: Vec<CheckRes> =
    (0..count).map(|_| Err((ErrKind::Compile, msg.to_string()))).collect();
  build_result_array(&results)
}

// =============================================================================
// Kernel ingress + egress roundtrip (via Ixon + decompile)
// =============================================================================
//
// End-to-end check of the compile + kernel pipeline WITHOUT typechecking:
//   Lean env → compile_env (stt)
//            → ixon_ingress (stt.env) → KEnv<Meta>
//            → ixon_egress (kenv, stt.env) → IxonEnv'
//            → patch stt.env = IxonEnv'
//            → decompile_env (stt) → DecompileState.env (Lean)
// and compare each constant's type/value against the original by content
// hash.
//
// Unlike the earlier direct `KEnv → lean_egress` variant, this path lets the
// validated `decompile_env` (the same pass `validate-aux` and `rust-compile`
// cover) regenerate the aux_gen auxiliaries (`.brecOn*`, `.brecOn_N.eq`,
// etc.) from the kernel-canonicalized Ixon form. That's the critical step
// for closing the `.brecOn*` binder-name / alpha-collapse drift: the prior
// direct path was a second decompiler with no aux_gen awareness.
//
// If `ixon_egress` is structurally faithful (kenv → ixon inversion preserves
// the original addressing) and decompile_env regenerates aux_gen correctly,
// this test should report zero mismatches.
//
// Test-only: this and the no-compile variant below import `egress` and
// `decompile_env`, which the production CLI path (`rs_kernel_check_consts`)
// doesn't need. Cfg-gating keeps `lake build ix` (no `test-ffi`) lean.

/// FFI: exercise the full pipeline
/// Lean → Ixon → kernel → Ixon' → decompile → Lean, and compare each
/// constant against the original.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_kernel_roundtrip"]
/// opaque rsKernelRoundtripFFI :
///     @& List (Lean.Name × Lean.ConstantInfo) → IO (Array String)
/// ```
/// Returns an `Array String` of per-constant diff messages. Empty = pass.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_roundtrip(
  env_consts: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();

  let t0 = Instant::now();
  let rust_env = decode_env(env_consts);
  eprintln!("[rs_kernel_roundtrip] read env:      {:>8.1?}", t0.elapsed());

  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let mut compile_state = match compile_env_with_options(
    &rust_env_arc,
    CompileOptions { check_originals: false, ..Default::default() },
  ) {
    Ok(s) => s,
    Err(e) => {
      return build_string_array(&[format!("compile error: {e:?}")]);
    },
  };
  eprintln!("[rs_kernel_roundtrip] compile:       {:>8.1?}", t1.elapsed());

  let t2 = Instant::now();
  let (mut kenv, intern) = match ixon_ingress::<Meta>(&compile_state.env) {
    Ok(v) => v,
    Err(msg) => {
      return build_string_array(&[format!("ingress error: {msg}")]);
    },
  };
  kenv.intern = intern;
  eprintln!(
    "[rs_kernel_roundtrip] ingress:       {:>8.1?} ({} consts)",
    t2.elapsed(),
    kenv.len()
  );

  // Egress KEnv → IxonEnv (reusing the original env's `ConstantMeta` +
  // blobs + names).
  let t3 = Instant::now();
  let egressed_ixon = match ixon_egress(&kenv, &compile_state.env) {
    Ok(e) => e,
    Err(msg) => {
      return build_string_array(&[format!("ixon_egress error: {msg}")]);
    },
  };
  eprintln!(
    "[rs_kernel_roundtrip] ixon egress:   {:>8.1?} ({} consts, {} named)",
    t3.elapsed(),
    egressed_ixon.const_count(),
    egressed_ixon.named_count()
  );

  // Free the kenv now that we've extracted everything we need; decompile
  // works off CompileState only and the kenv is the large structure we
  // built during ingress.
  drop(kenv);

  // Patch the compile state to point at the egressed Ixon env. Decompile
  // reads from `stt.env.named` / `stt.env.get_const` / `stt.env.get_blob` —
  // the egressed env preserves all of those (meta is copied from the
  // original; constants are re-synthesized from kenv; blobs/names are
  // cloned). `stt.blocks`, `stt.kctx`, `stt.aux_gen_extra_names`, etc.
  // remain untouched so decompile's Pass 2 (aux_gen regeneration) has the
  // block structure it expects.
  compile_state.env = egressed_ixon;

  let t4 = Instant::now();
  let dstt = match decompile_env(&compile_state) {
    Ok(d) => d,
    Err(e) => {
      return build_string_array(&[format!("decompile error: {e:?}")]);
    },
  };
  eprintln!(
    "[rs_kernel_roundtrip] decompile:     {:>8.1?} ({} consts)",
    t4.elapsed(),
    dstt.env.len()
  );

  // Build a plain Lean `Env` from decompile's DashMap for the standard
  // compare_envs / find_diff flow.
  let t5 = Instant::now();
  let mut decompiled_env = crate::ix::env::Env::default();
  for entry in dstt.env.iter() {
    decompiled_env.insert(entry.key().clone(), entry.value().clone());
  }
  eprintln!(
    "[rs_kernel_roundtrip] build lean env:{:>8.1?} ({} consts)",
    t5.elapsed(),
    decompiled_env.len()
  );

  // Compare decompiled env against original, content-hash by content-hash.
  let t6 = Instant::now();
  let (errors, checked, not_found) =
    compare_envs(&rust_env_arc, &decompiled_env);
  eprintln!(
    "[rs_kernel_roundtrip] verify:        {:>8.1?} (checked {checked}, not_found {not_found}, errors {})",
    t6.elapsed(),
    errors.len()
  );

  drop(compile_state);
  drop(rust_env_arc);

  eprintln!(
    "[rs_kernel_roundtrip] total:         {:>8.1?}",
    total_start.elapsed()
  );

  build_string_array(&errors)
}

/// Compare two envs for structural equality under content-hashing. Returns
/// `(errors, checked, not_found)`. `errors` is capped at 50 to keep outputs
/// manageable.
#[cfg(feature = "test-ffi")]
fn compare_envs(
  original: &crate::ix::env::Env,
  egressed: &crate::ix::env::Env,
) -> (Vec<String>, usize, usize) {
  use crate::ix::env::ConstantInfo as LCI;

  let total = original.len();
  let mut errors: Vec<String> = Vec::new();
  let mut checked = 0usize;
  let mut not_found = 0usize;

  for (name, orig_ci) in original.iter() {
    match egressed.get(name) {
      None => {
        not_found += 1;
      },
      Some(egressed_ci) => {
        checked += 1;
        if orig_ci.get_type().get_hash() != egressed_ci.get_type().get_hash() {
          let diff =
            find_diff(orig_ci.get_type(), egressed_ci.get_type(), "type");
          errors.push(format!("{name}: {diff}"));
        }
        match (orig_ci, egressed_ci) {
          (LCI::DefnInfo(a), LCI::DefnInfo(b))
            if a.value.get_hash() != b.value.get_hash() =>
          {
            let diff = find_diff(&a.value, &b.value, "value");
            errors.push(format!("{name}: {diff}"));
          },
          (LCI::ThmInfo(a), LCI::ThmInfo(b))
            if a.value.get_hash() != b.value.get_hash() =>
          {
            let diff = find_diff(&a.value, &b.value, "value");
            errors.push(format!("{name}: {diff}"));
          },
          (LCI::OpaqueInfo(a), LCI::OpaqueInfo(b))
            if a.value.get_hash() != b.value.get_hash() =>
          {
            let diff = find_diff(&a.value, &b.value, "value");
            errors.push(format!("{name}: {diff}"));
          },
          (LCI::RecInfo(a), LCI::RecInfo(b)) => {
            for (i, (r1, r2)) in a.rules.iter().zip(b.rules.iter()).enumerate()
            {
              if r1.rhs.get_hash() != r2.rhs.get_hash() {
                let diff =
                  find_diff(&r1.rhs, &r2.rhs, &format!("rule[{i}].rhs"));
                errors.push(format!("{name}: {diff}"));
              }
            }
          },
          _ => {},
        }
        if errors.len() >= 50 {
          break;
        }
      },
    }
    if checked % 10000 == 0 && checked > 0 {
      eprintln!(
        "[rs_kernel_roundtrip] verify:      {checked}/{total} ({} errors so far)",
        errors.len()
      );
    }
  }

  (errors, checked, not_found)
}

/// Walk two `Expr` trees in parallel and return the first structural diff.
/// Returns a path-annotated description of where the mismatch is.
#[cfg(feature = "test-ffi")]
fn find_diff(
  a: &crate::ix::env::Expr,
  b: &crate::ix::env::Expr,
  path: &str,
) -> String {
  use crate::ix::env::ExprData;

  if a.get_hash() == b.get_hash() {
    return format!("{path}: hashes match (ok)");
  }
  match (a.as_data(), b.as_data()) {
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) if i != j => {
      format!("{path}: bvar {i} vs {j}")
    },
    (ExprData::Sort(l1, _), ExprData::Sort(l2, _)) => {
      format!("{path}: sort hash {} vs {}", l1.get_hash(), l2.get_hash())
    },
    (ExprData::Const(n1, ls1, _), ExprData::Const(n2, ls2, _)) => {
      if n1 != n2 {
        format!("{path}: const name {n1} vs {n2}")
      } else {
        format!("{path}: const {n1} levels {}-vs-{}", ls1.len(), ls2.len())
      }
    },
    (ExprData::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
      if f1.get_hash() != f2.get_hash() {
        find_diff(f1, f2, &format!("{path}.app.fn"))
      } else {
        find_diff(a1, a2, &format!("{path}.app.arg"))
      }
    },
    (ExprData::Lam(n1, t1, b1, bi1, _), ExprData::Lam(n2, t2, b2, bi2, _)) => {
      if n1 != n2 {
        return format!("{path}: lam name {n1} vs {n2}");
      }
      if bi1 != bi2 {
        return format!("{path}: lam bi {bi1:?} vs {bi2:?}");
      }
      if t1.get_hash() != t2.get_hash() {
        find_diff(t1, t2, &format!("{path}.lam.ty"))
      } else {
        find_diff(b1, b2, &format!("{path}.lam.body"))
      }
    },
    (
      ExprData::ForallE(n1, t1, b1, bi1, _),
      ExprData::ForallE(n2, t2, b2, bi2, _),
    ) => {
      if n1 != n2 {
        return format!("{path}: pi name {n1} vs {n2}");
      }
      if bi1 != bi2 {
        return format!("{path}: pi bi {bi1:?} vs {bi2:?}");
      }
      if t1.get_hash() != t2.get_hash() {
        find_diff(t1, t2, &format!("{path}.pi.ty"))
      } else {
        find_diff(b1, b2, &format!("{path}.pi.body"))
      }
    },
    (
      ExprData::LetE(n1, t1, v1, b1, nd1, _),
      ExprData::LetE(n2, t2, v2, b2, nd2, _),
    ) => {
      if n1 != n2 {
        return format!("{path}: let name {n1} vs {n2}");
      }
      if nd1 != nd2 {
        return format!("{path}: let nonDep {nd1} vs {nd2}");
      }
      if t1.get_hash() != t2.get_hash() {
        find_diff(t1, t2, &format!("{path}.let.ty"))
      } else if v1.get_hash() != v2.get_hash() {
        find_diff(v1, v2, &format!("{path}.let.val"))
      } else {
        find_diff(b1, b2, &format!("{path}.let.body"))
      }
    },
    (ExprData::Lit(l1, _), ExprData::Lit(l2, _)) => {
      format!("{path}: lit {l1:?} vs {l2:?}")
    },
    (ExprData::Proj(n1, i1, s1, _), ExprData::Proj(n2, i2, s2, _)) => {
      if n1 != n2 || i1 != i2 {
        format!("{path}: proj {n1}.{i1} vs {n2}.{i2}")
      } else {
        find_diff(s1, s2, &format!("{path}.proj.struct"))
      }
    },
    (ExprData::Mdata(kvs1, e1, _), ExprData::Mdata(kvs2, e2, _)) => {
      // Both sides have mdata — compare content.
      let h1 =
        kvs1.iter().map(|(n, _)| format!("{n}")).collect::<Vec<_>>().join(",");
      let h2 =
        kvs2.iter().map(|(n, _)| format!("{n}")).collect::<Vec<_>>().join(",");
      if kvs1.len() != kvs2.len() || h1 != h2 {
        format!("{path}: mdata keys differ [{h1}] vs [{h2}]")
      } else {
        // Keys match — compare hashes of each value.
        let mut val_diffs = Vec::new();
        for (i, ((n1, v1), (_, v2))) in kvs1.iter().zip(kvs2.iter()).enumerate()
        {
          use crate::ix::env::hash_data_value;
          let mut h1 = blake3::Hasher::new();
          let mut h2 = blake3::Hasher::new();
          hash_data_value(v1, &mut h1);
          hash_data_value(v2, &mut h2);
          if h1.finalize() != h2.finalize() {
            val_diffs.push(format!("mdata[{i}] key={n1}: value hash differs"));
          }
        }
        if !val_diffs.is_empty() {
          format!("{path}: {}", val_diffs.join("; "))
        } else {
          // Mdata content matches — diff must be in the inner expr.
          find_diff(e1, e2, &format!("{path}.mdata="))
        }
      }
    },
    (ExprData::Mdata(kvs, e1, _), _) => {
      let keys: Vec<_> = kvs.iter().map(|(n, _)| format!("{n}")).collect();
      find_diff(e1, b, &format!("{path}.ORIG_HAS_mdata[{}]>", keys.join(",")))
    },
    (_, ExprData::Mdata(kvs, e2, _)) => {
      let keys: Vec<_> = kvs.iter().map(|(n, _)| format!("{n}")).collect();
      find_diff(a, e2, &format!("{path}.<EGRESS_HAS_mdata[{}]", keys.join(",")))
    },
    _ => {
      let kind_a = std::mem::discriminant(a.as_data());
      let kind_b = std::mem::discriminant(b.as_data());
      format!("{path}: node kind mismatch {kind_a:?} vs {kind_b:?}")
    },
  }
}

/// Build an `IO (Array String)` from a slice of error messages.
#[cfg(feature = "test-ffi")]
fn build_string_array(errors: &[String]) -> LeanIOResult<LeanOwned> {
  let arr = LeanArray::alloc(errors.len());
  for (i, msg) in errors.iter().enumerate() {
    arr.set(i, LeanString::new(msg));
  }
  LeanIOResult::ok(arr)
}

// =============================================================================
// Direct Lean env → kernel env roundtrip (no compile)
// =============================================================================
//
// End-to-end check that skips `compile_env` / `ixon_ingress` entirely.
// Pipeline: decoded Lean `Env` → `lean_ingress` → `KEnv<Meta>` →
// `lean_egress` → `Lean env` → compare against original.
//
// Reuses the same `compare_envs` / `find_diff` / `build_string_array`
// infrastructure as `rs_kernel_roundtrip`, so error messages have identical
// shape and we can diff counts 1:1 between the two paths.
//
// Useful for bisecting brecOn-like regressions: if this path is clean and
// `rs_kernel_roundtrip` has ~50 errors, the compile pipeline is dropping
// information; if both show the same errors, ingress/egress is.

/// FFI: exercise the full pipeline Lean env → kernel → Lean (egress) WITHOUT
/// going through Ixon compilation, and compare each constant against the
/// original.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_kernel_roundtrip_no_compile"]
/// opaque rsKernelRoundtripNoCompileFFI :
///     @& List (Lean.Name × Lean.ConstantInfo) → IO (Array String)
/// ```
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_roundtrip_no_compile(
  env_consts: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();

  let t0 = Instant::now();
  let rust_env = decode_env(env_consts);
  eprintln!(
    "[rs_kernel_roundtrip_no_compile] read env:    {:>8.1?}",
    t0.elapsed()
  );

  // Direct Lean → kernel ingress. No compile, no Ixon.
  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let kenv = lean_ingress(&rust_env_arc);
  eprintln!(
    "[rs_kernel_roundtrip_no_compile] ingress:     {:>8.1?} ({} consts)",
    t1.elapsed(),
    kenv.len()
  );

  // Egress kernel → Lean.
  let t2 = Instant::now();
  let egressed_env = lean_egress(&kenv);
  eprintln!(
    "[rs_kernel_roundtrip_no_compile] egress:      {:>8.1?} ({} consts)",
    t2.elapsed(),
    egressed_env.len()
  );

  // Compare.
  let t3 = Instant::now();
  let (errors, checked, not_found) = compare_envs(&rust_env_arc, &egressed_env);
  eprintln!(
    "[rs_kernel_roundtrip_no_compile] verify:      {:>8.1?} (checked {checked}, not_found {not_found}, errors {})",
    t3.elapsed(),
    errors.len()
  );

  drop(rust_env_arc);

  eprintln!(
    "[rs_kernel_roundtrip_no_compile] total:       {:>8.1?}",
    total_start.elapsed()
  );

  build_string_array(&errors)
}
