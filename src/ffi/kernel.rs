//! Kernel constant checking FFI.
//!
//! Exposes `rs_kernel_check_consts` (production, used by `lake exe ix check`
//! and `Tests/Ix/Kernel/Tutorial.lean`), `rs_kernel_ingress` (production,
//! used by `lake exe ix ingress` for ingress-only performance analysis),
//! plus a pair of test-only roundtrip probes (`rs_kernel_roundtrip` /
//! `rs_kernel_roundtrip_no_compile`).
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

use std::fs::File;
use std::io::Write;
use std::sync::{
  Arc, Mutex, OnceLock,
  atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

use lean_ffi::include::lean_object;
use lean_ffi::nat::Nat;
use rustc_hash::FxHashMap;

use lean_ffi::object::{
  LeanArray, LeanBool, LeanBorrowed, LeanIOResult, LeanList, LeanOption,
  LeanOwned, LeanProd, LeanRef, LeanString,
};

use crate::lean::LeanIxCheckError;

#[cfg(feature = "test-ffi")]
use crate::ffi::lean_env::{GlobalCache, decode_name};
use crate::ffi::lean_env::{decode_env, decode_name_array};
use crate::ix::address::Address;
use crate::ix::compile::{
  CompileOptions, CompileState, compile_env_with_options,
};
#[cfg(feature = "test-ffi")]
use crate::ix::decompile::decompile_env;
use crate::ix::env::{Name, NameData};
use crate::ix::ixon::constant::ConstantInfo as IxonCI;
#[cfg(feature = "test-ffi")]
use crate::ix::ixon::constant::MutConst as IxonMutConst;
use crate::ix::ixon::env::Env as IxonEnv;
#[cfg(feature = "test-ffi")]
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::metadata::ConstantMetaInfo;
#[cfg(feature = "test-ffi")]
use crate::ix::kernel::egress::{ixon_egress, lean_egress};
use crate::ix::kernel::env::KEnv;
use crate::ix::kernel::error::TcError;
use crate::ix::kernel::id::KId;
use crate::ix::kernel::ingress::{
  IxonIngressLookups, build_ixon_ingress_lookups,
  ingress_const_shallow_into_kenv_with_lookups, ixon_ingress_owned,
};
use crate::ix::kernel::ingress::{
  anon_ctor_proj_addr, anon_defn_proj_addr, anon_indc_proj_addr,
  anon_recr_proj_addr,
};
#[cfg(feature = "test-ffi")]
use crate::ix::kernel::ingress::{ixon_ingress, lean_ingress};
use crate::ix::kernel::mode::{Anon, CheckDupLevelParams, KernelMode, Meta};
use crate::ix::kernel::tc::TypeChecker;
use crate::ix::profile::{BlockProfile, ProfileBuilder, ProfileSink};

unsafe extern "C" {
  fn lean_name_mk_string(
    parent: *mut lean_object,
    part: *mut lean_object,
  ) -> *mut lean_object;
  fn lean_name_mk_numeral(
    parent: *mut lean_object,
    part: *mut lean_object,
  ) -> *mut lean_object;
}

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

/// Streaming writer for the `--fail-out` file used by `lake exe ix
/// check`.
///
/// The previous implementation buffered all failures in Lean and dumped them
/// once at the very end of the run, which meant a long-running full-env
/// check exposed nothing to a `tail -f` observer until the whole batch had
/// completed. Streaming here writes a header up front, appends each failure
/// (one record == one comment-line + one bare-name line + a trailing blank
/// line, matching the format `readNamesFile` understands) as it is detected,
/// and flushes after every record so the file is immediately readable from
/// outside the process.
///
/// Records are written under a `Mutex<File>` so parallel workers don't
/// interleave bytes — failures are rare enough that the lock contention is
/// negligible, and `File` writes go straight to the kernel page cache so
/// `tail -f` observers see new entries without needing `fsync`.
struct FailureLog {
  writer: Mutex<File>,
  count: AtomicUsize,
}

impl FailureLog {
  /// Truncate-create the file at `path`, write the comment header (`# env`,
  /// `# seeds`), and return a handle ready to record per-failure entries.
  fn open(path: &str, env_path: &str, seeds: usize) -> std::io::Result<Self> {
    let mut file = File::create(path)?;
    writeln!(file, "# ix check failures")?;
    writeln!(file, "# env: {env_path}")?;
    writeln!(file, "# seeds: {seeds}")?;
    writeln!(file)?;
    file.flush()?;
    Ok(Self { writer: Mutex::new(file), count: AtomicUsize::new(0) })
  }

  /// Append a single failure record. `name_pretty` is the dot-separated form
  /// of the constant; `msg` is the raw error string (newlines collapsed to
  /// ` | ` to keep each comment on one line).
  fn record(&self, name_pretty: &str, msg: &str) {
    let one_line = msg.replace('\n', " | ");
    let mut file = self.writer.lock().unwrap();
    let _ = writeln!(file, "# {one_line}");
    let _ = writeln!(file, "{name_pretty}");
    let _ = writeln!(file);
    let _ = file.flush();
    self.count.fetch_add(1, Ordering::Relaxed);
  }

  /// Append the trailing `# total failures: N` summary. Called once after
  /// all per-constant checks have reported.
  fn finalize(&self) {
    let mut file = self.writer.lock().unwrap();
    let _ = writeln!(
      file,
      "# total failures: {}",
      self.count.load(Ordering::Relaxed)
    );
    let _ = file.flush();
  }

  fn count(&self) -> usize {
    self.count.load(Ordering::Relaxed)
  }
}

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
  let compile_state =
    match compile_env_with_options(&rust_env_arc, CompileOptions::default()) {
      Ok(s) => s,
      Err(e) => {
        return build_uniform_error(
          names_vec.len(),
          &format!("[compile] {e:?}"),
        );
      },
    };
  eprintln!("[rs_kernel_check] compile:    {:>8.1?}", t1.elapsed());

  let CompileState { env: ixon_env, ungrounded: compile_ungrounded, .. } =
    compile_state;

  // Snapshot per-constant compile failures (ill-formed inductives,
  // cascading MissingConstant, etc.) keyed by `Name` so the check loop
  // can skip the kernel and report them as compile-side rejections.
  // `compile_env` no longer aborts on per-block failure; it populates
  // `CompileState.ungrounded` and continues, letting good constants still
  // compile cleanly.
  let ungrounded: FxHashMap<Name, String> = compile_ungrounded
    .iter()
    .map(|e| (e.key().clone(), e.value().clone()))
    .collect();
  drop(compile_ungrounded);
  drop(rust_env_arc);
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
  // Prepare read-only Ixon lookups. Kernel ingress happens on demand inside
  // each worker's private KEnv, so there is no shared typecheck cache.
  // ---------------------------------------------------------------------
  let t2 = Instant::now();
  let ixon_env = Arc::new(ixon_env);
  let lookups = Arc::new(build_ixon_ingress_lookups(&ixon_env));
  eprintln!(
    "[rs_kernel_check] ingress prep:{:>8.1?} ({} named)",
    t2.elapsed(),
    ixon_env.named_count()
  );
  let total = names_vec.len();
  let t3 = Instant::now();

  // ---------------------------------------------------------------------
  // Per-constant checking on a 256 MB stack
  // ---------------------------------------------------------------------
  // Deep recursor expansions push the Rust stack. A dedicated thread with a
  // large stack matches the old ix_old pattern.
  let results = match run_checks_on_large_stack::<Meta>(
    Arc::clone(&ixon_env),
    lookups,
    names_vec.clone(),
    expect_pass_vec,
    ungrounded,
    quiet,
    None,
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

/// Test-only FFI: compile a Lean fixture to Ixon, deliberately corrupt one
/// recursor rule in the compiled Ixon payload, then check that exact malformed
/// Ixon with the kernel.
///
/// This is intentionally separate from `rs_kernel_check_consts`: the normal
/// compile path may regenerate aux recursors, which is correct production
/// behavior but masks tests whose point is "reject this stored recursor
/// payload." Mutating after compile gives the tutorial suite a precise
/// regression hook without weakening aux generation for real inputs.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_check_malformed_rec_rule_ixon(
  env_consts: LeanList<LeanBorrowed<'_>>,
  rec_name_obj: LeanBorrowed<'_>,
) -> LeanIOResult<LeanOwned> {
  let t0 = Instant::now();
  let rust_env = decode_env(env_consts);
  let global = GlobalCache::default();
  let rec_name = decode_name(rec_name_obj, &global);
  eprintln!(
    "[rs_kernel_check_malformed_rec_rule_ixon] read env: {:>8.1?}",
    t0.elapsed()
  );

  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let compile_state =
    match compile_env_with_options(&rust_env_arc, CompileOptions::default()) {
      Ok(s) => s,
      Err(e) => {
        return LeanIOResult::error_string(&format!(
          "rs_kernel_check_malformed_rec_rule_ixon: compile failed: {e:?}"
        ));
      },
    };
  eprintln!(
    "[rs_kernel_check_malformed_rec_rule_ixon] compile:  {:>8.1?}",
    t1.elapsed()
  );

  let CompileState { env: ixon_env, ungrounded, .. } = compile_state;
  if let Some(msg) = ungrounded.get(&rec_name).map(|m| m.clone()) {
    drop(ungrounded);
    drop(rust_env_arc);
    return LeanIOResult::ok(build_option_result(&Err((
      ErrKind::Compile,
      msg,
    ))));
  }
  drop(ungrounded);
  drop(rust_env_arc);

  let rec_addr =
    match poison_second_rec_rule_returns_first_minor(&ixon_env, &rec_name) {
      Ok(addr) => addr,
      Err(msg) => {
        return LeanIOResult::error_string(&format!(
          "rs_kernel_check_malformed_rec_rule_ixon: {msg}"
        ));
      },
    };

  let t2 = Instant::now();
  let (mut kenv, intern) = match ixon_ingress_owned::<Meta>(ixon_env) {
    Ok(v) => v,
    Err(msg) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_check_malformed_rec_rule_ixon: ingress failed: {msg}"
      ));
    },
  };
  kenv.intern = intern;
  eprintln!(
    "[rs_kernel_check_malformed_rec_rule_ixon] ingress:  {:>8.1?}",
    t2.elapsed()
  );

  let kid = KId::new(rec_addr, rec_name);
  let result = {
    let mut tc = TypeChecker::new(&mut kenv);
    match tc.check_const(&kid) {
      Ok(()) => Ok(()),
      Err(e) => Err((ErrKind::Kernel, e.to_string())),
    }
  };
  LeanIOResult::ok(build_option_result(&result))
}

#[cfg(feature = "test-ffi")]
fn poison_second_rec_rule_returns_first_minor(
  ixon_env: &IxonEnv,
  rec_name: &Name,
) -> Result<Address, String> {
  let named = ixon_env
    .lookup_name(rec_name)
    .ok_or_else(|| format!("{}: missing Named entry", rec_name.pretty()))?;
  let rec_addr = named.addr.clone();
  // Materialize then clone out of the Arc — we mutate the constant
  // in-place to poison a recursor rule before storing it back.
  let rec_arc = ixon_env.get_const(&rec_addr).ok_or_else(|| {
    format!("{}: missing constant {}", rec_name.pretty(), rec_addr.hex())
  })?;
  let mut rec_constant: crate::ix::ixon::constant::Constant =
    (*rec_arc).clone();
  drop(rec_arc);

  match &mut rec_constant.info {
    IxonCI::Recr(rec) => {
      poison_recursor_rule_payload(rec)?;
      ixon_env.store_const(rec_addr.clone(), rec_constant);
      Ok(rec_addr)
    },
    IxonCI::Muts(members) => {
      let mut found = false;
      for member in members.iter_mut() {
        if let IxonMutConst::Recr(rec) = member {
          poison_recursor_rule_payload(rec)?;
          found = true;
          break;
        }
      }
      if !found {
        return Err(format!(
          "{}: directly named Muts block contains no recursor member",
          rec_name.pretty()
        ));
      }
      ixon_env.store_const(rec_addr.clone(), rec_constant);
      Ok(rec_addr)
    },
    IxonCI::RPrj(proj) => {
      let block_addr = proj.block.clone();
      let block_arc = ixon_env.get_const(&block_addr).ok_or_else(|| {
        format!(
          "{}: recursor projection points at missing block {}",
          rec_name.pretty(),
          block_addr.hex()
        )
      })?;
      let mut block_constant: crate::ix::ixon::constant::Constant =
        (*block_arc).clone();
      drop(block_arc);
      match &mut block_constant.info {
        IxonCI::Muts(members) => {
          let idx = usize::try_from(proj.idx).map_err(|_e| {
            format!(
              "{}: recursor projection index too large",
              rec_name.pretty()
            )
          })?;
          match members.get_mut(idx) {
            Some(IxonMutConst::Recr(rec)) => poison_recursor_rule_payload(rec)?,
            Some(_) => {
              return Err(format!(
                "{}: projection index {} is not a recursor member",
                rec_name.pretty(),
                proj.idx
              ));
            },
            None => {
              return Err(format!(
                "{}: projection index {} out of range for recursor block",
                rec_name.pretty(),
                proj.idx
              ));
            },
          }
        },
        other => {
          return Err(format!(
            "{}: recursor projection block is not Muts (got {other:?})",
            rec_name.pretty()
          ));
        },
      }
      ixon_env.store_const(block_addr, block_constant);
      Ok(rec_addr)
    },
    other => Err(format!(
      "{}: expected recursor or recursor projection, got {other:?}",
      rec_name.pretty()
    )),
  }
}

#[cfg(feature = "test-ffi")]
fn poison_recursor_rule_payload(
  rec: &mut crate::ix::ixon::constant::Recursor,
) -> Result<(), String> {
  if rec.rules.len() < 2 {
    return Err(format!(
      "expected at least two recursor rules, got {}",
      rec.rules.len()
    ));
  }
  rec.rules[1].rhs =
    wrong_successor_rule_returning_first_minor(&rec.rules[1].rhs)?;
  Ok(())
}

#[cfg(feature = "test-ffi")]
fn wrong_successor_rule_returning_first_minor(
  succ_rhs: &Arc<IxonExpr>,
) -> Result<Arc<IxonExpr>, String> {
  match succ_rhs.as_ref() {
    IxonExpr::Lam(motive_ty, rest) => match rest.as_ref() {
      IxonExpr::Lam(h_zero_ty, rest) => match rest.as_ref() {
        IxonExpr::Lam(h_succ_ty, rest) => match rest.as_ref() {
          IxonExpr::Lam(n_ty, _) => Ok(IxonExpr::lam(
            motive_ty.clone(),
            IxonExpr::lam(
              h_zero_ty.clone(),
              IxonExpr::lam(
                h_succ_ty.clone(),
                IxonExpr::lam(n_ty.clone(), IxonExpr::var(2)),
              ),
            ),
          )),
          other => {
            Err(format!("successor rule fourth node is not Lam: {other:?}"))
          },
        },
        other => {
          Err(format!("successor rule third node is not Lam: {other:?}"))
        },
      },
      other => Err(format!("successor rule second node is not Lam: {other:?}")),
    },
    other => Err(format!("successor rule first node is not Lam: {other:?}")),
  }
}

/// FFI: type-check constants from a serialized Ixon environment produced by
/// `ix compile --out`.
///
/// `fail_out` is a streaming-friendly failure file. An empty string means
/// "no file"; any other value is treated as a filesystem path that gets
/// truncate-created at start-of-run, populated incrementally as failures
/// are detected (one record per failure, flushed immediately so `tail -f`
/// observers see entries as they happen), and capped with a `# total
/// failures: N` footer once all checks complete. The format is the same
/// one `Ix.Cli.CheckIxonCmd.readNamesFile` expects (`#`-prefixed comments
/// plus bare-name lines), so the file is round-trippable as a
/// `--consts-file` input on a re-run.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_check_ixon(
  env_path: LeanString<LeanBorrowed<'_>>,
  names: LeanArray<LeanBorrowed<'_>>,
  expect_pass: LeanArray<LeanBorrowed<'_>>,
  quiet: LeanBool<LeanBorrowed<'_>>,
  fail_out: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();
  let quiet = quiet.to_bool();
  let path = env_path.to_string();
  let fail_out_path = fail_out.to_string();
  let fail_out_path =
    if fail_out_path.is_empty() { None } else { Some(fail_out_path) };
  let names_vec: Vec<Name> = decode_name_array(&names);
  let expect_pass_vec: Vec<bool> =
    expect_pass.map(|b| b.unbox_usize() == 1).into_iter().collect();

  let t0 = Instant::now();
  let bytes = match std::fs::read(&path) {
    Ok(bytes) => bytes,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_check_ixon: failed to read {path}: {e}"
      ));
    },
  };
  eprintln!(
    "[rs_kernel_check_ixon] read env:   {:>8.1?} ({} bytes)",
    t0.elapsed(),
    bytes.len()
  );

  let t1 = Instant::now();
  let mut slice: &[u8] = &bytes;
  let ixon_env = match IxonEnv::get(&mut slice) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_check_ixon: failed to deserialize {path}: {e}"
      ));
    },
  };
  drop(bytes);
  eprintln!(
    "[rs_kernel_check_ixon] deserialize:{:>8.1?} ({} named)",
    t1.elapsed(),
    ixon_env.named_count()
  );

  // Open the streaming failure log up front so any seed that fails
  // mid-run is persisted before this function returns. We open it before
  // the ingress lookups are built so that even a setup-time crash leaves
  // the user with a header noting the env path and seed count.
  let failure_log: Option<Arc<FailureLog>> = match fail_out_path.as_deref() {
    None => None,
    Some(out_path) => {
      match FailureLog::open(out_path, &path, names_vec.len()) {
        Ok(log) => {
          eprintln!("[rs_kernel_check_ixon] streaming failures to {out_path}");
          Some(Arc::new(log))
        },
        Err(e) => {
          return LeanIOResult::error_string(&format!(
            "rs_kernel_check_ixon: failed to open fail-out file {out_path}: {e}"
          ));
        },
      }
    },
  };

  let t2 = Instant::now();
  let ixon_env = Arc::new(ixon_env);
  let lookups = Arc::new(build_ixon_ingress_lookups(&ixon_env));
  eprintln!("[rs_kernel_check_ixon] ingress prep:{:>8.1?}", t2.elapsed());

  let total = names_vec.len();
  let t3 = Instant::now();
  let results = match run_checks_on_large_stack::<Meta>(
    ixon_env,
    lookups,
    names_vec,
    expect_pass_vec,
    FxHashMap::default(),
    quiet,
    failure_log.clone(),
  ) {
    Ok(r) => r,
    Err(msg) => {
      if let Some(log) = failure_log.as_ref() {
        log.finalize();
      }
      return build_uniform_error(total, &format!("[thread] {msg}"));
    },
  };

  let passed = results.iter().filter(|r| r.is_ok()).count();
  let failed = results.iter().filter(|r| r.is_err()).count();
  eprintln!(
    "[rs_kernel_check_ixon] {passed}/{total} passed, {failed} failed ({:.1?})",
    t3.elapsed()
  );
  eprintln!(
    "[rs_kernel_check_ixon] total:      {:>8.1?}",
    total_start.elapsed()
  );
  if let Some(log) = failure_log.as_ref() {
    log.finalize();
    eprintln!(
      "[rs_kernel_check_ixon] streamed {} failure(s) to fail-out",
      log.count()
    );
  }

  build_result_array(&results)
}

/// FFI: list the checkable names in a serialized Ixon environment.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_ixon_names(
  env_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let path = env_path.to_string();
  let bytes = match std::fs::read(&path) {
    Ok(bytes) => bytes,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_ixon_names: failed to read {path}: {e}"
      ));
    },
  };
  let mut slice: &[u8] = &bytes;
  let ixon_env = match IxonEnv::get(&mut slice) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_ixon_names: failed to deserialize {path}: {e}"
      ));
    },
  };
  let names = all_checkable_ixon_names(&ixon_env);
  LeanIOResult::ok(build_lean_name_array(&names))
}

/// FFI: expose the canonical primitive `(lean_name, hex_address)`
/// table from `PrimAddrs::new()` to the Lean test suite.
///
/// Used by `testPrimitivesParity`
/// (`Tests/Ix/Kernel/BuildPrimitives.lean`) to detect drift between
/// the hardcoded `PrimAddrs::new()` addresses and the freshly
/// compiled addresses produced by `rsCompileEnvFFI`. Any future
/// compile/serialize change that touches a primitive's content hash
/// will fail this test with a diff before the breakage propagates
/// to downstream consumers (Aiur, kernel primitive resolution).
#[unsafe(no_mangle)]
pub extern "C" fn rs_prim_addrs_canonical() -> LeanIOResult<LeanOwned> {
  let table = crate::ix::kernel::primitive::PrimAddrs::lean_parity_table();
  let arr = LeanArray::alloc(table.len());
  for (i, (name, hex)) in table.iter().enumerate() {
    let name_obj: LeanOwned = LeanString::new(name).into();
    let hex_obj: LeanOwned = LeanString::new(hex).into();
    let pair: LeanOwned = LeanProd::new(name_obj, hex_obj).into();
    arr.set(i, pair);
  }
  LeanIOResult::ok(arr)
}

fn all_checkable_ixon_names(ixon_env: &IxonEnv) -> Vec<Name> {
  let mut names = Vec::with_capacity(ixon_env.named_count());
  for entry in ixon_env.named.iter() {
    if matches!(entry.value().meta.info, ConstantMetaInfo::Muts { .. }) {
      continue;
    }
    names.push(entry.key().clone());
  }
  names.sort_by_key(|name| name.pretty());
  names
}

fn build_lean_name_array(names: &[Name]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(names.len());
  for (i, name) in names.iter().enumerate() {
    arr.set(i, build_lean_name(name));
  }
  arr
}

fn build_lean_name(name: &Name) -> LeanOwned {
  match name.as_data() {
    NameData::Anonymous(_) => LeanOwned::box_usize(0),
    NameData::Str(parent, s, _) => {
      let parent = build_lean_name(parent);
      let part = LeanString::new(s);
      unsafe {
        LeanOwned::from_raw(lean_name_mk_string(
          parent.into_raw(),
          part.into_raw(),
        ))
      }
    },
    NameData::Num(parent, n, _) => {
      let parent = build_lean_name(parent);
      let part = Nat::to_lean(n);
      unsafe {
        LeanOwned::from_raw(lean_name_mk_numeral(
          parent.into_raw(),
          part.into_raw(),
        ))
      }
    },
  }
}

/// FFI: ingress a Lean environment through compile + `ixon_ingress`, stopping
/// before kernel typechecking. Used by `lake exe ix ingress` for performance
/// analysis of the Lean → Ixon → KEnv pipeline in isolation.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_kernel_ingress"]
/// opaque rsKernelIngressFFI : @& List (Lean.Name × Lean.ConstantInfo) → IO USize
/// ```
///
/// Returns the number of kernel constants ingressed. The Rust side prints a
/// per-phase timing breakdown to stderr, mirroring `rs_kernel_check_consts`'s
/// `[rs_kernel_check] read env / compile / ingress` lines (renamed to
/// `[rs_kernel_ingress] ...`). Errors during compile or ingress are reported
/// via `LeanIOResult::error_string`, matching `rs_compile_env`.
///
/// **Always runs destructors** by default (opt out with `IX_SKIP_DROPS=1`),
/// because this is a perf-analysis tool — the `Arc<NameData>` chain-drops
/// across the InternTable shards and the KEnv consts map are part of the
/// real ingress pipeline we want to measure. The reported `total:` line
/// therefore includes teardown cost. Contrast with `rs_compile_env`, which
/// defaults to leaking those allocations to keep a one-shot CLI's wall
/// clock low; here measurement beats wall-clock.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_ingress(
  env_consts: LeanList<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();

  // ---------------------------------------------------------------------
  // Decode inputs
  // ---------------------------------------------------------------------
  let t0 = Instant::now();
  let rust_env = decode_env(env_consts);
  eprintln!("[rs_kernel_ingress] read env:   {:>8.1?}", t0.elapsed());

  // ---------------------------------------------------------------------
  // Compile Lean → Ixon
  // ---------------------------------------------------------------------
  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let compile_state =
    match compile_env_with_options(&rust_env_arc, CompileOptions::default()) {
      Ok(s) => s,
      Err(e) => {
        return LeanIOResult::error_string(&format!(
          "rs_kernel_ingress: compile failed: {e:?}"
        ));
      },
    };
  eprintln!("[rs_kernel_ingress] compile:    {:>8.1?}", t1.elapsed());

  let CompileState { env: ixon_env, ungrounded: compile_ungrounded, .. } =
    compile_state;
  let ungrounded_count = compile_ungrounded.len();
  drop(compile_ungrounded);
  drop(rust_env_arc);
  if ungrounded_count > 0 {
    eprintln!(
      "[rs_kernel_ingress] {ungrounded_count} constants failed to compile (ungrounded; ignored for ingress)"
    );
  }

  // ---------------------------------------------------------------------
  // Ingress Ixon → kernel
  // ---------------------------------------------------------------------
  let t2 = Instant::now();
  let (mut kenv, intern) = match ixon_ingress_owned::<Meta>(ixon_env) {
    Ok(v) => v,
    Err(msg) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_ingress: ingress failed: {msg}"
      ));
    },
  };
  // Move `intern` into the KEnv so they form a single owned tree, matching
  // `rs_kernel_check_consts`'s post-ingress shape. Dropping kenv (which
  // owns intern) gives the same drop-order as the check FFI: KEnv first
  // releases its expr/univ refs into the InternTable's DashMaps, then the
  // InternTable releases the underlying KExpr/KUniv values. Dropping the
  // two as separate locals would invert that order on `intern`'s contents
  // and (empirically) destabilises Lean's later runtime shutdown — this
  // form is segfault-free.
  kenv.intern = intern;
  let kenv_len = kenv.len();
  eprintln!(
    "[rs_kernel_ingress] ingress:    {:>8.1?} ({kenv_len} consts)",
    t2.elapsed(),
  );

  // Always run destructors so the reported `total:` includes teardown
  // cost — this is a perf-analysis CLI, and `Arc<NameData>` chain-drops
  // across the InternTable shards are part of the real ingress pipeline
  // we want to measure. (Contrast with `rs_compile_env`, which intentionally
  // forgets state to keep one-shot CLI wall-clock low; here measurement
  // beats wall-clock.) Opt out with `IX_SKIP_DROPS=1` if you want to
  // compare against the leaked-allocation baseline.
  if std::env::var("IX_SKIP_DROPS").ok().as_deref() == Some("1") {
    eprintln!("[rs_kernel_ingress] skipping destructors (IX_SKIP_DROPS=1)");
    std::mem::forget(kenv);
  } else {
    let drop_start = Instant::now();
    drop(kenv);
    eprintln!(
      "[rs_kernel_ingress] destructors: {:>8.1?}",
      drop_start.elapsed()
    );
  }

  eprintln!("[rs_kernel_ingress] total:      {:>8.1?}", total_start.elapsed());

  // Return the kenv length to Lean so the CLI can include it in its
  // `##ingress##` benchmark line. `USize` values stored inside Lean objects
  // must use Lean's heap scalar representation (`lean_box_usize`), not the
  // tagged-small-object representation used by `lean_box`.
  LeanIOResult::ok(LeanOwned::box_usize_obj(kenv_len))
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

#[derive(Clone, Debug)]
struct CheckWorkItem {
  primary: usize,
  aliases: Vec<usize>,
}

fn build_check_work(
  ixon_env: &IxonEnv,
  names: &[Name],
  expect_pass: &[bool],
  ungrounded: &FxHashMap<Name, String>,
) -> Vec<CheckWorkItem> {
  let mut work: Vec<CheckWorkItem> = Vec::with_capacity(names.len());
  let mut by_block: FxHashMap<(Address, bool), usize> = FxHashMap::default();

  for (i, name) in names.iter().enumerate() {
    let should_pass = expect_pass.get(i).copied().unwrap_or(true);
    let block_key = check_schedule_block_addr(ixon_env, name, ungrounded);
    if let Some(block_key) = block_key {
      let key = (block_key, should_pass);
      if let Some(work_idx) = by_block.get(&key).copied() {
        work[work_idx].aliases.push(i);
        continue;
      }
      let work_idx = work.len();
      by_block.insert(key, work_idx);
    }

    work.push(CheckWorkItem { primary: i, aliases: vec![i] });
  }

  work
}

fn check_schedule_block_addr(
  ixon_env: &IxonEnv,
  name: &Name,
  ungrounded: &FxHashMap<Name, String>,
) -> Option<Address> {
  if ungrounded.contains_key(name) {
    return None;
  }
  let named = ixon_env.lookup_name(name)?;
  if matches!(named.meta.info, ConstantMetaInfo::Muts { .. }) {
    return None;
  }
  let constant = ixon_env.get_const(&named.addr)?;
  // Only collapse work by actual serialized kernel blocks. Projection
  // constants carry the SCC block address directly; ordinary constants are
  // singleton blocks. Do not use declaration-family `all` metadata here: it
  // can include names that are not checked by the same kernel block.
  match &constant.info {
    IxonCI::IPrj(p) => Some(p.block.clone()),
    IxonCI::CPrj(p) => Some(p.block.clone()),
    IxonCI::RPrj(p) => Some(p.block.clone()),
    IxonCI::DPrj(p) => Some(p.block.clone()),
    IxonCI::Muts(_) => None,
    _ => Some(named.addr),
  }
}

fn run_checks_on_large_stack<M: KernelMode>(
  ixon_env: Arc<IxonEnv>,
  lookups: Arc<IxonIngressLookups>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  quiet: bool,
  failure_log: Option<Arc<FailureLog>>,
) -> Result<Vec<CheckRes>, String>
where
  M::MField<Vec<Name>>: CheckDupLevelParams,
{
  if names.is_empty() {
    eprintln!("[rs_kernel_check] checking 0 constants...");
    return Ok(Vec::new());
  }

  let work = build_check_work(&ixon_env, &names, &expect_pass, &ungrounded);
  if work.len() == names.len() {
    eprintln!("[rs_kernel_check] checking {} constants...", names.len());
  } else {
    eprintln!(
      "[rs_kernel_check] checking {} block work item(s) for {} constants...",
      work.len(),
      names.len()
    );
  }

  let worker_count = resolve_kernel_check_workers(work.len(), quiet);
  if worker_count == 1 {
    return run_checks_serial_on_large_stack::<M>(
      ixon_env,
      lookups,
      names,
      expect_pass,
      ungrounded,
      work,
      quiet,
      failure_log,
    );
  }

  run_checks_parallel_on_large_stacks::<M>(
    ixon_env,
    lookups,
    names,
    expect_pass,
    ungrounded,
    work,
    quiet,
    worker_count,
    failure_log,
  )
}

fn run_checks_serial_on_large_stack<M: KernelMode>(
  ixon_env: Arc<IxonEnv>,
  lookups: Arc<IxonIngressLookups>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  work: Vec<CheckWorkItem>,
  quiet: bool,
  failure_log: Option<Arc<FailureLog>>,
) -> Result<Vec<CheckRes>, String>
where
  M::MField<Vec<Name>>: CheckDupLevelParams,
{
  thread::Builder::new()
    .stack_size(KERNEL_CHECK_STACK_SIZE)
    .spawn(move || {
      check_consts_loop::<M>(
        ixon_env,
        lookups,
        names,
        expect_pass,
        ungrounded,
        work,
        quiet,
        failure_log,
      )
    })
    .map_err(|e| format!("failed to spawn kernel-check thread: {e}"))?
    .join()
    .map_err(|_panic| "kernel-check thread panicked".to_string())
}

// All by-value arguments below are immediately wrapped in `Arc` for sharing
// with worker threads — clippy can't see that, so suppress the lint.
#[allow(clippy::needless_pass_by_value)]
fn run_checks_parallel_on_large_stacks<M: KernelMode>(
  ixon_env: Arc<IxonEnv>,
  lookups: Arc<IxonIngressLookups>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  work: Vec<CheckWorkItem>,
  quiet: bool,
  worker_count: usize,
  failure_log: Option<Arc<FailureLog>>,
) -> Result<Vec<CheckRes>, String>
where
  M::MField<Vec<Name>>: CheckDupLevelParams,
{
  let total = names.len();
  let work_total = work.len();
  eprintln!(
    "[rs_kernel_check] checking {work_total} work item(s) for {total} constants with {worker_count} workers..."
  );

  let names = Arc::new(names);
  let expect_pass = Arc::new(expect_pass);
  let ungrounded = Arc::new(ungrounded);
  let work = Arc::new(work);
  let next_index = Arc::new(AtomicUsize::new(0));
  let results: Arc<Vec<OnceLock<CheckRes>>> =
    Arc::new((0..total).map(|_| OnceLock::new()).collect());
  let progress =
    Arc::new(ParallelProgress::new(work_total, worker_count, quiet));
  let mut reporter = ParallelProgress::spawn_reporter(Arc::clone(&progress));

  let mut handles: Vec<thread::JoinHandle<()>> =
    Vec::with_capacity(worker_count);
  for worker_idx in 0..worker_count {
    let ixon_env = Arc::clone(&ixon_env);
    let lookups = Arc::clone(&lookups);
    let names = Arc::clone(&names);
    let expect_pass = Arc::clone(&expect_pass);
    let ungrounded = Arc::clone(&ungrounded);
    let work = Arc::clone(&work);
    let next_index = Arc::clone(&next_index);
    let results = Arc::clone(&results);
    let progress_worker = Arc::clone(&progress);
    let failure_log_worker = failure_log.clone();

    let handle = match thread::Builder::new()
      .name(format!("ix-kernel-check-{worker_idx}"))
      .stack_size(KERNEL_CHECK_STACK_SIZE)
      .spawn(move || {
        let mut kenv = KEnv::<M>::new();
        let clear_every = kernel_check_clear_every();
        let mut checks_since_clear = clear_every;
        let diag_threshold = kernel_check_diag_threshold();
        let mut worker_peak_cache: usize = 0;
        loop {
          let work_idx = next_index.fetch_add(1, Ordering::Relaxed);
          if work_idx >= work_total {
            break;
          }
          let item = &work[work_idx];
          if checks_since_clear >= clear_every {
            kenv.clear_releasing_memory();
            checks_since_clear = 0;
          }

          let outcome = check_one_const(
            item.primary,
            work_idx,
            work_total,
            &ixon_env,
            &lookups,
            names.as_slice(),
            expect_pass.as_slice(),
            ungrounded.as_ref(),
            &mut kenv,
            |prefix| progress_worker.begin(worker_idx, prefix),
          );
          progress_worker.finish(worker_idx, &outcome);
          if let Some(threshold) = diag_threshold {
            log_block_diag_if_big(
              &kenv,
              worker_idx,
              work_idx,
              work_total,
              &outcome,
              threshold,
              &mut worker_peak_cache,
              &progress_worker,
            );
          }
          let result = outcome.result.clone();
          for &result_idx in &item.aliases {
            // Each result slot should be written exactly once. The
            // work-item dedup in `dedup_by_primary` ensures we
            // never schedule the same alias twice. If this fires,
            // a future build_check_work refactor has broken that
            // invariant — surface it instead of silently dropping
            // the second result.
            if results[result_idx].set(result.clone()).is_err() {
              debug_assert!(
                false,
                "meta work-item dedup invariant: result slot {result_idx} set twice"
              );
            }
            // Stream this seed's failure to the fail-out file (if any) as
            // soon as it's known, so a long full-env run grows the file
            // incrementally instead of dropping everything at the end.
            if let (Some(log), Err((_, msg))) =
              (failure_log_worker.as_ref(), result.as_ref())
            {
              log.record(&names[result_idx].pretty(), msg);
            }
          }
          checks_since_clear += 1;
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
  progress.log_mem_summary();
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

// ============================================================================
// Anon-mode parallel runner
// ============================================================================
//
// Companion to `run_checks_parallel_on_large_stacks` for the metadata-free
// anon path. Iterates `env.consts` exactly once to enumerate work items
// (block or standalone), then dispatches to workers each running
// `TypeChecker::<Anon>::new_with_lazy_anon` against its own `KEnv<Anon>`.
// The lazy ingress mechanism (in `tc.rs`) handles cross-block faults
// without consulting metadata.

#[derive(Clone, Debug)]
enum AnonWorkItem {
  /// A standalone (non-mutual, non-projection) constant.
  Standalone { result_idx: usize, addr: Address },
  /// A Muts block. `primary_addr` is the first member's projection address;
  /// `result_idxs` enumerates every kernel-checkable target produced by
  /// the block (each member's projection + each ctor's CPrj of inductive
  /// members), all sharing the same check result via the kernel's
  /// block coordination.
  Block { primary_addr: Address, result_idxs: Vec<usize> },
}

/// One pass over `env.consts`: enumerate work items + the kernel-checkable
/// target addresses (one per result slot). Skips projection constants
/// (covered by their parent block) and Muts addresses themselves
/// (blocks aren't kernel KIds).
fn build_anon_work(
  env: &IxonEnv,
) -> Result<(Vec<AnonWorkItem>, Vec<Address>), String> {
  use crate::ix::ixon::constant::ConstantInfo as CI;
  use crate::ix::ixon::constant::MutConst as MC;
  use crate::ix::ixon::lazy::ConstVariantTag as Tag;

  let mut work: Vec<AnonWorkItem> = Vec::new();
  let mut addrs: Vec<Address> = Vec::new();

  // Sort keys for deterministic ordering across runs.
  let mut keys: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  keys.sort_unstable();

  // Dispatch on the outer Tag4 byte via `peek_variant` — no body
  // parse, no allocation. Only `Muts` blocks require a full
  // materialization (to enumerate members for projection-address
  // computation); the resulting `Arc<Constant>` drops at the end of
  // that match arm. Standalones (Defn/Recr/Axio/Quot, ~95% of the
  // env) and projection skips don't even touch the body.
  //
  // Before this change, every constant was fully materialized here
  // and (worse) pinned forever in `LazyConstant.cache`'s OnceLock.
  // For mathlib that pinned ~30 GB of parsed `Arc<Expr>` trees in
  // the shared `Arc<IxonEnv>` before kernel checking even started.
  // The cache-free `LazyConstant` policy + this peek path keep
  // env-side memory bounded to "bytes (mmap'd) + per-const headers".
  for addr in keys {
    let lc = env.consts.get(&addr).ok_or_else(|| {
      format!("build_anon_work: missing const at {}", addr.hex())
    })?;
    let tag = lc.value().peek_variant().map_err(|e| {
      format!("build_anon_work: peek_variant {}: {e}", addr.hex())
    })?;
    match tag {
      Tag::IPrj | Tag::CPrj | Tag::RPrj | Tag::DPrj => {
        // Skip; covered by parent block.
      },
      Tag::Defn | Tag::Recr | Tag::Axio | Tag::Quot => {
        let result_idx = addrs.len();
        addrs.push(addr.clone());
        work.push(AnonWorkItem::Standalone { result_idx, addr: addr.clone() });
      },
      Tag::Muts => {
        // Materialize once to enumerate members; the `Arc<Constant>`
        // drops at the end of this arm — no cache retention.
        let constant = lc.value().get().map_err(|e| {
          format!("build_anon_work: materialize Muts {}: {e}", addr.hex())
        })?;
        let CI::Muts(members) = &constant.info else {
          return Err(format!(
            "build_anon_work: Tag::Muts but ConstantInfo is {:?} at {}",
            constant.info.variant(),
            addr.hex()
          ));
        };
        // Compute kernel-checkable targets deterministically. Each
        // member contributes its projection address; inductive members
        // contribute one CPrj per constructor.
        let mut targets: Vec<Address> = Vec::new();
        for (i, member) in members.iter().enumerate() {
          let i = i as u64;
          let member_addr = match member {
            MC::Defn(_) => anon_defn_proj_addr(&addr, i),
            MC::Indc(_) => anon_indc_proj_addr(&addr, i),
            MC::Recr(_) => anon_recr_proj_addr(&addr, i),
          };
          targets.push(member_addr);
          if let MC::Indc(ind) = member {
            for cidx in 0..ind.ctors.len() as u64 {
              targets.push(anon_ctor_proj_addr(&addr, i, cidx));
            }
          }
        }
        if targets.is_empty() {
          continue;
        }
        let primary_addr = targets[0].clone();
        let result_idxs: Vec<usize> =
          (addrs.len()..addrs.len() + targets.len()).collect();
        addrs.extend(targets);
        work.push(AnonWorkItem::Block { primary_addr, result_idxs });
      },
    }
  }

  Ok((work, addrs))
}

#[allow(clippy::needless_pass_by_value)]
fn run_anon_checks_parallel(
  env: Arc<IxonEnv>,
  work: Vec<AnonWorkItem>,
  addrs: Vec<Address>,
  quiet: bool,
  failure_log: Option<Arc<FailureLog>>,
) -> Result<Vec<CheckRes>, String> {
  let total = addrs.len();
  let work_total = work.len();
  let worker_count = resolve_kernel_check_workers(work_total, quiet);
  eprintln!(
    "[rs_kernel_check_anon] checking {work_total} work item(s) for {total} consts with {worker_count} worker(s)..."
  );

  let work = Arc::new(work);
  let addrs = Arc::new(addrs);
  let next_index = Arc::new(AtomicUsize::new(0));
  let results: Arc<Vec<OnceLock<CheckRes>>> =
    Arc::new((0..total).map(|_| OnceLock::new()).collect());
  let progress =
    Arc::new(ParallelProgress::new(work_total, worker_count, quiet));
  let mut reporter = ParallelProgress::spawn_reporter(Arc::clone(&progress));

  let mut handles: Vec<thread::JoinHandle<()>> =
    Vec::with_capacity(worker_count);
  for worker_idx in 0..worker_count {
    let env = Arc::clone(&env);
    let work = Arc::clone(&work);
    let addrs = Arc::clone(&addrs);
    let next_index = Arc::clone(&next_index);
    let results = Arc::clone(&results);
    let progress_worker = Arc::clone(&progress);
    let failure_log_worker = failure_log.clone();

    let handle = match thread::Builder::new()
      .name(format!("ix-kernel-check-anon-{worker_idx}"))
      .stack_size(KERNEL_CHECK_STACK_SIZE)
      .spawn(move || {
        let mut kenv = KEnv::<Anon>::new();
        let clear_every = kernel_check_clear_every();
        let mut checks_since_clear = clear_every;
        loop {
          let work_idx = next_index.fetch_add(1, Ordering::Relaxed);
          if work_idx >= work_total {
            break;
          }
          let item = &work[work_idx];
          if checks_since_clear >= clear_every {
            kenv.clear_releasing_memory();
            checks_since_clear = 0;
          }
          let (primary_addr, result_idxs): (Address, Vec<usize>) = match item {
            AnonWorkItem::Standalone { result_idx, addr } => {
              (addr.clone(), vec![*result_idx])
            },
            AnonWorkItem::Block { primary_addr, result_idxs } => {
              (primary_addr.clone(), result_idxs.clone())
            },
          };
          let display = format!("#{}", primary_addr.hex());
          let prefix = format!("  [{}/{work_total}] {display}", work_idx + 1);
          progress_worker.begin(worker_idx, &prefix);

          let tc_start = Instant::now();
          let kid = KId::<Anon>::new(primary_addr.clone(), ());
          let check_res = {
            let mut tc =
              TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
            tc.check_const(&kid)
          };
          let elapsed = tc_start.elapsed();
          let result: CheckRes = match check_res {
            Ok(()) => Ok(()),
            Err(e) => Err((ErrKind::Kernel, format!("{e}"))),
          };

          let outcome = CheckOutcome {
            progress_index: work_idx,
            progress_total: work_total,
            display: display.clone(),
            should_pass: true,
            result: result.clone(),
            status: CheckStatus::Checked,
            elapsed: Some(elapsed),
            peak: None,
          };
          progress_worker.finish(worker_idx, &outcome);

          for &result_idx in &result_idxs {
            // Each result slot is written exactly once across the
            // entire run. `build_anon_work` assigns disjoint
            // `result_idxs` per work item; if this assertion fires,
            // that invariant has been broken (likely by a future
            // dedup refactor) and we'd silently drop the second
            // write rather than expose the bug.
            if results[result_idx].set(result.clone()).is_err() {
              debug_assert!(
                false,
                "anon work-item dedup invariant: result slot {result_idx} set twice"
              );
            }
            if let (Some(log), Err((_, msg))) =
              (failure_log_worker.as_ref(), result.as_ref())
            {
              let label = format!("#{}", addrs[result_idx].hex());
              log.record(&label, msg);
            }
          }
          checks_since_clear += 1;
        }
      }) {
      Ok(h) => h,
      Err(e) => {
        progress.stop_reporter();
        if let Some(r) = reporter.take() {
          let _ = r.join();
        }
        for h in handles {
          let _ = h.join();
        }
        return Err(format!("spawn anon worker: {e}"));
      },
    };
    handles.push(handle);
  }

  let mut panicked = false;
  for h in handles {
    if h.join().is_err() {
      panicked = true;
    }
  }
  progress.stop_reporter();
  if let Some(r) = reporter {
    let _ = r.join();
  }
  progress.log_mem_summary();
  if panicked {
    return Err("anon worker panicked".to_string());
  }

  let mut ordered: Vec<CheckRes> = Vec::with_capacity(total);
  for i in 0..total {
    match results[i].get() {
      Some(r) => ordered.push(r.clone()),
      None => {
        return Err(format!("anon worker missed result idx {i}"));
      },
    }
  }
  Ok(ordered)
}

/// FFI: typecheck every kernel-checkable constant in a `.ixe` using the
/// metadata-free anon kernel.
///
/// - Loads the env via `IxonEnv::get_anon` (discards `named` / `names` /
///   `comms` sections during deserialization).
/// - Enumerates work items by walking `env.consts` once and skipping
///   projection constants (`IPrj`/`CPrj`/`RPrj`/`DPrj`); Muts blocks
///   become block work items whose member + ctor projection addresses
///   are reconstructed deterministically via `Constant::commit`.
/// - Workers each get their own `KEnv<Anon>` and a
///   `LazyAnonIngress`-backed `TypeChecker<Anon>`. Deep refs fault in
///   lazily via the anon-mode shallow ingress (`ingress_anon_addr_shallow`).
/// - Returns `Array (Option CheckError)`, one slot per kernel-checkable
///   address discovered during enumeration.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_check_anon(
  env_path: LeanString<LeanBorrowed<'_>>,
  quiet: LeanBool<LeanBorrowed<'_>>,
  fail_out: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();
  let quiet = quiet.to_bool();
  let path = env_path.to_string();
  let fail_out_path = fail_out.to_string();
  let fail_out_path =
    if fail_out_path.is_empty() { None } else { Some(fail_out_path) };

  // mmap the .ixe directly. Section 2 consts become zero-copy windows
  // into the mapping (`LazyConstant::from_mmap_slice`), avoiding the
  // ~3 GB heap copy that `std::fs::read` would impose on mathlib.
  // Sections 3-4 (names + named) are still parse-and-discard, but
  // their decoded forms drop before `get_anon_mmap` returns.
  let t1 = Instant::now();
  let ixon_env = match IxonEnv::get_anon_mmap(std::path::Path::new(&path)) {
    Ok(env) => env,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_check_anon: failed to mmap+deserialize {path}: {e}"
      ));
    },
  };
  eprintln!(
    "[rs_kernel_check_anon] mmap+parse:  {:>8.1?} ({} consts; \
     named={} names={} comms={})",
    t1.elapsed(),
    ixon_env.const_count(),
    ixon_env.named_count(),
    ixon_env.name_count(),
    ixon_env.comm_count(),
  );

  let t2 = Instant::now();
  let (work, addrs) = match build_anon_work(&ixon_env) {
    Ok(pair) => pair,
    Err(e) => {
      return LeanIOResult::error_string(&format!(
        "rs_kernel_check_anon: build_anon_work: {e}"
      ));
    },
  };
  eprintln!(
    "[rs_kernel_check_anon] build work:  {:>8.1?} ({} items, {} targets)",
    t2.elapsed(),
    work.len(),
    addrs.len()
  );

  let failure_log: Option<Arc<FailureLog>> = match fail_out_path.as_deref() {
    None => None,
    Some(out_path) => match FailureLog::open(out_path, &path, addrs.len()) {
      Ok(log) => {
        eprintln!("[rs_kernel_check_anon] streaming failures to {out_path}");
        Some(Arc::new(log))
      },
      Err(e) => {
        return LeanIOResult::error_string(&format!(
          "rs_kernel_check_anon: failed to open fail-out file {out_path}: {e}"
        ));
      },
    },
  };

  let total = addrs.len();
  // Keep our own copy for the per-slot `(hex, result)` FFI return;
  // the runner clones internally for worker dispatch.
  let addrs_for_return = addrs.clone();
  let t3 = Instant::now();
  let ixon_env_arc = Arc::new(ixon_env);
  let results = match run_anon_checks_parallel(
    ixon_env_arc,
    work,
    addrs,
    quiet,
    failure_log.clone(),
  ) {
    Ok(r) => r,
    Err(msg) => {
      if let Some(log) = failure_log.as_ref() {
        log.finalize();
      }
      return build_uniform_error(total, &format!("[thread] {msg}"));
    },
  };

  let passed = results.iter().filter(|r| r.is_ok()).count();
  let failed = results.iter().filter(|r| r.is_err()).count();
  eprintln!(
    "[rs_kernel_check_anon] {passed}/{total} passed, {failed} failed ({:.1?})",
    t3.elapsed()
  );
  eprintln!(
    "[rs_kernel_check_anon] total:       {:>8.1?}",
    total_start.elapsed()
  );
  if let Some(log) = failure_log.as_ref() {
    log.finalize();
    eprintln!(
      "[rs_kernel_check_anon] streamed {} failure(s) to fail-out",
      log.count()
    );
  }

  build_anon_result_array(&addrs_for_return, &results)
}

// ===========================================================================
// Sharding profiler: run the anon kernel out of circuit over a `.ixe`,
// recording per-block heartbeats + the delta-unfold graph into a `.ixesp`.
// See `plans/sharding.md`.
// ===========================================================================

/// Summary returned by [`profile_anon_ixe`].
pub struct ProfileStats {
  pub targets: usize,
  pub passed: usize,
  pub failed: usize,
  pub blocks: usize,
  pub edges: usize,
  pub bytes: usize,
}

/// Map a constant address to its *block* (ingress unit): the `block` address of
/// a projection constant, otherwise the address itself.
fn profile_block_of(env: &IxonEnv, addr: &Address) -> Address {
  match env.get_const(addr) {
    Some(c) => match &c.info {
      IxonCI::IPrj(p) => p.block.clone(),
      IxonCI::CPrj(p) => p.block.clone(),
      IxonCI::RPrj(p) => p.block.clone(),
      IxonCI::DPrj(p) => p.block.clone(),
      _ => addr.clone(),
    },
    None => addr.clone(),
  }
}

/// Serialized byte length of a block constant (the ingress-cost / net weight).
#[allow(clippy::cast_possible_truncation)] // clamped to u32::MAX above
fn profile_block_size(env: &IxonEnv, block: &Address) -> u32 {
  env
    .get_const_bytes(block)
    .map_or(0, |b| b.len().min(u32::MAX as usize) as u32)
}

/// Aggregate per-constant records into a block-level [`BlockProfile`]: map each
/// consumer/producer constant to its home block, attach serialized sizes, and
/// accumulate heartbeats + delta edges.
fn build_block_profile(env: &IxonEnv, merged: &ProfileSink) -> BlockProfile {
  let mut builder = ProfileBuilder::new();
  // addr -> (home block, block serialized size), memoized.
  let mut cache: FxHashMap<Address, (Address, u32)> = FxHashMap::default();
  let mut resolve = |a: &Address| -> (Address, u32) {
    if let Some(v) = cache.get(a) {
      return v.clone();
    }
    let block = profile_block_of(env, a);
    let size = profile_block_size(env, &block);
    let v = (block, size);
    cache.insert(a.clone(), v.clone());
    v
  };
  for (consumer, rec) in &merged.records {
    let (cblock, csize) = resolve(consumer);
    builder.block(cblock.clone(), rec.fuel, csize, 1);
    for prod in &rec.producers {
      let (pblock, psize) = resolve(prod);
      builder.block(pblock.clone(), 0, psize, 0);
      builder.delta_edge(cblock.clone(), pblock);
    }
  }
  builder.finish()
}

/// Run the anon kernel over `work`, with per-worker profile recording, and
/// return `(passed, failed, merged_sink)`.
// `map_err_ignore`: the discarded `Arc`/`PoisonError` carry no useful context.
#[allow(clippy::needless_pass_by_value, clippy::map_err_ignore)]
fn run_anon_profile_parallel(
  env: Arc<IxonEnv>,
  work: Vec<AnonWorkItem>,
  isolate: bool,
  quiet: bool,
) -> Result<(usize, usize, ProfileSink), String> {
  let work_total = work.len();
  let worker_count = resolve_kernel_check_workers(work_total, quiet);
  eprintln!(
    "[rs_kernel_profile] profiling {work_total} work item(s) with {worker_count} worker(s), isolate={isolate}..."
  );
  let work = Arc::new(work);
  let next_index = Arc::new(AtomicUsize::new(0));
  let passed = Arc::new(AtomicUsize::new(0));
  let failed = Arc::new(AtomicUsize::new(0));
  let sinks: Arc<Mutex<Vec<ProfileSink>>> = Arc::new(Mutex::new(Vec::new()));

  let mut handles: Vec<thread::JoinHandle<()>> =
    Vec::with_capacity(worker_count);
  for worker_idx in 0..worker_count {
    let env = Arc::clone(&env);
    let work = Arc::clone(&work);
    let next_index = Arc::clone(&next_index);
    let passed = Arc::clone(&passed);
    let failed = Arc::clone(&failed);
    let sinks = Arc::clone(&sinks);
    let handle = thread::Builder::new()
      .name(format!("ix-kernel-profile-{worker_idx}"))
      .stack_size(KERNEL_CHECK_STACK_SIZE)
      .spawn(move || {
        let mut kenv = KEnv::<Anon>::new();
        kenv.profile_sink = Some(ProfileSink::new(isolate));
        let clear_every = kernel_check_clear_every();
        let mut checks_since_clear = clear_every;
        loop {
          let work_idx = next_index.fetch_add(1, Ordering::Relaxed);
          if work_idx >= work_total {
            break;
          }
          // `clear_releasing_memory` preserves `profile_sink`, so recording
          // accumulates across scheduled-block boundaries.
          if checks_since_clear >= clear_every {
            kenv.clear_releasing_memory();
            checks_since_clear = 0;
          }
          let primary_addr = match &work[work_idx] {
            AnonWorkItem::Standalone { addr, .. } => addr.clone(),
            AnonWorkItem::Block { primary_addr, .. } => primary_addr.clone(),
          };
          let kid = KId::<Anon>::new(primary_addr, ());
          let res = {
            let mut tc =
              TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
            let r = tc.check_const(&kid);
            // The TypeChecker is recreated per work item, so the final
            // constant's record would never be flushed by a trailing reset —
            // flush it explicitly.
            tc.finish_constant_accounting();
            r
          };
          if res.is_ok() {
            passed.fetch_add(1, Ordering::Relaxed);
          } else {
            failed.fetch_add(1, Ordering::Relaxed);
          }
          checks_since_clear += 1;
        }
        if let Some(sink) = kenv.profile_sink.take() {
          sinks.lock().unwrap().push(sink);
        }
      })
      .map_err(|e| format!("spawn profile worker: {e}"))?;
    handles.push(handle);
  }

  let mut panicked = false;
  for h in handles {
    if h.join().is_err() {
      panicked = true;
    }
  }
  if panicked {
    return Err("profile worker panicked".to_string());
  }

  let mut merged = ProfileSink::new(isolate);
  let collected = Arc::try_unwrap(sinks)
    .map_err(|_| "profile sinks still shared".to_string())?
    .into_inner()
    .map_err(|_| "profile sinks mutex poisoned".to_string())?;
  for s in collected {
    merged.merge(s);
  }
  Ok((passed.load(Ordering::Relaxed), failed.load(Ordering::Relaxed), merged))
}

/// Profile a `.ixe` out of circuit and write the `.ixesp` sidecar. Pure-Rust
/// entry point (used by the FFI wrapper and Rust tests).
pub fn profile_anon_ixe(
  path: &str,
  out: &str,
  isolate: bool,
  quiet: bool,
) -> Result<ProfileStats, String> {
  let load_start = Instant::now();
  let ixon_env = IxonEnv::get_anon_mmap(std::path::Path::new(path))
    .map_err(|e| format!("profile: mmap+deserialize {path}: {e}"))?;
  eprintln!(
    "[rs_kernel_profile] loaded {} consts in {:.1?}",
    ixon_env.const_count(),
    load_start.elapsed()
  );
  let (work, addrs) = build_anon_work(&ixon_env)?;
  let targets = addrs.len();
  let env_arc = Arc::new(ixon_env);
  let run_start = Instant::now();
  let (passed, failed, merged) =
    run_anon_profile_parallel(Arc::clone(&env_arc), work, isolate, quiet)?;
  eprintln!(
    "[rs_kernel_profile] checked {passed}/{} ({} failed) in {:.1?}",
    passed + failed,
    failed,
    run_start.elapsed()
  );
  let profile = build_block_profile(&env_arc, &merged);
  let bytes = profile.to_bytes();
  std::fs::write(out, &bytes).map_err(|e| format!("write {out}: {e}"))?;
  eprintln!(
    "[rs_kernel_profile] wrote {out}: {} blocks, {} delta edges, {} bytes",
    profile.num_blocks(),
    profile.num_edges(),
    bytes.len()
  );
  Ok(ProfileStats {
    targets,
    passed,
    failed,
    blocks: profile.num_blocks(),
    edges: profile.num_edges(),
    bytes: bytes.len(),
  })
}

/// FFI: profile a `.ixe` out of circuit and write a `.ixesp` sidecar.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_profile_anon(
  env_path: LeanString<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
  isolate: LeanBool<LeanBorrowed<'_>>,
  quiet: LeanBool<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match profile_anon_ixe(
    &env_path.to_string(),
    &out_path.to_string(),
    isolate.to_bool(),
    quiet.to_bool(),
  ) {
    Ok(s) => {
      eprintln!(
        "[rs_kernel_profile] done: {} targets, {} blocks, {} edges, {} failed",
        s.targets, s.blocks, s.edges, s.failed
      );
      LeanIOResult::ok(LeanOwned::box_usize(0))
    },
    Err(e) => {
      LeanIOResult::error_string(&format!("rs_kernel_profile_anon: {e}"))
    },
  }
}

/// FFI: partition a `.ixesp` into `num_shards` shards and write a `.ixes`
/// manifest. Prints a what-if report to stderr.
#[allow(clippy::cast_precision_loss)] // balance_pct is a small percentage
#[unsafe(no_mangle)]
pub extern "C" fn rs_shard_esp(
  esp_path: LeanString<LeanBorrowed<'_>>,
  num_shards: LeanString<LeanBorrowed<'_>>,
  balance_pct: LeanString<LeanBorrowed<'_>>,
  out_path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let num_shards = num_shards.to_string().parse::<usize>().unwrap_or(1);
  let balance_pct = balance_pct.to_string().parse::<u64>().unwrap_or(5);
  let out = out_path.to_string();
  let out_opt = if out.is_empty() { None } else { Some(out.as_str()) };
  let balance = (balance_pct as f64) / 100.0;
  match crate::ix::shard::shard_esp(
    &esp_path.to_string(),
    num_shards,
    balance,
    out_opt,
  ) {
    Ok(report) => {
      eprintln!("[rs_shard]\n{report}");
      LeanIOResult::ok(LeanOwned::box_usize(0))
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_shard_esp: {e}")),
  }
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
const DEFAULT_CHECK_CLEAR_EVERY: usize = 1;

fn env_duration_ms(var: &str, default: Duration) -> Duration {
  std::env::var(var)
    .ok()
    .and_then(|s| s.parse::<u64>().ok())
    .map_or(default, Duration::from_millis)
}

fn env_duration_ms_optional(var: &str, default: Duration) -> Option<Duration> {
  let ms = std::env::var(var)
    .ok()
    .and_then(|s| s.parse::<u64>().ok())
    .unwrap_or_else(|| u64::try_from(default.as_millis()).unwrap_or(u64::MAX));
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

fn kernel_check_clear_every() -> usize {
  env_usize("IX_KERNEL_CHECK_CLEAR_EVERY", DEFAULT_CHECK_CLEAR_EVERY).max(1)
}

/// Threshold (max cache len) above which a per-block diagnostic line is
/// emitted, when `IX_KERNEL_CHECK_DIAG=1`. Default 100k entries — empirically
/// well above the typical mathlib block, so only the heavy outliers print.
/// Override with `IX_KERNEL_CHECK_DIAG_THRESHOLD=N`.
fn kernel_check_diag_threshold() -> Option<usize> {
  let enabled = matches!(
    std::env::var("IX_KERNEL_CHECK_DIAG").as_deref(),
    Ok("1" | "true" | "on" | "yes")
  );
  if !enabled {
    return None;
  }
  Some(env_usize("IX_KERNEL_CHECK_DIAG_THRESHOLD", 100_000))
}

fn kernel_check_mem_stats_enabled() -> bool {
  // Default ON: RSS via /proc/self/status + DashMap.len() is one syscall and
  // one atomic load per progress tick (~2s). Negligible overhead, and the
  // suffix is the primary signal for diagnosing memory growth across a long
  // env-check run. Explicit `IX_KERNEL_CHECK_MEM_STATS=0|false|off|no` opts
  // out for callers who want a clean line.
  !matches!(
    std::env::var("IX_KERNEL_CHECK_MEM_STATS").as_deref(),
    Ok("0" | "false" | "off" | "no")
  )
}

/// Emit a per-block cache-size diagnostic when the just-finished block
/// pushed any single cache past `threshold` entries, or when this block
/// set a new per-worker peak. Used only with `IX_KERNEL_CHECK_DIAG=1`.
#[allow(clippy::too_many_arguments)]
fn log_block_diag_if_big<M: KernelMode>(
  kenv: &KEnv<M>,
  worker_idx: usize,
  work_idx: usize,
  work_total: usize,
  outcome: &CheckOutcome,
  threshold: usize,
  worker_peak_cache: &mut usize,
  progress: &ParallelProgress,
) {
  let sizes = kenv.cache_sizes();
  let max_cache = sizes.max();
  let is_new_peak = max_cache > *worker_peak_cache;
  let exceeds_threshold = max_cache >= threshold;
  if !is_new_peak && !exceeds_threshold {
    return;
  }
  if is_new_peak {
    *worker_peak_cache = max_cache;
  }
  let elapsed = outcome
    .elapsed
    .map_or_else(|| "?".to_string(), |d| format!("{:.1}s", d.as_secs_f64()));
  let tag = if is_new_peak { "[diag-peak]" } else { "[diag-big]" };
  progress.log(&format!(
    "{tag} w={worker_idx} block={}/{} ({}) elapsed={elapsed} max={max_cache} {sizes}",
    work_idx + 1,
    work_total,
    outcome.display,
  ));
}

fn current_rss_mib() -> Option<u64> {
  let status = std::fs::read_to_string("/proc/self/status").ok()?;
  for line in status.lines() {
    let Some(rest) = line.strip_prefix("VmRSS:") else {
      continue;
    };
    let kb = rest.split_whitespace().next()?.parse::<u64>().ok()?;
    return Some(kb.div_ceil(1024));
  }
  None
}

fn kernel_check_mem_suffix(peak_rss_mib: Option<&AtomicU64>) -> String {
  if !kernel_check_mem_stats_enabled() {
    return String::new();
  }
  let rss_now = current_rss_mib();
  if let (Some(now), Some(peak)) = (rss_now, peak_rss_mib) {
    // Monotonic max: load-then-CAS loop, but a relaxed fetch_max is simpler.
    peak.fetch_max(now, Ordering::Relaxed);
  }
  let rss =
    rss_now.map_or_else(|| "unknown".to_string(), |mib| format!("{mib}MiB"));
  format!(" · mem: rss={rss}")
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CheckStatus {
  Checked,
  CompileFailed,
  NotFound,
}

#[derive(Clone)]
struct CheckOutcome {
  progress_index: usize,
  progress_total: usize,
  display: String,
  should_pass: bool,
  result: CheckRes,
  status: CheckStatus,
  elapsed: Option<Duration>,
  peak: Option<u32>,
}

impl CheckOutcome {
  fn prefix(&self) -> String {
    format!(
      "  [{}/{}] {}",
      self.progress_index + 1,
      self.progress_total,
      self.display
    )
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

fn check_one_const<M: KernelMode, F>(
  i: usize,
  progress_index: usize,
  progress_total: usize,
  ixon_env: &IxonEnv,
  lookups: &IxonIngressLookups,
  names: &[Name],
  expect_pass: &[bool],
  ungrounded: &FxHashMap<Name, String>,
  kenv: &mut KEnv<M>,
  mut before_kernel_check: F,
) -> CheckOutcome
where
  F: FnMut(&str),
  M::MField<Vec<Name>>: CheckDupLevelParams,
{
  let name = &names[i];
  let should_pass = expect_pass.get(i).copied().unwrap_or(true);
  // In anon mode, surface the content address in the per-constant log
  // line — the kernel itself doesn't see names. We still accept names
  // as input (and resolve them via `ixon_env.named` at the FFI
  // scheduling layer), so the user's identifier is preserved in the
  // CLI surface; only the kernel-visible progress label switches to a
  // hash. Falls back to the name if the address lookup fails.
  let display = if M::HAS_META {
    name.pretty()
  } else {
    match ixon_env.lookup_name(name) {
      Some(named) => format!("#{}", named.addr.hex()),
      None => name.pretty(),
    }
  };

  if let Some(msg) = ungrounded.get(name) {
    return CheckOutcome {
      progress_index,
      progress_total,
      display,
      should_pass,
      result: Err((ErrKind::Compile, msg.clone())),
      status: CheckStatus::CompileFailed,
      elapsed: None,
      peak: None,
    };
  }

  let prefix =
    format!("  [{}/{}] {display}", progress_index + 1, progress_total);
  before_kernel_check(&prefix);

  let tc_start = Instant::now();
  let kid = match ingress_const_shallow_into_kenv_with_lookups(
    kenv, ixon_env, lookups, name,
  ) {
    Ok(kid) => kid,
    Err(msg) => {
      let elapsed = tc_start.elapsed();
      let status = if msg.contains("missing Named entry") {
        CheckStatus::NotFound
      } else {
        CheckStatus::Checked
      };
      return CheckOutcome {
        progress_index,
        progress_total,
        display,
        should_pass,
        result: Err((ErrKind::Kernel, msg)),
        status,
        elapsed: Some(elapsed),
        peak: None,
      };
    },
  };

  let (result, peak): (Result<(), String>, u32) = {
    let mut tc = TypeChecker::new_with_lazy_ixon(kenv, ixon_env, lookups);
    tc.set_debug_label(display.clone());
    let result =
      tc.check_const(&kid).map_err(|e| format_tc_error(&e, ixon_env, lookups));
    let peak = tc.def_eq_peak;
    tc.finish_constant_accounting();
    (result, peak)
  };
  let elapsed = tc_start.elapsed();

  CheckOutcome {
    progress_index,
    progress_total,
    display,
    should_pass,
    result: result.map_err(|msg| (ErrKind::Kernel, msg)),
    status: CheckStatus::Checked,
    elapsed: Some(elapsed),
    peak: Some(peak),
  }
}

// Owned arguments are consumed via the worker pool but only borrowed in this
// function body — clippy flags the by-value receivers, but transferring
// ownership keeps the call sites simpler.
#[allow(clippy::needless_pass_by_value)]
fn check_consts_loop<M: KernelMode>(
  ixon_env: Arc<IxonEnv>,
  lookups: Arc<IxonIngressLookups>,
  names: Vec<Name>,
  expect_pass: Vec<bool>,
  ungrounded: FxHashMap<Name, String>,
  work: Vec<CheckWorkItem>,
  quiet: bool,
  failure_log: Option<Arc<FailureLog>>,
) -> Vec<CheckRes>
where
  M::MField<Vec<Name>>: CheckDupLevelParams,
{
  let total = names.len();
  let work_total = work.len();
  let mut results: Vec<Option<CheckRes>> = vec![None; total];
  let slow_threshold = kernel_check_slow_threshold();

  // Terminal width is only needed for ephemeral clearing in quiet mode. In
  // verbose mode we never rewrite, so the value is ignored.
  let mut progress = Progress::new(quiet);
  let mut kenv = KEnv::<M>::new();
  let clear_every = kernel_check_clear_every();
  let mut checks_since_clear = clear_every;

  for (work_idx, item) in work.iter().enumerate() {
    if checks_since_clear >= clear_every {
      kenv.clear_releasing_memory();
      checks_since_clear = 0;
    }
    let outcome = check_one_const(
      item.primary,
      work_idx,
      work_total,
      &ixon_env,
      &lookups,
      &names,
      &expect_pass,
      &ungrounded,
      &mut kenv,
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

    for &result_idx in &item.aliases {
      results[result_idx] = Some(outcome.result.clone());
      // Stream this seed's failure to the fail-out file (if any) as soon as
      // it's known, so a long check grows the file incrementally rather
      // than dumping everything at the end.
      if let (Some(log), Err((_, msg))) =
        (failure_log.as_ref(), outcome.result.as_ref())
      {
        log.record(&names[result_idx].pretty(), msg);
      }
    }
    checks_since_clear += 1;
  }

  // Clear any trailing ephemeral label before the summary lines print.
  progress.flush();

  results
    .into_iter()
    .enumerate()
    .map(|(i, result)| {
      result.unwrap_or_else(|| {
        Err((ErrKind::Kernel, format!("kernel-check missed result index {i}")))
      })
    })
    .collect()
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
  /// Peak resident-set size (MiB) sampled at progress ticks. Updated by the
  /// reporter and printed at end-of-run when memory stats are enabled.
  peak_rss_mib: AtomicU64,
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
      peak_rss_mib: AtomicU64::new(0),
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

  /// Print a one-shot summary of memory-related telemetry collected during
  /// the run. No-op when `IX_KERNEL_CHECK_MEM_STATS` is disabled.
  fn log_mem_summary(&self) {
    if !kernel_check_mem_stats_enabled() {
      return;
    }
    // Sample one more time so the suffix reflects post-completion state and
    // peak gets a final fetch_max.
    let final_rss = current_rss_mib();
    if let Some(now) = final_rss {
      self.peak_rss_mib.fetch_max(now, Ordering::Relaxed);
    }
    let rss_now = final_rss
      .map_or_else(|| "unknown".to_string(), |mib| format!("{mib}MiB"));
    let peak = self.peak_rss_mib.load(Ordering::Relaxed);
    let peak_str =
      if peak == 0 { "unknown".to_string() } else { format!("{peak}MiB") };
    self.log(&format!(
      "[rs_kernel_check] mem summary: peak_rss={peak_str} final_rss={rss_now}"
    ));
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
    // Progress reporting is approximate by nature; usize→f64 precision loss
    // is acceptable for percentages and ETAs.
    #[allow(clippy::cast_precision_loss)]
    let pct = if self.total == 0 {
      100.0
    } else {
      (done as f64 / self.total as f64) * 100.0
    };
    let elapsed = self.started.elapsed().as_secs_f64();
    #[allow(clippy::cast_precision_loss)]
    let rate = if elapsed > 0.0 { done as f64 / elapsed } else { 0.0 };
    #[allow(clippy::cast_precision_loss)]
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
    let mem_suffix = kernel_check_mem_suffix(Some(&self.peak_rss_mib));

    self.log(&format!(
      "[rs_kernel_check] {done}/{} ({pct:.1}%) · {:.1}/s · elapsed {:.0}s{eta}{mem_suffix}{active_suffix}",
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
fn format_tc_error<M: KernelMode>(
  e: &TcError<M>,
  ixon_env: &IxonEnv,
  lookups: &IxonIngressLookups,
) -> String {
  match e {
    TcError::AppTypeMismatch { depth, .. } => {
      format!("AppTypeMismatch at depth={depth}")
    },
    TcError::FunExpected { .. } => "FunExpected".to_string(),
    TcError::UnknownConst(addr) => {
      // Address-only label in anon mode: the kernel itself doesn't
      // know names, so error messages from the anon path shouldn't
      // either.
      if !M::HAS_META {
        return format!("unknown constant ({:.12})", addr.hex());
      }
      let name = lookups.name_for_addr(addr).map_or_else(
        || {
          if ixon_env.consts.contains_key(addr) {
            "<unnamed Ixon const>".to_string()
          } else {
            "<not in Ixon env>".to_string()
          }
        },
        |n| n.pretty(),
      );
      format!("unknown constant {name} ({:.12})", addr.hex())
    },
    // Everything else has a hand-written `Display` impl in
    // `src/ix/kernel/error.rs` — prefer it over `{:?}` which dumps raw
    // KExpr internals.
    other => format!("{other}"),
  }
}

// =============================================================================
// Lean-side result construction
// =============================================================================

/// Build one `Option CheckError` object from a Rust check result.
///
/// - `Ok(())`              → `none`
/// - `Err((Kernel, msg))`  → `some (CheckError.kernelException msg)`
/// - `Err((Compile, msg))` → `some (CheckError.compileError msg)`
fn build_option_result(result: &CheckRes) -> LeanOwned {
  match result {
    Ok(()) => LeanOption::none().into(),
    Err((kind, msg)) => {
      let err_ctor = LeanIxCheckError::alloc(kind.tag());
      err_ctor.set_obj(0, LeanString::new(msg));
      LeanOption::some(err_ctor).into()
    },
  }
}

/// Build an `IO (Array (Option CheckError))` from Rust results.
///
/// The Lean caller pairs each slot with `names[i]` (the input array) for
/// display, so there's no name in the returned tuple.
fn build_result_array(results: &[CheckRes]) -> LeanIOResult<LeanOwned> {
  let arr = LeanArray::alloc(results.len());
  for (i, result) in results.iter().enumerate() {
    arr.set(i, build_option_result(result));
  }
  LeanIOResult::ok(arr)
}

/// Build an `IO (Array (String × Option CheckError))` from Rust
/// `(address, result)` pairs.
///
/// Used by `rs_kernel_check_anon` to return per-result content
/// addresses alongside the check outcome — the anon CLI has no
/// Lean-side name to associate with each result slot, so the
/// `#<hex>` address label has to come back through the FFI to keep
/// `--fail-out` and `[check]` summary lines content-addressed.
fn build_anon_result_array(
  addrs: &[Address],
  results: &[CheckRes],
) -> LeanIOResult<LeanOwned> {
  debug_assert_eq!(
    addrs.len(),
    results.len(),
    "build_anon_result_array: addrs/results length mismatch"
  );
  let arr = LeanArray::alloc(results.len());
  for (i, result) in results.iter().enumerate() {
    let hex: LeanOwned = LeanString::new(&addrs[i].hex()).into();
    let res_obj = build_option_result(result);
    let pair: LeanOwned = LeanProd::new(hex, res_obj).into();
    arr.set(i, pair);
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
  let mut compile_state =
    match compile_env_with_options(&rust_env_arc, CompileOptions::default()) {
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
    if checked.is_multiple_of(10000) && checked > 0 {
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
