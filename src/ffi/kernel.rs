//! Test-only FFI: kernel constant checking.
//!
//! Exposes `rs_kernel_check_consts` for `Tests/Ix/Kernel/Tutorial.lean`, which
//! runs the full pipeline `Lean env → Ixon compile → kernel ingress →
//! typecheck` against a batch of requested constant names.
//!
//! Pipeline (mirroring the old ix_old `rs_zero_check_consts`):
//!
//! 1. Decode the Lean environment into the Rust `Env` type.
//! 2. Run `compile_env` to obtain the Ixon environment.
//! 3. Run `ixon_ingress::<Meta>` to ingress into the kernel.
//! 4. For each requested name, construct a `TypeChecker` sharing the
//!    `Arc<KEnv>` (so whnf / infer / def_eq caches accumulate across the
//!    batch) and call `check_const`.
//! 5. Return a Lean `Array (String × Option CheckError)` reporting per-name
//!    results, where `some (.kernelException msg)` signals a rejection.
//!
//! The `CheckError` ABI (tag 0 = `kernelException`) is defined in
//! `Tests/Ix/Kernel/Tutorial.lean`; see `KERNEL_EXCEPTION_TAG` below.

#![cfg(feature = "test-ffi")]

use std::sync::Arc;
use std::time::Instant;

use rustc_hash::FxHashMap;

use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanCtor, LeanIOResult, LeanList, LeanOwned,
  LeanRef, LeanString,
};

use crate::ffi::lean_env::{decode_env, parse_name};
use crate::ix::compile::compile_env;
use crate::ix::decompile::decompile_env;
use crate::ix::kernel::egress::{ixon_egress, lean_egress};
use crate::ix::kernel::env::KEnv;
use crate::ix::kernel::error::TcError;
use crate::ix::kernel::id::KId;
use crate::ix::kernel::ingress::{ixon_ingress, lean_ingress};
use crate::ix::kernel::mode::Meta;
use crate::ix::kernel::tc::TypeChecker;

/// Lean-side `CheckError` constructor tag for `kernelException`.
///
/// Defined in `Tests/Ix/Kernel/Tutorial.lean`:
/// ```lean
/// inductive CheckError where
///   | kernelException (msg : String)
///   deriving Repr
/// ```
/// The `kernelException` variant is the first (and only) constructor, so its
/// tag is `0`. If the Lean enum grows new variants ahead of this one, update
/// this constant to match.
const KERNEL_EXCEPTION_TAG: u8 = 0;

/// FFI: type-check a batch of constants through the full pipeline.
///
/// Lean signature:
/// ```lean
/// @[extern "rs_kernel_check_consts"]
/// opaque rsCheckConstsFFI :
///     @& List (Lean.Name × Lean.ConstantInfo) →
///     @& Array String →
///     @& Array Bool →
///     IO (Array (String × Option CheckError))
/// ```
///
/// `expect_pass[i]` is a hint: `true` means "good" (checker expected to
/// accept), `false` means "bad" (checker expected to reject). It only
/// influences per-constant progress logging; the actual pass/fail logic lives
/// on the Lean side.
#[unsafe(no_mangle)]
pub extern "C" fn rs_kernel_check_consts(
  env_consts: LeanList<LeanBorrowed<'_>>,
  names: LeanArray<LeanBorrowed<'_>>,
  expect_pass: LeanArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let total_start = Instant::now();

  // ---------------------------------------------------------------------
  // Decode inputs
  // ---------------------------------------------------------------------
  let t0 = Instant::now();
  let rust_env = decode_env(env_consts);
  let name_strings: Vec<String> =
    names.map(|s| s.as_string().to_string()).into_iter().collect();
  // Lean's `Bool` is an enum with two nullary constructors, so it's passed
  // unboxed: raw pointer value 0 = false, 1 = true.
  let expect_pass_vec: Vec<bool> =
    expect_pass.map(|b| b.as_raw() as usize == 1).into_iter().collect();
  eprintln!("[rs_kernel_check] read env:   {:>8.1?}", t0.elapsed());

  // ---------------------------------------------------------------------
  // Compile Lean → Ixon
  // ---------------------------------------------------------------------
  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let compile_state = match compile_env(&rust_env_arc) {
    Ok(s) => s,
    Err(e) => {
      return build_uniform_error(&name_strings, &format!("[compile] {e:?}"));
    },
  };
  eprintln!("[rs_kernel_check] compile:    {:>8.1?}", t1.elapsed());

  // ---------------------------------------------------------------------
  // Ingress Ixon → kernel
  // ---------------------------------------------------------------------
  let t2 = Instant::now();
  let (mut kenv, intern) =
    match ixon_ingress::<Meta>(&compile_state.env) {
      Ok(v) => v,
      Err(msg) => {
        return build_uniform_error(
          &name_strings,
          &format!("[ingress] {msg}"),
        );
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

  // Build Lean-name-string → KId map by iterating `kenv` itself. This
  // guarantees we look up by the exact KIds that ingress inserted, sidestepping
  // any risk of reconstruction mismatch (e.g. Muts-block member naming vs
  // `named` map keys).
  let mut name_to_id: FxHashMap<String, KId<Meta>> = FxHashMap::default();
  for (kid, _kconst) in kenv.iter() {
    let lean_name = format!("{}", kid.name);
    name_to_id.insert(lean_name, kid);
  }
  let total = name_strings.len();
  eprintln!("[rs_kernel_check] checking {total} constants...");
  let t3 = Instant::now();

  // ---------------------------------------------------------------------
  // Per-constant checking on a 256 MB stack
  // ---------------------------------------------------------------------
  // Deep recursor expansions push the Rust stack. A dedicated thread with a
  // large stack matches the old ix_old pattern.
  let results = match run_checks_on_large_stack(
    kenv.clone(),
    name_to_id,
    name_strings.clone(),
    expect_pass_vec,
  ) {
    Ok(r) => r,
    Err(msg) => {
      return build_uniform_error(
        &name_strings,
        &format!("[thread] {msg}"),
      );
    },
  };

  let passed = results.iter().filter(|(_, r)| r.is_ok()).count();
  let failed = results.iter().filter(|(_, r)| r.is_err()).count();
  eprintln!(
    "[rs_kernel_check] {passed}/{total} passed, {failed} failed ({:.1?})",
    t3.elapsed()
  );
  eprintln!("[rs_kernel_check] total:      {:>8.1?}", total_start.elapsed());

  build_result_array(&results)
}

// =============================================================================
// Checking loop (runs on a dedicated large-stack thread)
// =============================================================================

fn run_checks_on_large_stack(
  kenv: Arc<KEnv<Meta>>,
  name_to_id: FxHashMap<String, KId<Meta>>,
  name_strings: Vec<String>,
  expect_pass: Vec<bool>,
) -> Result<Vec<(String, Result<(), String>)>, String> {
  std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(move || check_consts_loop(kenv, name_to_id, name_strings, expect_pass))
    .map_err(|e| format!("failed to spawn kernel-check thread: {e}"))?
    .join()
    .map_err(|_| "kernel-check thread panicked".to_string())
}

fn check_consts_loop(
  kenv: Arc<KEnv<Meta>>,
  name_to_id: FxHashMap<String, KId<Meta>>,
  name_strings: Vec<String>,
  expect_pass: Vec<bool>,
) -> Vec<(String, Result<(), String>)> {
  let total = name_strings.len();
  let mut results: Vec<(String, Result<(), String>)> = Vec::with_capacity(total);

  for (i, raw_name) in name_strings.iter().enumerate() {
    let should_pass = expect_pass.get(i).copied().unwrap_or(true);

    // The test runner passes display-form names (e.g. "Nat.succ"). `name_to_id`
    // is keyed by `format!("{}", Name)`, which matches — but in the rare case
    // where the caller passes a raw-form string we parse-and-reformat to get
    // the canonical key.
    let pretty = format!("{}", parse_name(raw_name));
    let kid = match name_to_id
      .get(raw_name)
      .or_else(|| name_to_id.get(&pretty))
    {
      Some(id) => id.clone(),
      None => {
        eprintln!("  [{}/{}] ? {raw_name}: not found", i + 1, total);
        results.push((raw_name.clone(), Err(format!("not found: {raw_name}"))));
        continue;
      },
    };

    eprint!("  [{}/{}] {raw_name} ... ", i + 1, total);

    let tc_start = Instant::now();
    let mut tc = TypeChecker::new(kenv.clone());
    let result = tc.check_const(&kid).map_err(|e| format_tc_error(&e));
    let elapsed = tc_start.elapsed();
    let peak = tc.def_eq_peak;

    match (&result, should_pass) {
      (Ok(()), true) => eprintln!("ok ({elapsed:.1?}, depth={peak})"),
      (Ok(()), false) => {
        eprintln!("UNEXPECTED PASS ({elapsed:.1?}, depth={peak})")
      },
      (Err(msg), false) => eprintln!("REJECTED ({elapsed:.1?}): {msg}"),
      (Err(msg), true) => {
        eprintln!("FAIL ({elapsed:.1?}, depth={peak}): {msg}")
      },
    }
    results.push((raw_name.clone(), result));
  }

  results
}

/// Format a `TcError` for user-facing Lean-side display. For the two cases we
/// hit most often we emit a human-tuned multi-line message; everything else
/// falls through to `Debug`.
fn format_tc_error(e: &TcError<Meta>) -> String {
  match e {
    TcError::AppTypeMismatch { a_ty, dom, depth } => {
      format!("AppTypeMismatch at depth={depth}\n    a_ty = {a_ty}\n    dom  = {dom}")
    },
    TcError::FunExpected { e, whnf } => {
      format!("FunExpected\n    e    = {e}\n    whnf = {whnf}")
    },
    other => format!("{other:?}"),
  }
}

// =============================================================================
// Lean-side result construction
// =============================================================================

/// Build an `IO (Array (String × Option CheckError))` from Rust results.
///
/// - `Ok(())`  → `(name, none)`
/// - `Err(msg)`→ `(name, some (CheckError.kernelException msg))`
fn build_result_array(
  results: &[(String, Result<(), String>)],
) -> LeanIOResult<LeanOwned> {
  let arr = LeanArray::alloc(results.len());
  for (i, (name, result)) in results.iter().enumerate() {
    let name_obj = LeanString::new(name);

    let option_obj: LeanOwned = match result {
      Ok(()) => {
        // `Option.none` — tag 0, zero fields, zero scalars.
        LeanCtor::alloc(0, 0, 0).into()
      },
      Err(msg) => {
        // `CheckError.kernelException msg` — tag 0, one object field.
        let err_ctor = LeanCtor::alloc(KERNEL_EXCEPTION_TAG, 1, 0);
        err_ctor.set(0, LeanString::new(msg));
        // `Option.some err` — tag 1, one object field.
        let some_ctor = LeanCtor::alloc(1, 1, 0);
        some_ctor.set(0, err_ctor);
        some_ctor.into()
      },
    };

    // Product `(String, Option CheckError)` — tag 0, two object fields.
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, name_obj);
    pair.set(1, option_obj);
    arr.set(i, pair);
  }
  LeanIOResult::ok(arr)
}

/// Build a result array where every requested name is reported as failed with
/// the same error message. Used when compile/ingress/thread setup fails before
/// per-constant checking can begin.
fn build_uniform_error(
  names: &[String],
  msg: &str,
) -> LeanIOResult<LeanOwned> {
  let results: Vec<(String, Result<(), String>)> =
    names.iter().map(|n| (n.clone(), Err(msg.to_string()))).collect();
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
  let mut compile_state = match compile_env(&rust_env_arc) {
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
            for (i, (r1, r2)) in a.rules.iter().zip(b.rules.iter()).enumerate() {
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
        for (i, ((n1, v1), (_, v2))) in
          kvs1.iter().zip(kvs2.iter()).enumerate()
        {
          use crate::ix::env::hash_data_value;
          let mut h1 = blake3::Hasher::new();
          let mut h2 = blake3::Hasher::new();
          hash_data_value(v1, &mut h1);
          hash_data_value(v2, &mut h2);
          if h1.finalize() != h2.finalize() {
            val_diffs
              .push(format!("mdata[{i}] key={n1}: value hash differs"));
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
