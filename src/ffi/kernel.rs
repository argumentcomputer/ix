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
//! 3. Run `ixon_to_zenv::<Meta>` to ingress into the kernel.
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
use crate::ix::kernel::egress::egress_env;
use crate::ix::kernel::env::KEnv;
use crate::ix::kernel::error::TcError;
use crate::ix::kernel::id::KId;
use crate::ix::kernel::ingress::ixon_to_zenv;
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
    match ixon_to_zenv::<Meta>(&compile_state.env) {
      Ok(v) => v,
      Err(msg) => {
        return build_uniform_error(
          &name_strings,
          &format!("[ingress] {msg}"),
        );
      },
    };
  // FIXME: `ixon_to_zenv` returns a populated `InternTable` separately from
  // the fresh, empty one inside `KEnv::new()`. The TypeChecker reads
  // `env.intern`, so we have to swap. When ingress is refactored to populate
  // `kenv.intern` directly (and the function is renamed to `ixon_to_kenv`),
  // this line goes away.
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
  let mut anon_count = 0usize;
  let mut sample_names: Vec<String> = Vec::new();
  for (kid, _kconst) in kenv.iter() {
    let lean_name = format!("{}", kid.name);
    if lean_name.is_empty() || lean_name == "[anonymous]" {
      anon_count += 1;
    }
    if sample_names.len() < 10 && !lean_name.is_empty() {
      sample_names.push(lean_name.clone());
    }
    name_to_id.insert(lean_name, kid);
  }
  eprintln!(
    "[rs_kernel_check] name_to_id: {} entries ({} anonymous), sample: {:?}",
    name_to_id.len(),
    anon_count,
    sample_names
  );

  // Specifically probe a few names we know we'll ask for.
  for probe in &["Acc", "Acc.intro", "Acc.rec", "Nat", "Nat.succ", "Eq"] {
    let present = name_to_id.contains_key(*probe);
    eprintln!("[rs_kernel_check] probe '{probe}': {present}");
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
// Kernel ingress + egress roundtrip
// =============================================================================
//
// End-to-end check of the ingress pipeline WITHOUT typechecking: decode the
// Lean env, compile to Ixon, ingress into `KEnv<Meta>`, egress back to
// `crate::ix::env::Env`, then compare each constant's type/value expression
// against the original (by content hash, with a structural diff walker to
// pinpoint the mismatch when hashes disagree).
//
// This isolates ingress correctness from kernel-level reasoning, so if it
// succeeds but `rs_kernel_check_consts` fails then we know the bug lives in
// the check side (or in how we're looking up constants post-ingress).

/// FFI: exercise the full pipeline Lean env → Ixon → kernel → Lean (egress)
/// and compare each constant against the original.
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
  eprintln!("[rs_kernel_roundtrip] read env:    {:>8.1?}", t0.elapsed());

  let t1 = Instant::now();
  let rust_env_arc = Arc::new(rust_env);
  let compile_state = match compile_env(&rust_env_arc) {
    Ok(s) => s,
    Err(e) => {
      return build_string_array(&[format!("compile error: {e:?}")]);
    },
  };
  eprintln!("[rs_kernel_roundtrip] compile:     {:>8.1?}", t1.elapsed());

  let t2 = Instant::now();
  let (mut kenv, intern) = match ixon_to_zenv::<Meta>(&compile_state.env) {
    Ok(v) => v,
    Err(msg) => {
      return build_string_array(&[format!("ingress error: {msg}")]);
    },
  };
  kenv.intern = intern;
  eprintln!(
    "[rs_kernel_roundtrip] ingress:     {:>8.1?} ({} consts)",
    t2.elapsed(),
    kenv.len()
  );

  // Diagnostic: sample KId names from kenv and probe for tutorial targets.
  // Tells us whether ingress populated `kid.name` with meaningful values or
  // left them as `Name::anon()`, which would make all tutorial lookups fail.
  diagnose_kenv_names(
    &kenv,
    &compile_state.env,
    &[
      "Acc",
      "Acc.intro",
      "Acc.rec",
      "Nat",
      "Nat.succ",
      "Eq",
      "Prod",
      "List.rec",
      "Tests.Ix.Kernel.TutorialDefs.TRTree",
      "Tests.Ix.Kernel.TutorialDefs.TN",
    ],
  );

  // Diagnostic: check mdata-key name registration. `resolve_kvmap` uses
  // `ixon_env.get_name(addr)` to reconstruct each mdata key, and silently
  // drops entries where the name isn't registered. If `_recApp` (or other
  // metadata keys) aren't in `ixon_env.names`, mdata layers get stripped.
  {
    use crate::ix::address::Address;
    use crate::ix::env::Name;
    let probes = ["_recApp", "_patWithRef", "_private", "pp.universes"];
    for probe in &probes {
      let name = Name::str(Name::anon(), probe.to_string());
      let addr = Address::from_blake3_hash(*name.get_hash());
      let resolved = compile_state.env.get_name(&addr);
      eprintln!(
        "[diag] mdata key '{probe}': addr={} in ixon_env.names? {}",
        addr.hex()[..12].to_string(),
        resolved.is_some()
      );
    }
  }

  // Egress ZEnv → Lean env.
  let t3 = Instant::now();
  let egressed_env = egress_env(&kenv);
  eprintln!(
    "[rs_kernel_roundtrip] egress:      {:>8.1?} ({} consts)",
    t3.elapsed(),
    egressed_env.len()
  );

  // Compare egressed env against original, content-hash by content-hash.
  let t4 = Instant::now();
  let (errors, checked, not_found) =
    compare_envs(&rust_env_arc, &egressed_env);
  eprintln!(
    "[rs_kernel_roundtrip] verify:      {:>8.1?} (checked {checked}, not_found {not_found}, errors {})",
    t4.elapsed(),
    errors.len()
  );

  drop(compile_state);
  drop(rust_env_arc);

  eprintln!(
    "[rs_kernel_roundtrip] total:       {:>8.1?}",
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

/// Diagnostic: report the shape of `kid.name` in `kenv` vs what
/// `compile_state.env.named` contains for the same Lean-visible names.
///
/// Prints:
///   - total KId count and how many have `Name::anon()` (empty) names
///   - the first 10 non-empty `format!("{}", kid.name)` values
///   - for each probe name, whether `kenv` has a KId formatting to that name,
///     whether `compile_state.env.named` has it, and if so the addr prefix.
///
/// This lets us triangulate: if `named` has "Acc" but `kenv` doesn't, ingress
/// is dropping it; if `kenv` has it under a different formatted name, our
/// key-formatting assumption is wrong; if neither has it, compile itself didn't
/// register it.
fn diagnose_kenv_names(
  kenv: &KEnv<Meta>,
  ixon_env: &crate::ix::ixon::env::Env,
  probes: &[&str],
) {
  use crate::ix::address::Address;

  let mut by_name: FxHashMap<String, KId<Meta>> = FxHashMap::default();
  let mut by_addr: FxHashMap<Address, Vec<KId<Meta>>> = FxHashMap::default();
  let mut anon_count = 0usize;
  let mut sample: Vec<String> = Vec::new();

  for (kid, _kc) in kenv.iter() {
    let n = format!("{}", kid.name);
    if n.is_empty() || n == "[anonymous]" {
      anon_count += 1;
    } else if sample.len() < 10 {
      sample.push(n.clone());
    }
    by_addr.entry(kid.addr.clone()).or_default().push(kid.clone());
    // Last write wins on collisions; fine for diagnostic purposes.
    by_name.insert(n, kid);
  }

  eprintln!(
    "[diag] kenv has {} KIds total ({} unique addrs); {} anonymous; sample non-anon names: {:?}",
    kenv.len(),
    by_addr.len(),
    anon_count,
    sample
  );

  for probe in probes {
    let in_kenv = by_name.get(*probe);
    let named_entry = ixon_env
      .named
      .iter()
      .find(|e| format!("{}", e.key()) == *probe)
      .map(|e| (e.value().addr.clone(), e.value().addr.hex()[..12].to_string()));

    match (in_kenv, &named_entry) {
      (Some(kid), Some((_, named_addr))) => {
        let kenv_addr = kid.addr.hex()[..12].to_string();
        let match_str = if kenv_addr == *named_addr { "==" } else { "!=" };
        eprintln!(
          "[diag] '{probe}': kenv addr={kenv_addr} {match_str} named addr={named_addr}"
        );
      },
      (Some(kid), None) => {
        eprintln!(
          "[diag] '{probe}': in kenv (addr={}) but NOT in compile_state.env.named",
          kid.addr.hex()[..12].to_string()
        );
      },
      (None, Some((addr, named_addr))) => {
        // Probe by address into kenv — maybe the KId is there under a
        // different name (anon, transformed, or with surgery).
        let by_this_addr = by_addr.get(addr);
        match by_this_addr {
          Some(kids) => {
            let names_under_addr: Vec<String> =
              kids.iter().map(|k| format!("{}", k.name)).collect();
            eprintln!(
              "[diag] '{probe}': named addr={named_addr} present in kenv under other names: {:?}",
              names_under_addr
            );
          },
          None => {
            // Check what IxonCI variant lives at that address.
            let ci_variant = ixon_env
              .get_const(addr)
              .map(|c| match &c.info {
                crate::ix::ixon::constant::ConstantInfo::Defn(_) => "Defn",
                crate::ix::ixon::constant::ConstantInfo::Recr(_) => "Recr",
                crate::ix::ixon::constant::ConstantInfo::Axio(_) => "Axio",
                crate::ix::ixon::constant::ConstantInfo::Quot(_) => "Quot",
                crate::ix::ixon::constant::ConstantInfo::Muts(_) => "Muts",
                crate::ix::ixon::constant::ConstantInfo::IPrj(_) => "IPrj",
                crate::ix::ixon::constant::ConstantInfo::CPrj(_) => "CPrj",
                crate::ix::ixon::constant::ConstantInfo::RPrj(_) => "RPrj",
                crate::ix::ixon::constant::ConstantInfo::DPrj(_) => "DPrj",
              })
              .unwrap_or("<get_const None>");
            eprintln!(
              "[diag] '{probe}': named addr={named_addr} (IxonCI::{ci_variant}) absent from kenv — ingress dropped it"
            );
          },
        }
      },
      (None, None) => {
        eprintln!(
          "[diag] '{probe}': absent from both compile_state.env.named AND kenv — compile didn't register it"
        );
      },
    }
  }
}
