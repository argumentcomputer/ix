//! FFI bridge for the Rust NbE type-checker.
//!
//! Provides `extern "C"` functions callable from Lean via `@[extern]`:
//! - `rs_check_env`: type-check all declarations using the NbE kernel
//! - `rs_check_const`: type-check a single constant by name
//! - `rs_check_consts`: type-check a batch of constants by name
//! - `rs_convert_env`: convert env to kernel types with verification

use std::ffi::{CString, c_void};
use std::sync::Arc;
use std::time::Instant;

use super::builder::LeanBuildCache;
use super::ffi_io_guard;
use super::ix::name::build_name;
use super::lean_env::lean_ptr_to_env;
use crate::ix::compile::compile_env;
use crate::ix::env::Name;
use crate::ix::kernel::check::typecheck_const;
use crate::ix::kernel::deconvert::verify_roundtrip;
use crate::ix::kernel::from_ixon::ixon_to_kenv;
use crate::ix::kernel::error::TcError;
use crate::ix::kernel::types::{Meta, MetaId};
use crate::lean::array::LeanArrayObject;
use crate::lean::nat::Nat;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core,
  lean_ctor_set, lean_io_result_mk_ok, lean_mk_string,
};

/// Build a Lean `Ix.Kernel.CheckError` from a `TcError`.
///
/// Maps all error variants to the `kernelException` constructor (tag 7)
/// with a descriptive message string, since the kernel uses `KExpr` internally
/// which doesn't directly convert to `Ix.Expr`.
unsafe fn build_check_error(err: &TcError<Meta>) -> *mut c_void {
  unsafe {
    let msg = format!("{err}");
    let c_msg = CString::new(msg)
      .unwrap_or_else(|_| CString::new("kernel exception").unwrap());
    let obj = lean_alloc_ctor(7, 1, 0); // kernelException
    lean_ctor_set(obj, 0, lean_mk_string(c_msg.as_ptr()));
    obj
  }
}

/// FFI function to type-check all declarations using the NbE checker.
/// Returns `IO (Array (Ix.Name × CheckError))`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_check_env(env_consts_ptr: *const c_void) -> *mut c_void {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let total_start = Instant::now();

    let t0 = Instant::now();
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    eprintln!("[rs_check_env] read env:    {:>8.1?}", t0.elapsed());

    // Compile through Ixon, then convert to kernel types
    let t1 = Instant::now();
    let rust_env_arc = Arc::new(rust_env);
    let compile_result = compile_env(&rust_env_arc);
    let compile_state = match compile_result {
      Ok(s) => s,
      Err(e) => {
        let msg = format!("Ixon compilation failed: {e}");
        let err: TcError<Meta> = TcError::KernelException { msg };
        let name = Name::anon();
        let mut cache = LeanBuildCache::new();
        unsafe {
          let arr = lean_alloc_array(1, 1);
          let name_obj = build_name(&mut cache, &name);
          let err_obj = build_check_error(&err);
          let pair = lean_alloc_ctor(0, 2, 0);
          lean_ctor_set(pair, 0, name_obj);
          lean_ctor_set(pair, 1, err_obj);
          lean_array_set_core(arr, 0, pair);
          return lean_io_result_mk_ok(arr);
        }
      }
    };
    eprintln!("[rs_check_env] compile env: {:>8.1?}", t1.elapsed());

    let t2 = Instant::now();
    let (kenv, prims, quot_init) = match ixon_to_kenv::<Meta>(&compile_state) {
      Ok(v) => v,
      Err(msg) => {
        let err: TcError<Meta> = TcError::KernelException { msg };
        let name = Name::anon();
        let mut cache = LeanBuildCache::new();
        unsafe {
          let arr = lean_alloc_array(1, 1);
          let name_obj = build_name(&mut cache, &name);
          let err_obj = build_check_error(&err);
          let pair = lean_alloc_ctor(0, 2, 0);
          lean_ctor_set(pair, 0, name_obj);
          lean_ctor_set(pair, 1, err_obj);
          lean_array_set_core(arr, 0, pair);
          return lean_io_result_mk_ok(arr);
        }
      }
    };
    eprintln!("[rs_check_env] ixon→kenv:  {:>8.1?} ({} consts)", t2.elapsed(), kenv.len());
    drop(compile_state);
    drop(rust_env_arc);

    // Type-check all constants, collecting errors.
    // Run on a thread with a large stack to avoid stack overflow on deeply nested expressions.
    // Errors are converted to (Name, String) to cross the thread boundary (Rc is not Send).
    let t2 = Instant::now();
    let error_strings: Vec<(Name, String)> = {
      // SAFETY: kenv/prims are only accessed from the spawned thread while this
      // thread waits on join(). No concurrent access occurs.
      let kenv_ptr = &kenv as *const _ as usize;
      let prims_ptr = &prims as *const _ as usize;
      std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024) // 64 MB stack
        .spawn(move || {
          let kenv = unsafe { &*(kenv_ptr as *const crate::ix::kernel::types::KEnv<Meta>) };
          let prims = unsafe { &*(prims_ptr as *const crate::ix::kernel::types::Primitives<Meta>) };
          const FAIL_FAST: bool = true;
          let total = kenv.len();
          let mut errors: Vec<(Name, String)> = Vec::new();
          let mut checked = 0usize;
          for (id, ci) in kenv.iter() {
            checked += 1;
            let name = ci.name().pretty();
            eprint!("[rs_check_env]   {checked}/{total} {name} ...");
            let t = Instant::now();
            if let Err(e) = typecheck_const(kenv, prims, id, quot_init) {
              eprintln!(" FAIL ({:.1?}): {e}", t.elapsed());
              errors.push((ci.name().clone(), format!("{e}")));
              if FAIL_FAST {
                eprintln!("[rs_check_env] FAIL_FAST: stopping after first error");
                break;
              }
            } else {
              eprintln!(" ok ({:.1?})", t.elapsed());
            }
          }
          errors
        })
        .expect("failed to spawn typecheck thread")
        .join()
        .expect("typecheck thread panicked")
    };
    eprintln!("[rs_check_env] typecheck:   {:>8.1?} ({} errors)", t2.elapsed(), error_strings.len());
    eprintln!("[rs_check_env] total:       {:>8.1?}", total_start.elapsed());

    let mut cache = LeanBuildCache::new();
    unsafe {
      let arr = lean_alloc_array(error_strings.len(), error_strings.len());
      for (i, (name, err_msg)) in error_strings.iter().enumerate() {
        let name_obj = build_name(&mut cache, name);
        // Build CheckError from string (kernelException constructor, tag 7)
        let c_msg = CString::new(err_msg.as_str())
          .unwrap_or_else(|_| CString::new("kernel exception").unwrap());
        let err_obj = lean_alloc_ctor(7, 1, 0);
        lean_ctor_set(err_obj, 0, lean_mk_string(c_msg.as_ptr()));
        let pair = lean_alloc_ctor(0, 2, 0); // Prod.mk
        lean_ctor_set(pair, 0, name_obj);
        lean_ctor_set(pair, 1, err_obj);
        lean_array_set_core(arr, i, pair);
      }
      lean_io_result_mk_ok(arr)
    }
  }))
}

/// Parse a dotted name string (e.g. "Nat.add") into a `Name`.
fn parse_name(s: &str) -> Name {
  let mut name = Name::anon();
  for part in s.split('.') {
    // Strip French quotes if present: «foo» → foo
    let stripped = if part.starts_with('«') && part.ends_with('»') {
      &part['«'.len_utf8()..part.len() - '»'.len_utf8()]
    } else {
      part
    };
    // Try parsing as a number (Lean.Name.num component)
    if let Ok(n) = stripped.parse::<u64>() {
      name = Name::num(name, Nat::from(n));
    } else {
      name = Name::str(name, part.to_string());
    }
  }
  name
}

/// FFI function to type-check a single constant by name using the
/// NbE checker. Returns `IO (Option CheckError)`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_check_const(
  env_consts_ptr: *const c_void,
  name_ptr: *const c_void,
) -> *mut c_void {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let name_str: &LeanStringObject = as_ref_unsafe(name_ptr.cast());
    let target_name = parse_name(&name_str.as_string());

    // Compile through Ixon, then convert to kernel types
    let rust_env_arc = Arc::new(rust_env);
    let compile_state = match compile_env(&rust_env_arc) {
      Ok(s) => s,
      Err(e) => {
        let err: TcError<Meta> = TcError::KernelException {
          msg: format!("Ixon compilation failed: {e}"),
        };
        unsafe {
          let err_obj = build_check_error(&err);
          let some = lean_alloc_ctor(1, 1, 0);
          lean_ctor_set(some, 0, err_obj);
          return lean_io_result_mk_ok(some);
        }
      }
    };
    let (kenv, prims, quot_init) = match ixon_to_kenv::<Meta>(&compile_state) {
      Ok(v) => v,
      Err(msg) => {
        let err: TcError<Meta> = TcError::KernelException { msg };
        unsafe {
          let err_obj = build_check_error(&err);
          let some = lean_alloc_ctor(1, 1, 0);
          lean_ctor_set(some, 0, err_obj);
          return lean_io_result_mk_ok(some);
        }
      }
    };
    drop(compile_state);
    drop(rust_env_arc);

    // Find the constant by name
    let target_id = kenv
      .iter()
      .find(|(_, ci)| ci.name() == &target_name)
      .map(|(id, _)| id.clone());

    match target_id {
      None => {
        let err: TcError<Meta> = TcError::KernelException {
          msg: format!("constant not found: {}", target_name.pretty()),
        };
        unsafe {
          let err_obj = build_check_error(&err);
          let some = lean_alloc_ctor(1, 1, 0);
          lean_ctor_set(some, 0, err_obj);
          lean_io_result_mk_ok(some)
        }
      }
      Some(id) => {
        match typecheck_const(&kenv, &prims, &id, quot_init) {
          Ok(()) => unsafe {
            let none = lean_alloc_ctor(0, 0, 0); // Option.none
            lean_io_result_mk_ok(none)
          },
          Err(e) => unsafe {
            let err_obj = build_check_error(&e);
            let some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, err_obj);
            lean_io_result_mk_ok(some)
          },
        }
      }
    }
  }))
}

/// FFI function to convert env to kernel types and verify correctness.
/// Returns `IO (Array String)` with diagnostics:
///   [0] = "ok" | "error: <msg>"
///   [1] = kenv size
///   [2] = prims resolved count
///   [3] = quot_init
///   [4] = verification mismatches count
///   [5+] = "missing:<name>" | "mismatch:<name>:<detail>"
#[unsafe(no_mangle)]
pub extern "C" fn rs_convert_env(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let t0 = Instant::now();
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    eprintln!("[rs_convert_env] read env:    {:>8.1?}", t0.elapsed());

    // Compile through Ixon
    let t1 = Instant::now();
    let rust_env_arc = Arc::new(rust_env);
    let compile_state = match compile_env(&rust_env_arc) {
      Ok(s) => s,
      Err(e) => {
        drop(rust_env_arc);
        unsafe {
          let arr = lean_alloc_array(1, 1);
          let c_msg =
            CString::new(format!("error: Ixon compilation failed: {e}")).unwrap_or_default();
          lean_array_set_core(arr, 0, lean_mk_string(c_msg.as_ptr()));
          return lean_io_result_mk_ok(arr);
        }
      }
    };
    eprintln!("[rs_convert_env] compile env: {:>8.1?}", t1.elapsed());

    // Convert Ixon → KEnv
    let t2 = Instant::now();
    let result = ixon_to_kenv::<Meta>(&compile_state);
    eprintln!("[rs_convert_env] ixon→kenv:  {:>8.1?}", t2.elapsed());

    match result {
      Err(msg) => {
        drop(compile_state);
        drop(rust_env_arc);
        unsafe {
          let arr = lean_alloc_array(1, 1);
          let c_msg =
            CString::new(format!("error: {msg}")).unwrap_or_default();
          lean_array_set_core(arr, 0, lean_mk_string(c_msg.as_ptr()));
          lean_io_result_mk_ok(arr)
        }
      }
      Ok((kenv, prims, quot_init)) => {
        // Verify: deconvert KEnv back to Lean types, compare against Ixon decompiled
        let t3 = Instant::now();
        let mismatches = verify_roundtrip(&compile_state, &kenv);
        eprintln!("[rs_convert_env] verify:      {:>8.1?}", t3.elapsed());
        drop(compile_state);
        drop(rust_env_arc);

        let (prims_found, missing) = prims.count_resolved();
        let base_count = 5;
        let total = base_count + missing.len() + mismatches.len();

        unsafe {
          let arr = lean_alloc_array(total, total);

          // [0] status
          let status = if mismatches.is_empty() { "ok" } else { "verify_failed" };
          let c_status = CString::new(status).unwrap();
          lean_array_set_core(arr, 0, lean_mk_string(c_status.as_ptr()));

          // [1] kenv size
          let c_size =
            CString::new(format!("{}", kenv.len())).unwrap();
          lean_array_set_core(arr, 1, lean_mk_string(c_size.as_ptr()));

          // [2] prims found
          let c_prims =
            CString::new(format!("{prims_found}")).unwrap();
          lean_array_set_core(arr, 2, lean_mk_string(c_prims.as_ptr()));

          // [3] quot_init
          let c_quot =
            CString::new(format!("{quot_init}")).unwrap();
          lean_array_set_core(arr, 3, lean_mk_string(c_quot.as_ptr()));

          // [4] mismatches count
          let c_mismatches =
            CString::new(format!("{}", mismatches.len())).unwrap();
          lean_array_set_core(arr, 4, lean_mk_string(c_mismatches.as_ptr()));

          // [5+] missing prims, then mismatches
          let mut idx = base_count;
          for name in &missing {
            let c_name =
              CString::new(format!("missing:{name}")).unwrap();
            lean_array_set_core(arr, idx, lean_mk_string(c_name.as_ptr()));
            idx += 1;
          }
          for (name, detail) in &mismatches {
            let c_entry =
              CString::new(format!("mismatch:{name}:{detail}"))
                .unwrap_or_default();
            lean_array_set_core(arr, idx, lean_mk_string(c_entry.as_ptr()));
            idx += 1;
          }

          lean_io_result_mk_ok(arr)
        }
      }
    }
  }))
}

/// FFI function to type-check a batch of constants by name.
/// Converts the env once, then checks each name.
/// Returns `IO (Array (String × Option CheckError))`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_check_consts(
  env_consts_ptr: *const c_void,
  names_ptr: *const c_void,
) -> *mut c_void {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let total_start = Instant::now();

    // Phase 1: Read Lean env from FFI pointer
    let t0 = Instant::now();
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let names_array: &LeanArrayObject = as_ref_unsafe(names_ptr.cast());
    let name_strings: Vec<String> = names_array
      .data()
      .iter()
      .map(|ptr| {
        let s: &LeanStringObject = as_ref_unsafe((*ptr).cast());
        s.as_string()
      })
      .collect();
    eprintln!("[rs_check_consts] read env:    {:>8.1?}", t0.elapsed());

    // Phase 2: Compile through Ixon, then convert to kernel types
    let t1 = Instant::now();
    let rust_env_arc = Arc::new(rust_env);
    let compile_state = match compile_env(&rust_env_arc) {
      Ok(s) => s,
      Err(e) => {
        let msg = format!("Ixon compilation failed: {e}");
        unsafe {
          let arr = lean_alloc_array(name_strings.len(), name_strings.len());
          for (i, name) in name_strings.iter().enumerate() {
            let c_name =
              CString::new(name.as_str()).unwrap_or_default();
            let name_obj = lean_mk_string(c_name.as_ptr());
            let c_msg = CString::new(format!("env conversion failed: {msg}"))
              .unwrap_or_default();
            let err_obj = lean_alloc_ctor(7, 1, 0);
            lean_ctor_set(err_obj, 0, lean_mk_string(c_msg.as_ptr()));
            let some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, err_obj);
            let pair = lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(pair, 0, name_obj);
            lean_ctor_set(pair, 1, some);
            lean_array_set_core(arr, i, pair);
          }
          return lean_io_result_mk_ok(arr);
        }
      }
    };
    eprintln!("[rs_check_consts] compile env: {:>8.1?}", t1.elapsed());

    let t2 = Instant::now();
    let (kenv, prims, quot_init) = match ixon_to_kenv::<Meta>(&compile_state) {
      Ok(v) => v,
      Err(msg) => {
        unsafe {
          let arr = lean_alloc_array(name_strings.len(), name_strings.len());
          for (i, name) in name_strings.iter().enumerate() {
            let c_name =
              CString::new(name.as_str()).unwrap_or_default();
            let name_obj = lean_mk_string(c_name.as_ptr());
            let c_msg = CString::new(format!("ixon→kenv failed: {msg}"))
              .unwrap_or_default();
            let err_obj = lean_alloc_ctor(7, 1, 0);
            lean_ctor_set(err_obj, 0, lean_mk_string(c_msg.as_ptr()));
            let some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, err_obj);
            let pair = lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(pair, 0, name_obj);
            lean_ctor_set(pair, 1, some);
            lean_array_set_core(arr, i, pair);
          }
          return lean_io_result_mk_ok(arr);
        }
      }
    };
    eprintln!("[rs_check_consts] ixon→kenv:  {:>8.1?} ({} consts)", t2.elapsed(), kenv.len());
    drop(compile_state);
    drop(rust_env_arc);

    // Phase 3: Build name → id lookup
    let t2 = Instant::now();
    let mut name_to_id: rustc_hash::FxHashMap<String, MetaId<Meta>> =
      rustc_hash::FxHashMap::default();
    for (id, ci) in kenv.iter() {
      name_to_id.insert(ci.name().pretty(), id.clone());
    }
    eprintln!("[rs_check_consts] build index: {:>8.1?}", t2.elapsed());

    // Phase 4: Type-check each constant
    eprintln!("[rs_check_consts] checking {} constants...", name_strings.len());
    let t3 = Instant::now();
    unsafe {
      let arr = lean_alloc_array(name_strings.len(), name_strings.len());
      for (i, name) in name_strings.iter().enumerate() {
        let c_name =
          CString::new(name.as_str()).unwrap_or_default();
        let name_obj = lean_mk_string(c_name.as_ptr());

        let tc_start = Instant::now();
        let target_name = parse_name(name);
        let result_obj = match name_to_id.get(&target_name.pretty()) {
          None => {
            let c_msg = CString::new(format!("constant not found: {name}"))
              .unwrap_or_default();
            let err_obj = lean_alloc_ctor(7, 1, 0);
            lean_ctor_set(err_obj, 0, lean_mk_string(c_msg.as_ptr()));
            let some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, err_obj);
            some
          }
          Some(id) => {
            eprintln!("checking {name}");
            let trace = name.contains("heapifyDown");
            if trace {
              if let Some(ci) = kenv.get(id) {
                let dump = format!(
                  "[debug] {name} type:\n{}\n{}",
                  ci.typ(),
                  match ci {
                    crate::ix::kernel::types::KConstantInfo::Definition(v) =>
                      format!("[debug] {name} value:\n{}", v.value),
                    crate::ix::kernel::types::KConstantInfo::Theorem(v) =>
                      format!("[debug] {name} value:\n{}", v.value),
                    crate::ix::kernel::types::KConstantInfo::Opaque(v) =>
                      format!("[debug] {name} value:\n{}", v.value),
                    _ =>
                      format!("[debug] {name} has no value ({})", ci.kind_name()),
                  }
                );
                let dump_path = format!("/tmp/ix_debug_{}.txt", name.replace('.', "_"));
                if let Err(e) = std::fs::write(&dump_path, &dump) {
                  eprintln!("[debug] failed to write {dump_path}: {e}");
                } else {
                  eprintln!("[debug] dumped {name} expr to {dump_path} ({} bytes)", dump.len());
                }
              }
            }
            // Run typecheck on a thread with a large stack to avoid stack overflow
            let kenv_ptr = &kenv as *const _ as usize;
            let prims_ptr = &prims as *const _ as usize;
            let id_clone = id.clone();
            let name_clone = name.clone();
            let (result, heartbeats, stats) = std::thread::Builder::new()
              .stack_size(64 * 1024 * 1024) // 64 MB stack
              .spawn(move || {
                let kenv = unsafe { &*(kenv_ptr as *const crate::ix::kernel::types::KEnv<Meta>) };
                let prims = unsafe { &*(prims_ptr as *const crate::ix::kernel::types::Primitives<Meta>) };
                let (result, heartbeats, stats) =
                  crate::ix::kernel::check::typecheck_const_with_stats_trace(
                    kenv, prims, &id_clone, quot_init, trace, &name_clone,
                  );
                // Convert error to string to cross thread boundary (Rc not Send)
                let result = result.map_err(|e| format!("{e}"));
                (result, heartbeats, stats)
              })
              .expect("failed to spawn typecheck thread")
              .join()
              .expect("typecheck thread panicked");
            // Convert error string back to TcError
            let result = result.map_err(|msg| TcError::<Meta>::KernelException { msg });
            let tc_elapsed = tc_start.elapsed();
            eprintln!("checked {name} ({tc_elapsed:.1?})");
            if tc_elapsed.as_millis() >= 10 {
              eprintln!(
                "[rs_check_consts]   {name}: {tc_elapsed:.1?} \
                 (hb={heartbeats} infer={} eval={} deq={} thunks={} forces={} hits={} cache={})",
                stats.infer_calls, stats.eval_calls, stats.def_eq_calls,
                stats.thunk_count, stats.thunk_forces, stats.thunk_hits, stats.cache_hits,
              );
              eprintln!(
                "[rs_check_consts]     quick: true={} false={}  equiv={}  ptr_succ={}  ptr_fail={}  proof_irrel={}",
                stats.quick_true, stats.quick_false, stats.equiv_hits,
                stats.ptr_success_hits, stats.ptr_failure_hits, stats.proof_irrel_hits,
              );
              eprintln!(
                "[rs_check_consts]     whnf: hit={} miss={}  equiv={}  core_hit={}  core_miss={}",
                stats.whnf_cache_hits, stats.whnf_cache_misses, stats.whnf_equiv_hits,
                stats.whnf_core_cache_hits, stats.whnf_core_cache_misses,
              );
              eprintln!(
                "[rs_check_consts]     delta: steps={}  unfold_hit={}  lazy_iters={}  same_head: check={}  hit={}",
                stats.delta_steps, stats.unfold_cache_hits, stats.lazy_delta_iters,
                stats.same_head_checks, stats.same_head_hits,
              );
              eprintln!(
                "[rs_check_consts]     step10={}  step11={}  native={}",
                stats.step10_fires, stats.step11_fires, stats.native_reduces,
              );
            }
            match result {
              Ok(()) => lean_alloc_ctor(0, 0, 0), // Option.none
              Err(e) => {
                let err_obj = build_check_error(&e);
                let some = lean_alloc_ctor(1, 1, 0);
                lean_ctor_set(some, 0, err_obj);
                some
              }
            }
          }
        };

        let pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, name_obj);
        lean_ctor_set(pair, 1, result_obj);
        lean_array_set_core(arr, i, pair);
      }
      eprintln!("[rs_check_consts] typecheck:   {:>8.1?}", t3.elapsed());
      eprintln!("[rs_check_consts] total:       {:>8.1?}", total_start.elapsed());
      lean_io_result_mk_ok(arr)
    }
  }))
}
