//! FFI bridge for the Rust NbE type-checker.
//!
//! Provides `extern "C"` functions callable from Lean via `@[extern]`:
//! - `rs_check_env`: type-check all declarations using the NbE kernel
//! - `rs_check_const`: type-check a single constant by name
//! - `rs_check_consts`: type-check a batch of constants by name
//! - `rs_convert_env`: convert env to kernel types with verification

use std::ffi::{CString, c_void};
use std::time::Instant;

use super::builder::LeanBuildCache;
use super::ffi_io_guard;
use super::ix::name::build_name;
use super::lean_env::lean_ptr_to_env;
use crate::ix::env::Name;
use crate::ix::kernel::check::{typecheck_const, typecheck_const_with_stats};
use crate::lean::nat::Nat;
use crate::ix::kernel::convert::{convert_env, verify_conversion};
use crate::ix::kernel::error::TcError;
use crate::ix::kernel::types::Meta;
use crate::lean::array::LeanArrayObject;
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

    // Convert env::Env to kernel types
    let t1 = Instant::now();
    let (kenv, prims, quot_init) = match convert_env::<Meta>(&rust_env) {
      Ok(v) => v,
      Err(msg) => {
        // Return a single-element array with the conversion error
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
    eprintln!("[rs_check_env] convert env: {:>8.1?} ({} consts)", t1.elapsed(), kenv.len());
    drop(rust_env); // Free env memory before type-checking

    // Type-check all constants, collecting errors
    let t2 = Instant::now();
    let mut errors: Vec<(Name, TcError<Meta>)> = Vec::new();
    for (addr, ci) in &kenv {
      if let Err(e) = typecheck_const(&kenv, &prims, addr, quot_init) {
        errors.push((ci.name().clone(), e));
      }
    }
    eprintln!("[rs_check_env] typecheck:   {:>8.1?} ({} errors)", t2.elapsed(), errors.len());
    eprintln!("[rs_check_env] total:       {:>8.1?}", total_start.elapsed());

    let mut cache = LeanBuildCache::new();
    unsafe {
      let arr = lean_alloc_array(errors.len(), errors.len());
      for (i, (name, tc_err)) in errors.iter().enumerate() {
        let name_obj = build_name(&mut cache, name);
        let err_obj = build_check_error(tc_err);
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

    // Convert env::Env to kernel types
    let (kenv, prims, quot_init) = match convert_env::<Meta>(&rust_env) {
      Ok(v) => v,
      Err(msg) => {
        let err: TcError<Meta> = TcError::KernelException { msg };
        unsafe {
          let err_obj = build_check_error(&err);
          let some = lean_alloc_ctor(1, 1, 0); // Option.some
          lean_ctor_set(some, 0, err_obj);
          return lean_io_result_mk_ok(some);
        }
      }
    };
    drop(rust_env);

    // Find the constant by name
    let target_addr = kenv
      .iter()
      .find(|(_, ci)| ci.name() == &target_name)
      .map(|(addr, _)| addr.clone());

    match target_addr {
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
      Some(addr) => {
        match typecheck_const(&kenv, &prims, &addr, quot_init) {
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

    let t1 = Instant::now();
    let result = convert_env::<Meta>(&rust_env);
    eprintln!("[rs_convert_env] convert env: {:>8.1?}", t1.elapsed());

    match result {
      Err(msg) => {
        drop(rust_env);
        unsafe {
          let arr = lean_alloc_array(1, 1);
          let c_msg =
            CString::new(format!("error: {msg}")).unwrap_or_default();
          lean_array_set_core(arr, 0, lean_mk_string(c_msg.as_ptr()));
          lean_io_result_mk_ok(arr)
        }
      }
      Ok((kenv, prims, quot_init)) => {
        // Verify conversion correctness
        let t2 = Instant::now();
        let mismatches = verify_conversion(&rust_env, &kenv);
        eprintln!("[rs_convert_env] verify:      {:>8.1?}", t2.elapsed());
        drop(rust_env);

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

    // Phase 2: Convert env to kernel types
    let t1 = Instant::now();
    let (kenv, prims, quot_init) = match convert_env::<Meta>(&rust_env) {
      Ok(v) => v,
      Err(msg) => {
        // Return array with conversion error for every name
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
    eprintln!("[rs_check_consts] convert env: {:>8.1?} ({} consts)", t1.elapsed(), kenv.len());
    drop(rust_env);

    // Phase 3: Build name → address lookup
    let t2 = Instant::now();
    let mut name_to_addr =
      rustc_hash::FxHashMap::default();
    for (addr, ci) in &kenv {
      name_to_addr.insert(ci.name().pretty(), addr.clone());
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
        let result_obj = match name_to_addr.get(&target_name.pretty()) {
          None => {
            let c_msg = CString::new(format!("constant not found: {name}"))
              .unwrap_or_default();
            let err_obj = lean_alloc_ctor(7, 1, 0);
            lean_ctor_set(err_obj, 0, lean_mk_string(c_msg.as_ptr()));
            let some = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(some, 0, err_obj);
            some
          }
          Some(addr) => {
            let trace = name.contains("parseWith");
            let (result, heartbeats, stats) =
              crate::ix::kernel::check::typecheck_const_with_stats_trace(
                &kenv, &prims, addr, quot_init, trace,
              );
            let tc_elapsed = tc_start.elapsed();
            if tc_elapsed.as_millis() >= 10 {
              eprintln!(
                "[rs_check_consts]   {name}: {tc_elapsed:.1?} \
                 (hb={heartbeats} infer={} eval={} deq={} thunks={} forces={} hits={} cache={})",
                stats.infer_calls, stats.eval_calls, stats.def_eq_calls,
                stats.thunk_count, stats.thunk_forces, stats.thunk_hits, stats.cache_hits,
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
