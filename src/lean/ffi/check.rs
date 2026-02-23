//! FFI bridge for the Rust kernel type-checker.
//!
//! Provides `extern "C"` function callable from Lean via `@[extern]`:
//! - `rs_check_env`: type-check all declarations in a Lean environment

use std::ffi::{CString, c_void};

use super::builder::LeanBuildCache;
use super::ffi_io_guard;
use super::ix::expr::build_expr;
use super::ix::name::build_name;
use super::lean_env::lean_ptr_to_env;
use crate::ix::env::{ConstantInfo, Name};
use crate::ix::kernel::dag_tc::{DagTypeChecker, dag_check_env};
use crate::ix::kernel::error::TcError;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core,
  lean_ctor_set, lean_ctor_set_uint64, lean_io_result_mk_ok, lean_mk_string,
};

/// Build a Lean `Ix.Kernel.CheckError` constructor from a Rust `TcError`.
///
/// Constructor tags (must match the Lean `inductive CheckError`):
/// - 0: typeExpected (2 obj: expr, inferred)
/// - 1: functionExpected (2 obj: expr, inferred)
/// - 2: typeMismatch (3 obj: expected, found, expr)
/// - 3: defEqFailure (2 obj: lhs, rhs)
/// - 4: unknownConst (1 obj: name)
/// - 5: duplicateUniverse (1 obj: name)
/// - 6: freeBoundVariable (0 obj + 8 byte scalar: idx)
/// - 7: kernelException (1 obj: msg)
unsafe fn build_check_error(
  cache: &mut LeanBuildCache,
  err: &TcError,
) -> *mut c_void {
  unsafe {
    match err {
      TcError::TypeExpected { expr, inferred } => {
        let obj = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(obj, 0, build_expr(cache, expr));
        lean_ctor_set(obj, 1, build_expr(cache, inferred));
        obj
      },
      TcError::FunctionExpected { expr, inferred } => {
        let obj = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(obj, 0, build_expr(cache, expr));
        lean_ctor_set(obj, 1, build_expr(cache, inferred));
        obj
      },
      TcError::TypeMismatch { expected, found, expr } => {
        let obj = lean_alloc_ctor(2, 3, 0);
        lean_ctor_set(obj, 0, build_expr(cache, expected));
        lean_ctor_set(obj, 1, build_expr(cache, found));
        lean_ctor_set(obj, 2, build_expr(cache, expr));
        obj
      },
      TcError::DefEqFailure { lhs, rhs } => {
        let obj = lean_alloc_ctor(3, 2, 0);
        lean_ctor_set(obj, 0, build_expr(cache, lhs));
        lean_ctor_set(obj, 1, build_expr(cache, rhs));
        obj
      },
      TcError::UnknownConst { name } => {
        let obj = lean_alloc_ctor(4, 1, 0);
        lean_ctor_set(obj, 0, build_name(cache, name));
        obj
      },
      TcError::DuplicateUniverse { name } => {
        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, build_name(cache, name));
        obj
      },
      TcError::FreeBoundVariable { idx } => {
        let obj = lean_alloc_ctor(6, 0, 8);
        lean_ctor_set_uint64(obj, 0, *idx);
        obj
      },
      TcError::KernelException { msg } => {
        let c_msg = CString::new(msg.as_str())
          .unwrap_or_else(|_| CString::new("kernel exception").unwrap());
        let obj = lean_alloc_ctor(7, 1, 0);
        lean_ctor_set(obj, 0, lean_mk_string(c_msg.as_ptr()));
        obj
      },
    }
  }
}

/// FFI function to type-check all declarations in a Lean environment using the
/// Rust kernel. Returns `IO (Array (Ix.Name × CheckError))`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_check_env(env_consts_ptr: *const c_void) -> *mut c_void {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let errors = dag_check_env(&rust_env);
    let mut cache = LeanBuildCache::new();
    unsafe {
      let arr = lean_alloc_array(errors.len(), errors.len());
      for (i, (name, tc_err)) in errors.iter().enumerate() {
        let name_obj = build_name(&mut cache, name);
        let err_obj = build_check_error(&mut cache, tc_err);
        let pair = lean_alloc_ctor(0, 2, 0); // Prod.mk
        lean_ctor_set(pair, 0, name_obj);
        lean_ctor_set(pair, 1, err_obj);
        lean_array_set_core(arr, i, pair);
      }
      lean_io_result_mk_ok(arr)
    }
  }))
}

/// Parse a dotted name string (e.g. "ISize.toInt16_ofIntLE") into a `Name`.
fn parse_name(s: &str) -> Name {
  let mut name = Name::anon();
  for part in s.split('.') {
    name = Name::str(name, part.to_string());
  }
  name
}

/// FFI function to type-check a single constant by name.
/// Takes the environment and a dotted name string.
/// Returns `IO (Option CheckError)` — `none` on success, `some err` on failure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_check_const(
  env_consts_ptr: *const c_void,
  name_ptr: *const c_void,
) -> *mut c_void {
  ffi_io_guard(std::panic::AssertUnwindSafe(|| {
    eprintln!("[rs_check_const] entered FFI");
    let rust_env = lean_ptr_to_env(env_consts_ptr);
    let name_str: &LeanStringObject = as_ref_unsafe(name_ptr.cast());
    let name = parse_name(&name_str.as_string());
    eprintln!("[rs_check_const] checking: {}", name.pretty());

    let ci = match rust_env.get(&name) {
      Some(ci) => {
        match ci {
          ConstantInfo::DefnInfo(d) => {
            eprintln!("[rs_check_const] type: {:#?}", d.cnst.typ);
            eprintln!("[rs_check_const] value: {:#?}", d.value);
            eprintln!("[rs_check_const] hints: {:?}", d.hints);
          },
          _ => {},
        }
        ci
      },
      None => {
        // Return some (kernelException "not found")
        let err = TcError::KernelException {
          msg: format!("constant not found: {}", name.pretty()),
        };
        let mut cache = LeanBuildCache::new();
        unsafe {
          let err_obj = build_check_error(&mut cache, &err);
          let some = lean_alloc_ctor(1, 1, 0); // Option.some
          lean_ctor_set(some, 0, err_obj);
          return lean_io_result_mk_ok(some);
        }
      },
    };

    let mut tc = DagTypeChecker::new(&rust_env);
    match tc.check_declar(ci) {
      Ok(()) => unsafe {
        // Option.none = ctor tag 0, 0 fields
        let none = lean_alloc_ctor(0, 0, 0);
        lean_io_result_mk_ok(none)
      },
      Err(e) => {
        let mut cache = LeanBuildCache::new();
        unsafe {
          let err_obj = build_check_error(&mut cache, &e);
          let some = lean_alloc_ctor(1, 1, 0); // Option.some
          lean_ctor_set(some, 0, err_obj);
          lean_io_result_mk_ok(some)
        }
      },
    }
  }))
}
