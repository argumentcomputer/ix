pub mod aiur;
pub mod byte_array;
pub mod keccak;
pub mod lean_env;
pub mod unsigned;

// Modular FFI structure
pub mod builder; // IxEnvBuilder struct
pub mod compile; // Compilation: rs_compile_env_full, rs_compile_phases, etc.
pub mod graph; // Graph/SCC: rs_build_ref_graph, rs_compute_sccs
pub mod ix; // Ix types: Name, Level, Expr, ConstantInfo, Environment
pub mod ixon; // Ixon types: Univ, Expr, Constant, metadata
pub mod primitives; // Primitives: rs_roundtrip_nat, rs_roundtrip_string, etc.

use std::ffi::{CString, c_void};

use crate::lean::{
  lean::{lean_io_result_mk_error, lean_mk_io_user_error, lean_mk_string},
  lean_array_to_vec, lean_sarray_data, lean_unbox_u32,
};

/// Guard an FFI function that returns a Lean IO result against panics.
/// On panic, returns a Lean IO error with the panic message instead of
/// unwinding across the `extern "C"` boundary (which is undefined behavior).
pub(crate) fn ffi_io_guard<F>(f: F) -> *mut c_void
where
  F: FnOnce() -> *mut c_void + std::panic::UnwindSafe,
{
  match std::panic::catch_unwind(f) {
    Ok(result) => result,
    Err(panic_info) => {
      let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
        format!("FFI panic: {s}")
      } else if let Some(s) = panic_info.downcast_ref::<String>() {
        format!("FFI panic: {s}")
      } else {
        "FFI panic: unknown".to_string()
      };
      let c_msg = CString::new(msg).unwrap_or_else(|_| {
        CString::new("FFI panic: (invalid message)").unwrap()
      });
      unsafe {
        let lean_msg = lean_mk_string(c_msg.as_ptr());
        let lean_err = lean_mk_io_user_error(lean_msg);
        lean_io_result_mk_error(lean_err).cast()
      }
    },
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_boxed_u32s_are_equivalent_to_bytes(
  u32s: *const c_void,
  bytes: *const c_void,
) -> bool {
  let u32s = lean_array_to_vec(u32s, lean_unbox_u32)
    .into_iter()
    .flat_map(u32::to_le_bytes)
    .collect::<Vec<_>>();
  u32s == lean_sarray_data(bytes)
}
