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

use crate::lean::lean::{
  lean_io_result_mk_error, lean_io_result_mk_ok, lean_mk_io_user_error,
};
use crate::lean::obj::{LeanObj, LeanString};

/// Guard an FFI function that returns a Lean IO result against panics.
/// On panic, returns a Lean IO error with the panic message instead of
/// unwinding across the `extern "C"` boundary (which is undefined behavior).
pub(crate) fn ffi_io_guard<F>(f: F) -> LeanObj
where
  F: FnOnce() -> LeanObj + std::panic::UnwindSafe,
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
      io_error(&msg)
    },
  }
}

/// Wrap a Lean value in an IO success result.
pub(crate) fn io_ok(val: impl Into<LeanObj>) -> LeanObj {
  let val: LeanObj = val.into();
  unsafe {
    LeanObj::from_raw(lean_io_result_mk_ok(val.as_mut_ptr().cast()).cast())
  }
}

/// Create a Lean IO error result from a Rust error message.
pub(crate) fn io_error(msg: &str) -> LeanObj {
  let lean_msg = LeanString::from_str(msg);
  unsafe {
    let lean_err = lean_mk_io_user_error(lean_msg.as_mut_ptr().cast());
    LeanObj::from_raw(lean_io_result_mk_error(lean_err).cast())
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_boxed_u32s_are_equivalent_to_bytes(
  u32s: LeanObj,
  bytes: LeanObj,
) -> bool {
  let arr = u32s.as_array();
  let u32s_flat: Vec<u8> = arr
    .map(|elem| elem.unbox_u32())
    .into_iter()
    .flat_map(u32::to_le_bytes)
    .collect();
  let ba = bytes.as_byte_array();
  u32s_flat == ba.as_bytes()
}
