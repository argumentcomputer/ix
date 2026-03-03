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

use lean_sys::object::{LeanArray, LeanByteArray, LeanIOResult};

/// Guard an FFI function that returns a Lean IO result against panics.
/// On panic, returns a Lean IO error with the panic message instead of
/// unwinding across the `extern "C"` boundary (which is undefined behavior).
pub(crate) fn ffi_io_guard<F>(f: F) -> LeanIOResult
where
  F: FnOnce() -> LeanIOResult + std::panic::UnwindSafe,
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
      LeanIOResult::error_string(&msg)
    },
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_boxed_u32s_are_equivalent_to_bytes(
  u32s: LeanArray,
  bytes: LeanByteArray,
) -> bool {
  let u32s_flat: Vec<u8> = u32s
    .map(|elem| elem.unbox_u32())
    .into_iter()
    .flat_map(u32::to_le_bytes)
    .collect();
  u32s_flat == bytes.as_bytes()
}
