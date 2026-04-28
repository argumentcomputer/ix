// Lean and C don't support feature flags, so the _iroh module is exposed as a fallback for when the `net` feature is disabled and/or on the `aarch64-darwin` target.
// This fallback module contains dummy functions that can still be called via Lean->Rust FFI, but will return an error message that Lean then prints before exiting.
#[cfg(any(
  not(feature = "net"),
  all(target_os = "macos", target_arch = "aarch64")
))]
pub mod _iroh;
pub mod aiur;
pub mod byte_array;
#[cfg(all(
  feature = "net",
  not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod iroh;
pub mod keccak;
pub mod lean_env;
pub mod unsigned;

// Modular FFI structure
pub mod builder; // IxEnvBuilder struct
pub mod compile; // Compilation: rs_compile_env_full, rs_compile_phases, etc.
pub mod graph; // Graph/SCC: rs_build_ref_graph, rs_compute_sccs
pub mod ix; // Ix types: Name, Level, Expr, ConstantInfo, Environment
pub mod ixon; // Ixon types: Univ, Expr, Constant, metadata
pub mod kernel; // Kernel type-checker FFI: rs_kernel_check_consts, rs_kernel_ingress (production); rs_kernel_roundtrip* (test-only)
pub mod primitives; // Primitives: rs_roundtrip_nat, rs_roundtrip_string, etc.
#[cfg(feature = "test-ffi")]
pub mod refcount; // Reference counting / ownership tests (test-only)

#[cfg(feature = "test-ffi")]
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanOwned, LeanRef,
};

#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_boxed_u32s_are_equivalent_to_bytes(
  u32s: LeanArray<LeanOwned>,
  bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> bool {
  let u32s_flat: Vec<u8> = u32s
    .map(|elem| elem.unbox_u32())
    .into_iter()
    .flat_map(u32::to_le_bytes)
    .collect();
  u32s_flat == bytes.as_bytes()
}
