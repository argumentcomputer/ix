// `_iroh` provides dummy fallbacks when the `net` feature is disabled or on
// `aarch64-darwin` (where iroh doesn't work). Lean and C don't support feature
// flags, so we always expose iroh symbols — they just panic with an error
// message when called without `net`.
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
pub mod texray;
#[cfg(all(
  feature = "net",
  not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod lean_iroh;
pub mod unsigned;

pub mod builder;
pub mod compile;
pub mod graph;
pub mod ix;
pub mod kernel;
pub mod lean_ixon;
pub mod primitives;
#[cfg(feature = "test-ffi")]
pub mod refcount;

pub mod lean;
mod sha256;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

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
