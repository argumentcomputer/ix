// `_iroh` provides dummy fallbacks when the `net` feature is disabled or on
// `aarch64-darwin` (where iroh doesn't work). Lean and C don't support feature
// flags, so we always expose iroh symbols — they just panic with an error
// message when called without `net`.
#[cfg(any(
  not(feature = "net"),
  all(target_os = "macos", target_arch = "aarch64")
))]
pub mod _iroh;
#[cfg(all(
  feature = "net",
  not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod iroh;
pub mod keccak;
#[cfg(all(
  feature = "net",
  not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod lean_iroh;
pub mod texray;
pub mod unsigned;

pub mod catalog;
pub mod lean_ixon;
pub mod primitives;
#[cfg(feature = "test-ffi")]
pub mod refcount;

pub mod lean;
mod sha256;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use lean_ffi::object::{LeanIOResult, LeanOwned};

unsafe extern "C" {
  fn lean_internal_set_thread_stack_size(size: usize);
}

/// Set the stack size (in bytes) for subsequently spawned Lean runtime threads,
/// adapting the bare `void lean_internal_set_thread_stack_size(size_t)` runtime
/// call to the `BaseIO Unit` ABI.
#[unsafe(no_mangle)]
pub extern "C" fn rs_lean_set_thread_stack_size(
  size: usize,
) -> LeanIOResult<LeanOwned> {
  unsafe {
    lean_internal_set_thread_stack_size(size);
  }
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

#[cfg(feature = "test-ffi")]
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanByteArray, LeanRef};

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
