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

mod aiur_chain;
mod aiur_compression;
mod aiur_stages;
pub mod catalog;
mod compression;
pub mod formal;
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
  fn mi_option_set(option: core::ffi::c_int, value: core::ffi::c_long);
}

/// `mi_option_purge_delay` in mimalloc v3's `mi_option_t`. `libmimalloc-sys`
/// does not export this constant.
const MI_OPTION_PURGE_DELAY: core::ffi::c_int = 15;

/// Make mimalloc return freed pages to the OS immediately. The default delay
/// keeps a freed execution record resident for seconds after the record pool
/// has released its budget, so RSS overruns the host budget by up to one
/// record. An explicit `MIMALLOC_PURGE_DELAY` in the environment wins.
#[unsafe(no_mangle)]
pub extern "C" fn rs_configure_allocator() -> LeanIOResult<LeanOwned> {
  if std::env::var_os("MIMALLOC_PURGE_DELAY").is_none() {
    // SAFETY: mimalloc options are plain atomics that may be set at any time;
    // the purge delay is read on every purge decision.
    unsafe { mi_option_set(MI_OPTION_PURGE_DELAY, 0) };
  }
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// Set the stack size (in bytes) for subsequently spawned Lean runtime threads,
/// adapting the bare `void lean_internal_set_thread_stack_size(size_t)` runtime
/// call to the `BaseIO Unit` ABI (which returns `Unit` = `lean_box(0)`).
#[unsafe(no_mangle)]
pub extern "C" fn rs_lean_set_thread_stack_size(size: usize) -> LeanOwned {
  // SAFETY: a plain call into the Lean runtime with no Lean objects, which
  // lean-ffi does not wrap; it only records the size used for threads the
  // runtime spawns later.
  unsafe {
    lean_internal_set_thread_stack_size(size);
  }
  LeanOwned::box_usize(0)
}

#[cfg(test)]
mod tests {
  /// `aiur::ixon` carries the Aiur crate's copy of Ixon's TagN integer code
  /// (Aiur may not depend on `ixon`). Both directions must agree with
  /// `ixon::tag::TagN` at a zero-bit flag on every rung boundary.
  #[test]
  fn aiur_artifact_integers_are_ixon_tagn() {
    use ixon::tag::TagN;
    let mut values = vec![0, 1, u64::MAX - 1, u64::MAX];
    for end in [
      TagN::end1(0),
      TagN::end2(0),
      TagN::end3(0),
      TagN::end4(0),
      TagN::end5(0),
    ] {
      values.extend([end - 1, end, end + 1]);
    }
    for value in values {
      let mut expected = vec![];
      TagN::put(0, 0, value, &mut expected);
      let mut writer = aiur::ixon::Writer::new();
      writer.nat(value);
      assert_eq!(writer.into_bytes(), expected, "{value}");
      let mut reader = aiur::ixon::Reader::new(&expected);
      assert_eq!(reader.nat().unwrap(), value);
      reader.finish().unwrap();
    }
  }
}
