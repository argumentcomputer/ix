//! Lean FFI wrapper for the `cronos` Rust profiler so the Aiur benchmark
//! (or any other Lean caller) can dump the timeline collected by
//! `cronos::clock(...)` calls inside multi-stark / Aiur Rust code.

use lean_ffi::object::{LeanIOResult, LeanOwned};

/// `Aiur.cronosPrint : BaseIO Unit` — dumps the global cronos timeline.
#[unsafe(no_mangle)]
extern "C" fn rs_cronos_print() -> LeanIOResult<LeanOwned> {
  cronos::print();
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// Enable streaming: each completed `clock(tag)` prints a one-liner.
#[unsafe(no_mangle)]
extern "C" fn rs_cronos_streaming_enable() -> LeanIOResult<LeanOwned> {
  cronos::set_streaming(true);
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// Disable streaming.
#[unsafe(no_mangle)]
extern "C" fn rs_cronos_streaming_disable() -> LeanIOResult<LeanOwned> {
  cronos::set_streaming(false);
  LeanIOResult::ok(LeanOwned::box_usize(0))
}