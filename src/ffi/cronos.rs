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

/// Enable RAM tracking: each `clock(tag)` samples `/proc/self/status` so
/// streaming output and the timeline include net RSS deltas plus the running
/// peak. Off by default — costs one `read()` per clock call. Linux only.
#[unsafe(no_mangle)]
extern "C" fn rs_cronos_ram_enable() -> LeanIOResult<LeanOwned> {
  cronos::set_ram(true);
  LeanIOResult::ok(LeanOwned::box_usize(0))
}

/// Disable RAM tracking.
#[unsafe(no_mangle)]
extern "C" fn rs_cronos_ram_disable() -> LeanIOResult<LeanOwned> {
  cronos::set_ram(false);
  LeanIOResult::ok(LeanOwned::box_usize(0))
}