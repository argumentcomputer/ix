//! Lean FFI wrapper for the `cronos` Rust profiler so the Aiur benchmark
//! (or any other Lean caller) can dump the timeline collected by
//! `cronos::clock(...)` calls inside multi-stark / Aiur Rust code.

use lean_ffi::object::{LeanIOResult, LeanOwned};

/// `Aiur.cronosPrint : BaseIO Unit` — dumps the global cronos timeline.
#[unsafe(no_mangle)]
extern "C" fn rs_cronos_print(
  _world: LeanOwned,
) -> LeanIOResult<LeanOwned> {
  cronos::print();
  LeanIOResult::ok(LeanOwned::box_usize(0))
}