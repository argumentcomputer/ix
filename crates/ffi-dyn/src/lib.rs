//! Loadable form of Ix's own raw `@[extern]` symbols for Lean's native
//! evaluator during `native_decide` elaboration, before any executable links
//! `ix-ffi` statically.
//!
//! The source is shared verbatim with `ix-ffi` (compiled into both), so there
//! is a single implementation. Only the raw entry points need a loadable
//! definition here; the boxed wrappers Lean actually calls come from its own
//! generated objects for the declaring modules.

#[path = "../../ffi/src/unsigned.rs"]
mod unsigned;
