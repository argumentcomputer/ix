//! Utilities for converting Lean `Nat` fields to Rust integer types.
//!
//! Lean's `Nat` is arbitrary-precision, but structural metadata fields
//! (`num_params`, `num_indices`, `num_motives`, `num_minors`, `num_fields`,
//! `num_nested`) are always small values. These utilities make the conversion
//! explicit rather than silently producing 0 on overflow.

use lean_ffi::nat::Nat;

use crate::ix::ixon::CompileError;

/// Convert a Lean `Nat` to `usize`, returning `CompileError` on overflow.
///
/// Use in functions that return `Result<_, CompileError>`.
pub(crate) fn try_nat_to_usize(n: &Nat) -> Result<usize, CompileError> {
  n.to_u64().map(|v| v as usize).ok_or_else(|| CompileError::UnsupportedExpr {
    desc: "Nat field exceeds u64".into(),
  })
}

/// Convert a Lean `Nat` to `usize`, panicking on overflow.
///
/// Use in pure functions where returning `Result` would cascade through
/// callers. Overflow is impossible for valid Lean metadata — these fields
/// represent type constructor arities which are always < 2^64.
pub(crate) fn nat_to_usize(n: &Nat) -> usize {
  n.to_u64().expect("Nat field exceeds u64") as usize
}

/// Convert a Lean `Nat` to `u64`, panicking on overflow.
pub(crate) fn nat_to_u64(n: &Nat) -> u64 {
  n.to_u64().expect("Nat field exceeds u64")
}
