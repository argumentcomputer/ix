//! Type checker error types.

use crate::ix::address::Address;

use super::expr::KExpr;
use super::mode::KernelMode;

/// Convert `u64` to `usize`, returning `TcError` if the value exceeds
/// the platform's pointer width (relevant for 32-bit targets).
#[inline(always)]
pub fn u64_to_usize<M: KernelMode>(val: u64) -> Result<usize, TcError<M>> {
  usize::try_from(val)
    .map_err(|_e| TcError::Other(format!("{val} exceeds usize::MAX")))
}

#[derive(Debug)]
pub enum TcError<M: KernelMode> {
  TypeExpected,
  FunExpected { e: KExpr<M>, whnf: KExpr<M> },
  AppTypeMismatch { a_ty: KExpr<M>, dom: KExpr<M>, depth: usize },
  DeclTypeMismatch,
  UnknownConst(Address),
  UnivParamMismatch { expected: u64, got: usize },
  VarOutOfRange { idx: u64, ctx_len: usize },
  DefEqFailed,
  MaxRecDepth,
  Other(String),
}
