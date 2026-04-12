//! Type checker error types.

use crate::ix::address::Address;

use super::expr::KExpr;
use super::mode::KernelMode;

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
