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
  /// An interior universe substitution hit `Param(idx)` where `idx` was
  /// out of range for the supplied universe list. Distinct from
  /// `UnivParamMismatch` which is the arity gate at Const-infer time;
  /// this variant fires from `subst_univ` as defense-in-depth against
  /// any code path that reaches substitution without the arity check.
  UnivParamOutOfRange { idx: u64, bound: usize },
  VarOutOfRange { idx: u64, ctx_len: usize },
  DefEqFailed,
  MaxRecDepth,
  Other(String),
}

impl<M: KernelMode> std::fmt::Display for TcError<M> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TcError::TypeExpected => write!(f, "type expected"),
      TcError::FunExpected { e, whnf } => {
        write!(f, "function expected, got {e} (whnf: {whnf})")
      },
      TcError::AppTypeMismatch { a_ty, dom, depth } => {
        write!(
          f,
          "app type mismatch at depth {depth}: arg has type {a_ty}, domain is {dom}"
        )
      },
      TcError::DeclTypeMismatch => write!(f, "declaration type mismatch"),
      TcError::UnknownConst(addr) => {
        write!(f, "unknown constant {:.12}", addr.hex())
      },
      TcError::UnivParamMismatch { expected, got } => {
        write!(f, "universe param count: expected {expected}, got {got}")
      },
      TcError::UnivParamOutOfRange { idx, bound } => {
        write!(
          f,
          "universe Param({idx}) out of range: only {bound} universes supplied"
        )
      },
      TcError::VarOutOfRange { idx, ctx_len } => {
        write!(f, "variable #{idx} out of range (context depth {ctx_len})")
      },
      TcError::DefEqFailed => write!(f, "definitional equality check failed"),
      TcError::MaxRecDepth => write!(f, "max recursion depth exceeded"),
      TcError::Other(s) => write!(f, "{s}"),
    }
  }
}
