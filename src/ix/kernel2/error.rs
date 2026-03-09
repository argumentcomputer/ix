//! Type-checking errors for Kernel2.

use std::fmt;

use super::types::{KExpr, MetaMode};

/// Errors produced by the Kernel2 type checker.
#[derive(Debug, Clone)]
pub enum TcError<M: MetaMode> {
  /// Expected a sort (Type/Prop) but got something else.
  TypeExpected { expr: KExpr<M>, inferred: KExpr<M> },
  /// Expected a function (Pi type) but got something else.
  FunctionExpected { expr: KExpr<M>, inferred: KExpr<M> },
  /// Type mismatch between expected and inferred types.
  TypeMismatch {
    expected: KExpr<M>,
    found: KExpr<M>,
    expr: KExpr<M>,
  },
  /// Definitional equality check failed.
  DefEqFailure { lhs: KExpr<M>, rhs: KExpr<M> },
  /// Reference to an unknown constant.
  UnknownConst { msg: String },
  /// Bound variable index out of range.
  FreeBoundVariable { idx: usize },
  /// Generic kernel error with message.
  KernelException { msg: String },
  /// Fuel exhausted (too many reduction steps).
  FuelExhausted,
  /// Recursion depth exceeded.
  RecursionDepthExceeded,
}

impl<M: MetaMode> fmt::Display for TcError<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TcError::TypeExpected { .. } => write!(f, "type expected"),
      TcError::FunctionExpected { .. } => write!(f, "function expected"),
      TcError::TypeMismatch { .. } => write!(f, "type mismatch"),
      TcError::DefEqFailure { .. } => write!(f, "definitional equality failure"),
      TcError::UnknownConst { msg } => write!(f, "unknown constant: {msg}"),
      TcError::FreeBoundVariable { idx } => {
        write!(f, "free bound variable at index {idx}")
      }
      TcError::KernelException { msg } => write!(f, "kernel exception: {msg}"),
      TcError::FuelExhausted => write!(f, "fuel exhausted"),
      TcError::RecursionDepthExceeded => {
        write!(f, "recursion depth exceeded")
      }
    }
  }
}

impl<M: MetaMode> std::error::Error for TcError<M> {}
