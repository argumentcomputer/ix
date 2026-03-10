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
  /// Heartbeat limit exceeded (too much work).
  HeartbeatLimitExceeded,
}

impl<M: MetaMode> fmt::Display for TcError<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TcError::TypeExpected { expr, inferred } => write!(f, "type expected: {expr} has type {inferred}"),
      TcError::FunctionExpected { expr, inferred } => write!(f, "function expected: {expr} has type {inferred}"),
      TcError::TypeMismatch { expected, found, expr } => write!(f, "type mismatch: expected {expected}, found {found}, in expr {expr}"),
      TcError::DefEqFailure { lhs, rhs } => write!(f, "def-eq failure: {lhs} ≠ {rhs}"),
      TcError::UnknownConst { msg } => write!(f, "unknown constant: {msg}"),
      TcError::FreeBoundVariable { idx } => {
        write!(f, "free bound variable at index {idx}")
      }
      TcError::KernelException { msg } => write!(f, "kernel exception: {msg}"),
      TcError::HeartbeatLimitExceeded => {
        write!(f, "heartbeat limit exceeded")
      }
    }
  }
}

impl<M: MetaMode> std::error::Error for TcError<M> {}
