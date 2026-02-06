use crate::ix::env::{Expr, Name};

#[derive(Debug)]
pub enum TcError {
  TypeExpected {
    expr: Expr,
    inferred: Expr,
  },
  FunctionExpected {
    expr: Expr,
    inferred: Expr,
  },
  TypeMismatch {
    expected: Expr,
    found: Expr,
    expr: Expr,
  },
  DefEqFailure {
    lhs: Expr,
    rhs: Expr,
  },
  UnknownConst {
    name: Name,
  },
  DuplicateUniverse {
    name: Name,
  },
  FreeBoundVariable {
    idx: u64,
  },
  KernelException {
    msg: String,
  },
}

impl std::fmt::Display for TcError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      TcError::TypeExpected { .. } => write!(f, "type expected"),
      TcError::FunctionExpected { .. } => write!(f, "function expected"),
      TcError::TypeMismatch { .. } => write!(f, "type mismatch"),
      TcError::DefEqFailure { .. } => {
        write!(f, "definitional equality failure")
      },
      TcError::UnknownConst { name } => {
        write!(f, "unknown constant: {}", name.pretty())
      },
      TcError::DuplicateUniverse { name } => {
        write!(f, "duplicate universe: {}", name.pretty())
      },
      TcError::FreeBoundVariable { idx } => {
        write!(f, "free bound variable at index {}", idx)
      },
      TcError::KernelException { msg } => write!(f, "{}", msg),
    }
  }
}

impl std::error::Error for TcError {}
