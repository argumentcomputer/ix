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
  FunExpected {
    e: KExpr<M>,
    whnf: KExpr<M>,
  },
  AppTypeMismatch {
    a_ty: KExpr<M>,
    dom: KExpr<M>,
    depth: usize,
  },
  DeclTypeMismatch,
  UnknownConst(Address),
  UnivParamMismatch {
    expected: u64,
    got: usize,
  },
  /// An interior universe substitution hit `Param(idx)` where `idx` was
  /// out of range for the supplied universe list. Distinct from
  /// `UnivParamMismatch` which is the arity gate at Const-infer time;
  /// this variant fires from `subst_univ` as defense-in-depth against
  /// any code path that reaches substitution without the arity check.
  UnivParamOutOfRange {
    idx: u64,
    bound: usize,
  },
  VarOutOfRange {
    idx: u64,
    ctx_len: usize,
  },
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

#[cfg(test)]
mod tests {
  use super::super::expr::KExpr;
  use super::super::level::KUniv;
  use super::super::mode::Anon;
  use super::*;

  fn sort0() -> KExpr<Anon> {
    KExpr::sort(KUniv::zero())
  }

  #[test]
  fn u64_to_usize_small_value() {
    let r: Result<usize, TcError<Anon>> = u64_to_usize::<Anon>(42u64);
    assert_eq!(r.unwrap(), 42);
  }

  #[test]
  fn u64_to_usize_zero() {
    let r: Result<usize, TcError<Anon>> = u64_to_usize::<Anon>(0u64);
    assert_eq!(r.unwrap(), 0);
  }

  #[test]
  fn display_type_expected() {
    let e: TcError<Anon> = TcError::TypeExpected;
    assert_eq!(format!("{e}"), "type expected");
  }

  #[test]
  fn display_fun_expected() {
    let e: TcError<Anon> = TcError::FunExpected { e: sort0(), whnf: sort0() };
    let s = format!("{e}");
    // Must contain the "function expected" header; the expression format
    // isn't frozen so we only sniff for the leading text.
    assert!(s.starts_with("function expected"));
  }

  #[test]
  fn display_app_type_mismatch() {
    let e: TcError<Anon> =
      TcError::AppTypeMismatch { a_ty: sort0(), dom: sort0(), depth: 7 };
    let s = format!("{e}");
    assert!(s.contains("app type mismatch"));
    assert!(s.contains("depth 7"));
  }

  #[test]
  fn display_decl_type_mismatch() {
    let e: TcError<Anon> = TcError::DeclTypeMismatch;
    assert_eq!(format!("{e}"), "declaration type mismatch");
  }

  #[test]
  fn display_unknown_const() {
    let addr = Address::hash(b"some-constant");
    let e: TcError<Anon> = TcError::UnknownConst(addr.clone());
    let s = format!("{e}");
    assert!(s.starts_with("unknown constant"));
    // The display uses `{:.12}` — precision truncates the hex. Verify the
    // first 12 chars of the hex appear.
    let hex = addr.hex();
    assert!(s.contains(&hex[..12]));
  }

  #[test]
  fn display_univ_param_mismatch() {
    let e: TcError<Anon> = TcError::UnivParamMismatch { expected: 2, got: 3 };
    let s = format!("{e}");
    assert!(s.contains("universe param count"));
    assert!(s.contains("expected 2"));
    assert!(s.contains("got 3"));
  }

  #[test]
  fn display_univ_param_out_of_range() {
    let e: TcError<Anon> = TcError::UnivParamOutOfRange { idx: 5, bound: 2 };
    let s = format!("{e}");
    assert!(s.contains("Param(5)"));
    assert!(s.contains("only 2 universes supplied"));
  }

  #[test]
  fn display_var_out_of_range() {
    let e: TcError<Anon> = TcError::VarOutOfRange { idx: 7, ctx_len: 3 };
    let s = format!("{e}");
    assert!(s.contains("#7"));
    assert!(s.contains("depth 3"));
  }

  #[test]
  fn display_def_eq_failed() {
    let e: TcError<Anon> = TcError::DefEqFailed;
    assert_eq!(format!("{e}"), "definitional equality check failed");
  }

  #[test]
  fn display_max_rec_depth() {
    let e: TcError<Anon> = TcError::MaxRecDepth;
    assert_eq!(format!("{e}"), "max recursion depth exceeded");
  }

  #[test]
  fn display_other_passthrough() {
    let e: TcError<Anon> = TcError::Other("custom diagnostic".into());
    assert_eq!(format!("{e}"), "custom diagnostic");
  }

  #[test]
  fn debug_is_implemented() {
    // Regression guard: TcError must remain Debug for `?` propagation
    // through test assertions.
    let e: TcError<Anon> = TcError::TypeExpected;
    let _ = format!("{e:?}");
  }
}
