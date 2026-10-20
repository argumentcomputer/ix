//! A standalone expression, not a declaration. Eval inherits its type from
//! the checked input. Encoded by `serialize.rs`; transported in `Env::blobs`.

use std::sync::Arc;

use ix_common::address::Address;

use crate::{Expr, Univ};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprObj {
  pub lvls: u64,
  pub root: Arc<Expr>,
  pub sharing: Vec<Arc<Expr>>,
  pub refs: Vec<Address>,
  pub univs: Vec<Arc<Univ>>,
}

fn index(i: u64, n: usize) -> Result<usize, String> {
  usize::try_from(i)
    .ok()
    .filter(|&i| i < n)
    .ok_or_else(|| "ExprObj: table index out of bounds".into())
}

fn check_univ(u: &Univ, bound: u64) -> Result<(), String> {
  let mut stack = vec![u];
  while let Some(u) = stack.pop() {
    match u {
      Univ::Zero => {},
      Univ::Succ(u) => stack.push(u),
      Univ::Max(a, b) | Univ::IMax(a, b) => stack.extend([&**a, &**b]),
      Univ::Var(i) if *i < bound => {},
      Univ::Var(_) => {
        return Err("ExprObj: universe parameter out of bounds".into());
      },
    }
  }
  Ok(())
}

// u128 represents even Var(u64::MAX)'s loose-variable requirement exactly.
fn loose(
  e: &Expr,
  shares: &[u128],
  refs: usize,
  univs: usize,
) -> Result<u128, String> {
  let mut stack = vec![(e, 0u128)];
  let mut required = 0;
  while let Some((e, depth)) = stack.pop() {
    match e {
      Expr::Sort(i) => {
        index(*i, univs)?;
      },
      Expr::Var(i) => {
        required = required.max((u128::from(*i) + 1).saturating_sub(depth));
      },
      Expr::Ref(i, us) => {
        index(*i, refs)?;
        for u in us {
          index(*u, univs)?;
        }
      },
      Expr::Rec(..) => {
        return Err("ExprObj: block-local Rec is forbidden".into());
      },
      Expr::Prj(i, _, e) => {
        index(*i, refs)?;
        stack.push((e, depth));
      },
      Expr::Str(i) | Expr::Nat(i) => {
        index(*i, refs)?;
      },
      Expr::App(f, a) => stack.extend([(&**f, depth), (&**a, depth)]),
      Expr::Lam(_, t, b) | Expr::All(_, _, t, b) => {
        stack.extend([(&**t, depth), (&**b, depth + 1)])
      },
      Expr::Let(_, t, v, b) => {
        stack.extend([(&**t, depth), (&**v, depth), (&**b, depth + 1)])
      },
      Expr::Share(i) => {
        required =
          required.max(shares[index(*i, shares.len())?].saturating_sub(depth));
      },
    }
  }
  Ok(required)
}

impl ExprObj {
  /// Structural validation, not typechecking. Shared open subterms are allowed
  /// inside binders; the root is closed. Every sharing edge points backward.
  pub fn validate(&self) -> Result<(), String> {
    for u in &self.univs {
      check_univ(u, self.lvls)?;
    }
    let mut shares = Vec::with_capacity(self.sharing.len());
    for e in &self.sharing {
      shares.push(loose(e, &shares, self.refs.len(), self.univs.len())?);
    }
    if loose(&self.root, &shares, self.refs.len(), self.univs.len())? != 0 {
      return Err("ExprObj: free term variable".into());
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn identity() -> ExprObj {
    ExprObj {
      lvls: 0,
      root: Expr::lam(Expr::sort(0), Expr::var(0)),
      sharing: vec![],
      refs: vec![],
      univs: vec![Univ::zero()],
    }
  }

  #[test]
  fn codec_and_strict_envelope() {
    let o = identity();
    let (addr, bytes) = o.commit();
    // Shared Lean/Aiur fixture: E0 05, lvls, lambda, tables.
    assert_eq!(bytes, [0xe0, 5, 0, 0x81, 7, 0, 0x10, 0, 0, 1, 0]);
    assert_eq!(addr, Address::hash(&bytes));
    assert_eq!(ExprObj::from_bytes(&bytes).unwrap(), o);
    for n in 0..bytes.len() {
      assert!(ExprObj::from_bytes(&bytes[..n]).is_err());
    }
    let mut extra = bytes.clone();
    extra.push(0);
    assert!(ExprObj::from_bytes(&extra).is_err());
    for (i, byte) in [(0, 0xd0), (1, 4), (1, 6)] {
      let mut bad = bytes.clone();
      bad[i] = byte;
      assert!(ExprObj::from_bytes(&bad).is_err());
    }
  }

  #[test]
  fn scope_and_tables() {
    let mut o = identity();
    o.sharing = vec![Expr::var(0)];
    o.root = Expr::lam(Expr::sort(0), Expr::share(0));
    assert!(o.validate().is_ok());
    for root in [
      Expr::share(0),
      Expr::var(u64::MAX),
      Expr::sort(1),
      Expr::reference(0, vec![]),
      Expr::rec(0, vec![]),
    ] {
      o.root = root;
      assert!(o.validate().is_err());
    }
    o = identity();
    o.sharing = vec![Expr::share(0)];
    assert!(o.validate().is_err());
    o.sharing.clear();
    o.univs = vec![Univ::var(0)];
    assert!(o.validate().is_err());
    o.lvls = 1;
    assert!(o.validate().is_ok());
  }
}
