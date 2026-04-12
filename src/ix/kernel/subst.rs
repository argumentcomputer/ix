//! Substitution and lifting for zero kernel expressions.
//!
//! All functions intern results through `InternTable` for pointer deduplication.

use super::env::InternTable;
use super::expr::{ExprData, KExpr};
use super::mode::KernelMode;

/// Perform single substitution: `body[arg/Var(depth)]`.
///
/// Replaces `Var(depth)` with `arg` (lifted by `depth`), shifts free
/// variables above `depth` down by 1. Uses `lbr()` for fast-path skipping.
pub fn subst<M: KernelMode>(
  env: &InternTable<M>,
  body: &KExpr<M>,
  arg: &KExpr<M>,
  depth: u64,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }

  let result = match body.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i == depth {
        lift(env, arg, depth, 0)
      } else if i > depth {
        KExpr::var(i - 1, name.clone())
      } else {
        return body.clone();
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = subst(env, f, arg, depth);
      let x2 = subst(env, x, arg, depth);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = subst(env, ty, arg, depth);
      let inner2 = subst(env, inner, arg, depth + 1);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = subst(env, ty, arg, depth);
      let inner2 = subst(env, inner, arg, depth + 1);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = subst(env, ty, arg, depth);
      let val2 = subst(env, val, arg, depth);
      let inner2 = subst(env, inner, arg, depth + 1);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = subst(env, val, arg, depth);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => return body.clone(),
  };

  env.intern_expr(result)
}

/// Perform simultaneous substitution: replace `Var(depth)..Var(depth+n-1)`
/// with `substs[0]..substs[n-1]`, shifting free variables above by `-n`.
pub fn simul_subst<M: KernelMode>(
  env: &InternTable<M>,
  body: &KExpr<M>,
  substs: &[KExpr<M>],
  depth: u64,
) -> KExpr<M> {
  if body.lbr() <= depth {
    return body.clone();
  }

  let n = substs.len() as u64;

  let result = match body.data() {
    ExprData::Var(i, _, _) => {
      let i = *i;
      if i >= depth && i < depth + n {
        #[allow(clippy::cast_possible_truncation)] // guarded: i < depth + substs.len()
        return lift(env, &substs[(i - depth) as usize], depth, 0);
      } else if i >= depth + n {
        KExpr::var(i - n, M::meta_field(crate::ix::env::Name::anon()))
      } else {
        return body.clone();
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = simul_subst(env, f, substs, depth);
      let x2 = simul_subst(env, x, substs, depth);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, inner, _) => {
      let ty2 = simul_subst(env, ty, substs, depth);
      let inner2 = simul_subst(env, inner, substs, depth + 1);
      KExpr::lam(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::All(name, bi, ty, inner, _) => {
      let ty2 = simul_subst(env, ty, substs, depth);
      let inner2 = simul_subst(env, inner, substs, depth + 1);
      KExpr::all(name.clone(), bi.clone(), ty2, inner2)
    },

    ExprData::Let(name, ty, val, inner, nd, _) => {
      let ty2 = simul_subst(env, ty, substs, depth);
      let val2 = simul_subst(env, val, substs, depth);
      let inner2 = simul_subst(env, inner, substs, depth + 1);
      KExpr::let_(name.clone(), ty2, val2, inner2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = simul_subst(env, val, substs, depth);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => return body.clone(),
  };

  env.intern_expr(result)
}

/// Shift free de Bruijn indices ≥ `cutoff` up by `shift`.
/// Used when substituting an argument into a deeper context.
pub fn lift<M: KernelMode>(
  env: &InternTable<M>,
  e: &KExpr<M>,
  shift: u64,
  cutoff: u64,
) -> KExpr<M> {
  if shift == 0 || e.lbr() <= cutoff {
    return e.clone();
  }

  let result = match e.data() {
    ExprData::Var(i, name, _) => {
      let i = *i;
      if i >= cutoff {
        KExpr::var(i + shift, name.clone())
      } else {
        return e.clone();
      }
    },

    ExprData::App(f, x, _) => {
      let f2 = lift(env, f, shift, cutoff);
      let x2 = lift(env, x, shift, cutoff);
      KExpr::app(f2, x2)
    },

    ExprData::Lam(name, bi, ty, body, _) => {
      let ty2 = lift(env, ty, shift, cutoff);
      let body2 = lift(env, body, shift, cutoff + 1);
      KExpr::lam(name.clone(), bi.clone(), ty2, body2)
    },

    ExprData::All(name, bi, ty, body, _) => {
      let ty2 = lift(env, ty, shift, cutoff);
      let body2 = lift(env, body, shift, cutoff + 1);
      KExpr::all(name.clone(), bi.clone(), ty2, body2)
    },

    ExprData::Let(name, ty, val, body, nd, _) => {
      let ty2 = lift(env, ty, shift, cutoff);
      let val2 = lift(env, val, shift, cutoff);
      let body2 = lift(env, body, shift, cutoff + 1);
      KExpr::let_(name.clone(), ty2, val2, body2, *nd)
    },

    ExprData::Prj(id, field, val, _) => {
      let val2 = lift(env, val, shift, cutoff);
      KExpr::prj(id.clone(), *field, val2)
    },

    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Nat(..)
    | ExprData::Str(..) => return e.clone(),
  };

  env.intern_expr(result)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::kernel::id::KId;
  
  use crate::ix::kernel::mode::Anon;
  use lean_ffi::nat::Nat;

  type AE = KExpr<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  #[test]
  fn subst_var_0() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &v0, &arg, 0);
    assert_eq!(result, arg);
  }

  #[test]
  fn subst_closed_skip() {
    let env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &nat, &arg, 0);
    assert!(result.ptr_eq(&nat));
  }

  #[test]
  fn subst_free_var_shift() {
    let env = InternTable::<Anon>::new();
    let v1 = AE::var(1, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &v1, &arg, 0);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn subst_app() {
    let env = InternTable::<Anon>::new();
    let c = AE::cnst(KId::new(mk_addr("f"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    let app = AE::app(c.clone(), v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &app, &arg, 0);
    let expected = AE::app(c, arg);
    assert_eq!(result, expected);
  }

  #[test]
  fn subst_under_lambda() {
    let env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v1 = AE::var(1, ());
    // λ(_:Nat). Var(1) — body references outer variable
    let lam = AE::lam((), (), nat.clone(), v1);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &lam, &arg, 0);
    // Result: λ(_:Nat). 3
    let expected = AE::lam((), (), nat, arg);
    assert_eq!(result, expected);
  }

  #[test]
  fn subst_bound_var_unchanged() {
    let env = InternTable::<Anon>::new();
    let nat = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let v0 = AE::var(0, ());
    // λ(_:Nat). Var(0) — body is lambda-bound, closed under binder
    let lam = AE::lam((), (), nat, v0);
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));
    let result = subst(&env, &lam, &arg, 0);
    assert!(result.ptr_eq(&lam));
  }

  #[test]
  fn lift_var() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    // lift(Var(0), shift=1, cutoff=0) → Var(1)
    let result = lift(&env, &v0, 1, 0);
    assert_eq!(result, AE::var(1, ()));
    // lift(Var(0), shift=1, cutoff=1) → Var(0) (below cutoff)
    let result2 = lift(&env, &v0, 1, 1);
    assert!(result2.ptr_eq(&v0));
  }

  #[test]
  fn lift_zero_shift() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let result = lift(&env, &v0, 0, 0);
    assert!(result.ptr_eq(&v0));
  }

  #[test]
  fn simul_subst_basic() {
    let env = InternTable::<Anon>::new();
    let v0 = AE::var(0, ());
    let v1 = AE::var(1, ());
    let app = AE::app(v1, v0); // App(Var(1), Var(0))

    let a = AE::nat(Nat::from(1u64), mk_addr("a"));
    let b = AE::nat(Nat::from(2u64), mk_addr("b"));

    // simul_subst([a, b], depth=0):
    //   Var(0) → substs[0] = a
    //   Var(1) → substs[1] = b
    let result = simul_subst(&env, &app, &[a.clone(), b.clone()], 0);
    let expected = AE::app(b, a);
    assert_eq!(result, expected);
  }

  #[test]
  fn simul_subst_shift() {
    let env = InternTable::<Anon>::new();
    let v2 = AE::var(2, ());

    let a = AE::nat(Nat::from(1u64), mk_addr("a"));
    let b = AE::nat(Nat::from(2u64), mk_addr("b"));

    // Var(2) >= depth+2 → shifted to Var(0)
    let result = simul_subst(&env, &v2, &[a, b], 0);
    assert_eq!(result, AE::var(0, ()));
  }

  #[test]
  fn intern_dedup() {
    let env = InternTable::<Anon>::new();
    let _v0 = AE::var(0, ());
    let v2 = AE::var(2, ());
    let arg = AE::nat(Nat::from(3u64), mk_addr("3"));

    // Two substitutions producing the same result should be pointer-equal after interning
    let r1 = subst(&env, &v2, &arg, 0);
    let r2 = subst(&env, &v2, &arg, 0);
    assert!(r1.ptr_eq(&r2), "interned results should be ptr-equal");
  }
}
