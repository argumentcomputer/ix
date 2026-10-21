//! Reordering a constant's leading binders, and the small weak-head reducer
//! of the structural transport (a port of
//! `Ix/Compile/Pass/Clique/Telescope.lean` and `Whnf.lean`).
//!
//! **Telescopes.** Lean puts a clique's fixed parameters in the *first*
//! function's order (`getFixedParamPerms`): the telescope of `f₀._mutual`
//! (well-founded), of every `f._f` (structural) and of the abstracted
//! decreasing proofs that use fixed parameters follows the clique's first
//! member. Under `σ` the first member changes, so the telescope is permuted
//! (a definitional change). The binders are opened with fresh free
//! variables, their bodies transformed, and closed again in the new order; a
//! new order in which a binder's type would mention a later binder is
//! refused.
//!
//! **Weak head normal forms.** The structural transport types a path into a
//! `below` dictionary by replaying Lean's `searchPProd` walk: the packed
//! motives are replaced by fresh free variables (the canaries), and the
//! `below` type is reduced by δ (definitions), β, ζ, ι (a recursor on a
//! constructor application, Nat literals as `zero`/`succ`) and projection of
//! a constructor, only to weak head normal form. Every step consumes `fuel`
//! (the callers pass [`WHNF_FUEL`](super::bounds::WHNF_FUEL)), and its
//! exhaustion is an error, never a term: [`whnf`] answers a weak head normal
//! form or fails, and [`whnf_step`] tells "normal" (`Ok(None)`) from "out of
//! fuel" (an error).

use bignat::Nat;
use num_bigint::BigUint;

use ix_common::env::{
  ConstantInfo, Expr, ExprData, Level, Literal, Name, RecursorVal,
};

use super::basic::{
  ConstOf, Local, R, TState, arr_nat, cnst, dotted, exprs, extract,
  inst_locals, instantiate_rev, mentions_fvar, mk_app_n, mk_forall, mk_lambda,
};
use crate::compile::pass3::expr::{
  get_app_fn_args, nat_usize, strip_mdata, subst_levels,
};

// ---------------------------------------------------------------------------
// Telescopes
// ---------------------------------------------------------------------------

/// `openBinders`: open `m` leading binders (`λ` when `is_lam`, else `∀`)
/// with fresh free variables. Fails when there are fewer.
pub fn open_binders(
  tm: &mut TState,
  is_lam: bool,
  m: usize,
  e: &Expr,
) -> R<(Vec<Local>, Expr)> {
  let mut cur = e.clone();
  let mut ls: Vec<Local> = Vec::new();
  for _ in 0..m {
    let s = strip_mdata(&cur);
    match (is_lam, s.as_data()) {
      (true, ExprData::Lam(nm, t, b, bi, _))
      | (false, ExprData::ForallE(nm, t, b, bi, _)) => {
        let typ = inst_locals(t, &exprs(&ls));
        let fvar = tm.fresh_fvar();
        ls.push(Local { fvar, user_name: nm.clone(), typ, bi: bi.clone() });
        cur = b.clone();
      },
      _ => return Err(format!("openBinders: expected {m} binders")),
    }
  }
  let body = inst_locals(&cur, &exprs(&ls));
  Ok((ls, body))
}

/// `closeBinders`: close the binders `xs` (outermost first) over `body`;
/// refuses an order in which a binder's type mentions a later binder.
pub fn close_binders(is_lam: bool, xs: &[Local], body: &Expr) -> R<Expr> {
  for (i, x) in xs.iter().enumerate() {
    if xs.iter().skip(i + 1).any(|y| mentions_fvar(&y.fvar, &x.typ)) {
      return Err(
        "closeBinders: the new order breaks a dependency between fixed \
         parameters"
          .to_string(),
      );
    }
  }
  Ok(if is_lam { mk_lambda(xs, body) } else { mk_forall(xs, body) })
}

/// `reorder`: `xs` reordered, new position `p` holding `xs[perm[p]]`;
/// `None` when `perm` indexes past `xs`.
pub fn reorder<T: Clone>(perm: &[usize], xs: &[T]) -> Option<Vec<T>> {
  perm.iter().map(|&i| xs.get(i).cloned()).collect()
}

/// A transformation of a binder type or body inside the transport.
pub type BinderK<'a> = &'a dyn Fn(&mut TState, &Expr) -> R<Expr>;

/// `withReorderedBinders2`: open `m` binders, transform their types with
/// `k_ty` and the body with `k_body` (the body first, then the types
/// outermost first), and close them in the order `perm` (new position `p` is
/// old binder `perm[p]`).
pub fn with_reordered_binders2(
  tm: &mut TState,
  is_lam: bool,
  m: usize,
  perm: &[usize],
  e: &Expr,
  k_ty: BinderK<'_>,
  k_body: BinderK<'_>,
) -> R<Expr> {
  let (xs, body) = open_binders(tm, is_lam, m, e)?;
  let body = k_body(tm, &body)?;
  let mut xs2: Vec<Local> = Vec::with_capacity(xs.len());
  for x in xs {
    let typ = k_ty(tm, &x.typ)?;
    xs2.push(Local { typ, ..x });
  }
  let Some(ys) = reorder(perm, &xs2) else {
    return Err(format!(
      "withReorderedBinders: the order {} indexes past the {} binders",
      arr_nat(perm),
      xs2.len()
    ));
  };
  close_binders(is_lam, &ys, &body)
}

/// `withReorderedBinders`: [`with_reordered_binders2`] with one
/// transformation `k` for the binders' types and the body.
pub fn with_reordered_binders(
  tm: &mut TState,
  is_lam: bool,
  m: usize,
  perm: &[usize],
  e: &Expr,
  k: BinderK<'_>,
) -> R<Expr> {
  with_reordered_binders2(tm, is_lam, m, perm, e, k, k)
}

/// `idPerm`: the identity permutation of `0..m`.
pub fn id_perm(m: usize) -> Vec<usize> {
  (0..m).collect()
}

// ---------------------------------------------------------------------------
// Weak head normal forms
// ---------------------------------------------------------------------------

pub fn n_nat_zero() -> Name {
  dotted("Nat.zero")
}
pub fn n_nat_succ() -> Name {
  dotted("Nat.succ")
}

/// `natLitToCtor`: `natLit k ↦ Nat.zero` / `Nat.succ (natLit (k - 1))`.
pub fn nat_lit_to_ctor(e: &Expr) -> Option<Expr> {
  let ExprData::Lit(Literal::NatVal(k), _) = e.as_data() else { return None };
  if k.0 == BigUint::default() {
    return Some(cnst(&n_nat_zero(), &[]));
  }
  let pred = Expr::lit(Literal::NatVal(Nat(&k.0 - 1u32)));
  Some(Expr::app(cnst(&n_nat_succ(), &[]), pred))
}

/// `betaApp`: beta-reduce a head `λ` against the arguments.
pub fn beta_app(f: &Expr, args: &[Expr]) -> Expr {
  let mut f = f.clone();
  let mut i = 0;
  while i < args.len() {
    let s = strip_mdata(&f);
    let ExprData::Lam(_, _, b, _, _) = s.as_data() else { break };
    f = b.clone();
    i += 1;
  }
  // `instantiateRev` takes the innermost binder's value first
  let rev: Vec<Expr> = args.iter().take(i).rev().cloned().collect();
  mk_app_n(instantiate_rev(&f, &rev), &extract(args, i, args.len()))
}

/// `whnfExhausted`: the error of an exhausted [`whnf`] / [`whnf_step`]
/// bound.
pub const WHNF_EXHAUSTED: &str = "whnf: fuel exhausted";

/// `whnfStep`: one weak-head step. `Ok(Some(e'))` for the next term,
/// `Ok(None)` when `e` is in weak head normal form, an error when the fuel
/// is exhausted (at this step, or while reducing a recursor's major premise
/// or a projected structure).
pub fn whnf_step(
  const_of: ConstOf<'_>,
  fuel: usize,
  e: &Expr,
) -> R<Option<Expr>> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err(WHNF_EXHAUSTED.to_string());
  };
  let e = strip_mdata(e);
  let (h, args) = get_app_fn_args(&e);
  let h = strip_mdata(&h);
  Ok(match h.as_data() {
    ExprData::Lam(..) => {
      if args.is_empty() {
        None
      } else {
        Some(beta_app(&h, &args))
      }
    },
    ExprData::LetE(_, _, v, b, _, _) => {
      Some(mk_app_n(instantiate_rev(b, std::slice::from_ref(v)), &args))
    },
    ExprData::Const(c, us, _) => match const_of(c) {
      Some(ConstantInfo::DefnInfo(d)) => {
        Some(mk_app_n(subst_levels(&d.cnst.level_params, us, &d.value), &args))
      },
      Some(ConstantInfo::RecInfo(r)) => {
        iota_step(const_of, fuel, &r, us, &args)?
      },
      _ => None,
    },
    ExprData::Proj(_, i, s, _) => {
      let s = whnf(const_of, fuel, s)?;
      let (kh, kargs) = get_app_fn_args(&s);
      match kh.as_data() {
        ExprData::Const(k, _, _) => match const_of(k) {
          Some(ConstantInfo::CtorInfo(cv)) => kargs
            .get(nat_usize(&cv.num_params).saturating_add(nat_usize(i)))
            .map(|fld| mk_app_n(fld.clone(), &args)),
          _ => None,
        },
        _ => None,
      }
    },
    _ => None,
  })
}

/// The recursor case of [`whnf_step`]: ι-reduce the recursor `r` (at the
/// levels `us`) applied to `args` when its major premise reduces to a
/// constructor application (or a Nat literal).
fn iota_step(
  const_of: ConstOf<'_>,
  fuel: usize,
  r: &RecursorVal,
  us: &[Level],
  args: &[Expr],
) -> R<Option<Expr>> {
  let num_pre = nat_usize(&r.num_params)
    .saturating_add(nat_usize(&r.num_motives))
    .saturating_add(nat_usize(&r.num_minors));
  let major_idx = num_pre.saturating_add(nat_usize(&r.num_indices));
  let Some(major) = args.get(major_idx) else { return Ok(None) };
  let major = whnf(const_of, fuel, major)?;
  let major = nat_lit_to_ctor(&major).unwrap_or(major);
  let (kh, kargs) = get_app_fn_args(&major);
  let ExprData::Const(k, _, _) = kh.as_data() else { return Ok(None) };
  let rule = r.rules.iter().find(|rule| rule.ctor == *k);
  let (Some(rule), Some(ConstantInfo::CtorInfo(cv))) = (rule, const_of(k))
  else {
    return Ok(None);
  };
  let rhs = subst_levels(&r.cnst.level_params, us, &rule.rhs);
  let mut pre = extract(args, 0, num_pre);
  pre.extend(extract(&kargs, nat_usize(&cv.num_params), kargs.len()));
  let rest = extract(args, major_idx + 1, args.len());
  Ok(Some(mk_app_n(mk_app_n(rhs, &pre), &rest)))
}

/// `whnf`: the weak head normal form of `e`, within `fuel` steps; an error
/// when the fuel is exhausted before a normal form is reached.
pub fn whnf(const_of: ConstOf<'_>, fuel: usize, e: &Expr) -> R<Expr> {
  let mut fuel = fuel;
  let mut cur = e.clone();
  loop {
    let Some(rest) = fuel.checked_sub(1) else {
      return Err(WHNF_EXHAUSTED.to_string());
    };
    fuel = rest;
    match whnf_step(const_of, fuel, &cur)? {
      Some(next) => cur = next,
      None => return Ok(cur),
    }
  }
}

#[cfg(test)]
mod tests {
  use ix_common::env::{
    BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
    DefinitionSafety, DefinitionVal, Expr, Literal, Name, ReducibilityHints,
  };

  use super::{
    TState, WHNF_EXHAUSTED, close_binders, nat_lit_to_ctor, open_binders,
    reorder, whnf, whnf_step, with_reordered_binders,
  };
  use crate::compile::pass3::clique::basic::{bvar, cnst, dotted, sort0};
  use crate::compile::pass3::clique::bounds::WHNF_FUEL;
  use crate::compile::pass3::expr::nat;

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn lam(x: &str, t: Expr, b: Expr) -> Expr {
    Expr::lam(dotted(x), t, b, BinderInfo::Default)
  }

  fn app(f: Expr, a: Expr) -> Expr {
    Expr::app(f, a)
  }

  fn cnst_val(n: &str) -> ConstantVal {
    ConstantVal { name: dotted(n), level_params: vec![], typ: sort0() }
  }

  fn defn(n: &str, value: Expr) -> ConstantInfo {
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst: cnst_val(n),
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![dotted(n)],
    })
  }

  fn env(n: &Name) -> Option<ConstantInfo> {
    if *n == dotted("id") {
      Some(defn("id", lam("x", c("T"), bvar(0))))
    } else if *n == dotted("loop") {
      Some(defn("loop", c("loop")))
    } else if *n == dotted("Pair.mk") {
      Some(ConstantInfo::CtorInfo(ConstructorVal {
        cnst: cnst_val("Pair.mk"),
        induct: dotted("Pair"),
        cidx: nat(0),
        num_params: nat(0),
        num_fields: nat(2),
        is_unsafe: false,
      }))
    } else {
      None
    }
  }

  #[test]
  fn whnf_normal_step_and_exhaustion() {
    // normal
    assert_eq!(whnf_step(&env, 5, &c("A")), Ok(None));
    assert_eq!(whnf(&env, WHNF_FUEL, &c("A")), Ok(c("A")));
    // one δ step, then a β step; `mdata` at the head is stripped
    let e = app(c("id"), c("A"));
    let unfolded = app(lam("x", c("T"), bvar(0)), c("A"));
    assert_eq!(whnf_step(&env, 5, &e), Ok(Some(unfolded.clone())));
    assert_eq!(whnf_step(&env, 5, &unfolded), Ok(Some(c("A"))));
    let md = Expr::mdata(vec![(dotted("k"), DataValue::OfBool(true))], e);
    assert_eq!(whnf(&env, WHNF_FUEL, &md), Ok(c("A")));
    // projection of a constructor
    let pair = app(app(c("Pair.mk"), c("a")), c("b"));
    let p = Expr::proj(dotted("Pair"), nat(1), pair);
    assert_eq!(whnf(&env, WHNF_FUEL, &p), Ok(c("b")));
    // exhaustion is an error, counted as Lean counts it
    let out = Err(WHNF_EXHAUSTED.to_string());
    assert_eq!(whnf(&env, WHNF_FUEL, &c("loop")), out);
    assert_eq!(whnf_step(&env, 0, &c("A")), Err(WHNF_EXHAUSTED.to_string()));
    assert_eq!(whnf(&env, 0, &c("A")), out);
    assert_eq!(whnf(&env, 1, &c("A")), out);
    assert_eq!(whnf(&env, 2, &c("A")), Ok(c("A")));
    // literals as constructors
    assert_eq!(
      nat_lit_to_ctor(&Expr::lit(Literal::NatVal(nat(0)))),
      Some(c("Nat.zero"))
    );
    assert_eq!(
      nat_lit_to_ctor(&Expr::lit(Literal::NatVal(nat(3)))),
      Some(app(c("Nat.succ"), Expr::lit(Literal::NatVal(nat(2)))))
    );
  }

  #[test]
  fn reordered_binders() {
    assert_eq!(reorder(&[1, 0], &["a", "b"]), Some(vec!["b", "a"]));
    assert_eq!(reorder(&[2], &["a", "b"]), None);
    // λ (a : A) (b : B). F a b  ↦  λ (b : B) (a : A). F a b
    let f = |x, y| app(app(c("F"), x), y);
    let e = lam("a", c("A"), lam("b", c("B"), f(bvar(1), bvar(0))));
    let want = lam("b", c("B"), lam("a", c("A"), f(bvar(0), bvar(1))));
    let mut tm = TState::default();
    let id = |_: &mut TState, x: &Expr| Ok::<Expr, String>(x.clone());
    let out = with_reordered_binders(&mut tm, true, 2, &[1, 0], &e, &id);
    assert_eq!(out, Ok(want));
    assert_eq!(tm.next, 2);
    assert_eq!(
      with_reordered_binders(&mut tm, true, 2, &[0, 5], &e, &id),
      Err(
        "withReorderedBinders: the order #[0, 5] indexes past the 2 binders"
          .to_string()
      )
    );
    assert_eq!(
      open_binders(&mut tm, true, 3, &e).map(|(xs, _)| xs.len()),
      Err("openBinders: expected 3 binders".to_string())
    );
    // a type that mentions a later binder is refused
    let dep = lam("a", c("A"), lam("b", app(c("P"), bvar(0)), bvar(0)));
    let (xs, body) = open_binders(&mut tm, true, 2, &dep).unwrap();
    let swapped = [xs[1].clone(), xs[0].clone()];
    assert!(close_binders(true, &swapped, &body).is_err());
    assert_eq!(close_binders(true, &xs, &body), Ok(dep));
  }
}
