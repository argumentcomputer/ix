//! Reordering a constant's leading binders, and the small weak-head reducer
//! of the structural transport (a port of `Ix/Compile/Clique/Telescope.lean`
//! and `Whnf.lean`).

use ix_common::env::{ConstantInfo, Expr, ExprData, Name};

use super::basic::*;
use crate::compile::pass3::expr::{
  get_app_fn_args, nat_usize, strip_mdata, subst_levels,
};

/// `openBinders`.
pub fn open_binders(
  tm: &mut Tm,
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
        let t2 = inst_locals(t, &exprs(&ls));
        let f = tm.fresh();
        ls.push(local(f, nm.clone(), t2, bi.clone()));
        cur = b.clone();
      },
      _ => return Err(format!("openBinders: expected {m} binders")),
    }
  }
  let body = inst_locals(&cur, &exprs(&ls));
  Ok((ls, body))
}

/// `closeBinders`.
pub fn close_binders(is_lam: bool, xs: &[Local], body: &Expr) -> R<Expr> {
  for i in 0..xs.len() {
    for j in i + 1..xs.len() {
      if mentions_fvar(&xs[j].fvar, &xs[i].typ) {
        return Err(
          "closeBinders: the new order breaks a dependency between fixed parameters"
            .into(),
        );
      }
    }
  }
  Ok(if is_lam { mk_lambda(xs, body) } else { mk_forall(xs, body) })
}

/// `withReorderedBinders2` (and `withReorderedBinders` with `k_ty = k_body`).
pub fn with_reordered_binders2(
  tm: &mut Tm,
  is_lam: bool,
  m: usize,
  perm: &[usize],
  e: &Expr,
  k_ty: &mut dyn FnMut(&mut Tm, &Expr) -> R<Expr>,
  k_body: &mut dyn FnMut(&mut Tm, &Expr) -> R<Expr>,
) -> R<Expr> {
  let (xs, body) = open_binders(tm, is_lam, m, e)?;
  let body2 = k_body(tm, &body)?;
  let mut xs2: Vec<Local> = Vec::new();
  for x in &xs {
    let t = k_ty(tm, &x.typ)?;
    xs2.push(Local { typ: t, ..x.clone() });
  }
  close_binders(is_lam, &reorder(perm, &xs2), &body2)
}

pub fn with_reordered_binders(
  tm: &mut Tm,
  is_lam: bool,
  m: usize,
  perm: &[usize],
  e: &Expr,
  k: &mut dyn FnMut(&mut Tm, &Expr) -> R<Expr>,
) -> R<Expr> {
  let (xs, body) = open_binders(tm, is_lam, m, e)?;
  let body2 = k(tm, &body)?;
  let mut xs2: Vec<Local> = Vec::new();
  for x in &xs {
    let t = k(tm, &x.typ)?;
    xs2.push(Local { typ: t, ..x.clone() });
  }
  close_binders(is_lam, &reorder(perm, &xs2), &body2)
}

// ---------------------------------------------------------------------------
// Whnf
// ---------------------------------------------------------------------------

pub fn n_nat_zero() -> Name {
  ln("Nat.zero")
}
pub fn n_nat_succ() -> Name {
  ln("Nat.succ")
}

/// `natLitToCtor`.
pub fn nat_lit_to_ctor(e: &Expr) -> Option<Expr> {
  match e.as_data() {
    ExprData::Lit(ix_common::env::Literal::NatVal(k), _) => {
      if k.0 == num_bigint::BigUint::from(0u32) {
        Some(cnst(&n_nat_zero(), &[]))
      } else {
        let k1 = bignat::Nat(k.0.clone() - num_bigint::BigUint::from(1u32));
        Some(Expr::app(
          cnst(&n_nat_succ(), &[]),
          Expr::lit(ix_common::env::Literal::NatVal(k1)),
        ))
      }
    },
    _ => None,
  }
}

/// `betaApp`.
pub fn beta_app(f: &Expr, args: &[Expr]) -> Expr {
  let mut f = f.clone();
  let mut i = 0;
  let mut acc: Vec<Expr> = Vec::new();
  for a in args {
    let s = strip_mdata(&f);
    match s.as_data() {
      ExprData::Lam(_, _, b, _, _) => {
        acc.push(a.clone());
        f = b.clone();
        i += 1;
      },
      _ => break,
    }
  }
  let rev: Vec<Expr> = acc.into_iter().rev().collect();
  mk_app_n(instantiate_rev(&f, &rev), &args[i..])
}

/// `whnfStep`.
pub fn whnf_step(const_of: ConstOf<'_>, fuel: usize, e: &Expr) -> Option<Expr> {
  if fuel == 0 {
    return None;
  }
  let fuel = fuel - 1;
  let e = strip_mdata(e);
  let (h, args) = get_app_fn_args(&e);
  let h = strip_mdata(&h);
  match h.as_data() {
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
        let major_idx = nat_usize(&r.num_params)
          + nat_usize(&r.num_motives)
          + nat_usize(&r.num_minors)
          + nat_usize(&r.num_indices);
        if major_idx < args.len() {
          let major = whnf(const_of, fuel, &args[major_idx]);
          let major = nat_lit_to_ctor(&major).unwrap_or(major);
          let (kh, kargs) = get_app_fn_args(&major);
          match kh.as_data() {
            ExprData::Const(k, _, _) => {
              let rule = r.rules.iter().find(|rl| rl.ctor == *k);
              match (rule, const_of(k)) {
                (Some(rule), Some(ConstantInfo::CtorInfo(cv))) => {
                  let rhs = subst_levels(&r.cnst.level_params, us, &rule.rhs);
                  let pre_n = nat_usize(&r.num_params)
                    + nat_usize(&r.num_motives)
                    + nat_usize(&r.num_minors);
                  let mut pre: Vec<Expr> = extract(&args, 0, pre_n);
                  let fields =
                    extract(&kargs, nat_usize(&cv.num_params), kargs.len());
                  pre.extend(fields);
                  Some(mk_app_n(
                    mk_app_n(rhs, &pre),
                    &extract(&args, major_idx + 1, args.len()),
                  ))
                },
                _ => None,
              }
            },
            _ => None,
          }
        } else {
          None
        }
      },
      _ => None,
    },
    ExprData::Proj(_, i, s, _) => {
      let s2 = whnf(const_of, fuel, s);
      let (kh, kargs) = get_app_fn_args(&s2);
      match kh.as_data() {
        ExprData::Const(k, _, _) => match const_of(k) {
          Some(ConstantInfo::CtorInfo(cv)) => {
            let idx = nat_usize(&cv.num_params) + nat_usize(i);
            kargs.get(idx).map(|fld| mk_app_n(fld.clone(), &args))
          },
          _ => None,
        },
        _ => None,
      }
    },
    _ => None,
  }
}

/// `whnf`.
pub fn whnf(const_of: ConstOf<'_>, fuel: usize, e: &Expr) -> Expr {
  let mut fuel = fuel;
  let mut cur = e.clone();
  loop {
    if fuel == 0 {
      return cur;
    }
    fuel -= 1;
    match whnf_step(const_of, fuel, &cur) {
      Some(e2) => cur = e2,
      None => return cur,
    }
  }
}

pub const WHNF_FUEL: usize = 256;
