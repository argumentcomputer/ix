//! Non-monadic utility functions on `Val` and `KExpr`.
//!
//! These helpers don't depend on the TypeChecker and can be used freely.

use num_bigint::BigUint;

use crate::ix::address::Address;
use crate::ix::env::{Literal, Name, ReducibilityHints};
use crate::lean::nat::Nat;

use super::types::{
  KConstantInfo, KEnv, KExpr, KExprData, KLevel, KLevelData,
  MetaMode, Primitives, TypedConst,
};
use super::value::{Head, Thunk, Val, ValInner};

/// Euclidean GCD for BigUint.
fn biguint_gcd(a: &BigUint, b: &BigUint) -> BigUint {
  let mut a = a.clone();
  let mut b = b.clone();
  while b != BigUint::ZERO {
    let t = b.clone();
    b = &a % &b;
    a = t;
  }
  a
}

/// Extract a natural number from a Val if it's a Nat literal, a Nat.zero
/// constructor, or a Nat.zero neutral.
pub fn extract_nat_val<M: MetaMode>(v: &Val<M>, prims: &Primitives) -> Option<Nat> {
  match v.inner() {
    ValInner::Lit(Literal::NatVal(n)) => Some(n.clone()),
    ValInner::Ctor {
      addr,
      cidx: 0,
      spine,
      ..
    } => {
      if Some(addr) == prims.nat_zero.as_ref() && spine.is_empty() {
        Some(Nat::from(0u64))
      } else {
        None
      }
    }
    ValInner::Neutral {
      head: Head::Const { addr, .. },
      spine,
    } => {
      if Some(addr) == prims.nat_zero.as_ref() && spine.is_empty() {
        Some(Nat::from(0u64))
      } else {
        None
      }
    }
    _ => None,
  }
}

/// Check if an address is a nat primitive binary operation.
pub fn is_nat_bin_op(addr: &Address, prims: &Primitives) -> bool {
  [
    &prims.nat_add,
    &prims.nat_sub,
    &prims.nat_mul,
    &prims.nat_pow,
    &prims.nat_gcd,
    &prims.nat_mod,
    &prims.nat_div,
    &prims.nat_beq,
    &prims.nat_ble,
    &prims.nat_land,
    &prims.nat_lor,
    &prims.nat_xor,
    &prims.nat_shift_left,
    &prims.nat_shift_right,
  ]
  .iter()
  .any(|p| p.as_ref() == Some(addr))
}

/// Check if a value is Nat.zero (constructor, neutral, or literal 0).
pub fn is_nat_zero_val<M: MetaMode>(v: &Val<M>, prims: &Primitives) -> bool {
  match v.inner() {
    ValInner::Lit(Literal::NatVal(n)) => n.0 == BigUint::ZERO,
    ValInner::Neutral {
      head: Head::Const { addr, .. },
      spine,
    } => prims.nat_zero.as_ref() == Some(addr) && spine.is_empty(),
    ValInner::Ctor { addr, spine, .. } => {
      prims.nat_zero.as_ref() == Some(addr) && spine.is_empty()
    }
    _ => false,
  }
}

/// Extract the predecessor thunk from a structural Nat.succ value, without forcing.
/// Only matches Ctor(nat_succ, [thunk]) or Neutral(nat_succ, [thunk]).
/// Does NOT match Lit(NatVal(n)) — literals are handled by computeNatPrim in O(1).
/// Matching literals here would cause O(n) recursion in the symbolic step-case reductions.
pub fn extract_succ_pred<M: MetaMode>(
  v: &Val<M>,
  prims: &Primitives,
) -> Option<Thunk<M>> {
  match v.inner() {
    ValInner::Neutral {
      head: Head::Const { addr, .. },
      spine,
    } if prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 => {
      Some(spine[0].clone())
    }
    ValInner::Ctor { addr, spine, .. }
      if prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 =>
    {
      Some(spine[0].clone())
    }
    _ => None,
  }
}

/// Check if an address is nat_succ.
pub fn is_nat_succ(addr: &Address, prims: &Primitives) -> bool {
  prims.nat_succ.as_ref() == Some(addr)
}

/// Compute a nat binary primitive operation.
pub fn compute_nat_prim<M: MetaMode>(
  addr: &Address,
  a: &Nat,
  b: &Nat,
  prims: &Primitives,
) -> Option<Val<M>> {
  let nat_val = |n: BigUint| Val::mk_lit(Literal::NatVal(Nat(n)));
  let zero = BigUint::ZERO;

  let result = if prims.nat_add.as_ref() == Some(addr) {
    nat_val(&a.0 + &b.0)
  } else if prims.nat_sub.as_ref() == Some(addr) {
    nat_val(if a.0 >= b.0 { &a.0 - &b.0 } else { zero })
  } else if prims.nat_mul.as_ref() == Some(addr) {
    nat_val(&a.0 * &b.0)
  } else if prims.nat_pow.as_ref() == Some(addr) {
    let exp = b.to_u64().unwrap_or(0) as u32;
    nat_val(a.0.pow(exp))
  } else if prims.nat_gcd.as_ref() == Some(addr) {
    nat_val(biguint_gcd(&a.0, &b.0))
  } else if prims.nat_mod.as_ref() == Some(addr) {
    nat_val(if b.0 == zero {
      a.0.clone()
    } else {
      &a.0 % &b.0
    })
  } else if prims.nat_div.as_ref() == Some(addr) {
    nat_val(if b.0 == zero {
      zero
    } else {
      &a.0 / &b.0
    })
  } else if prims.nat_beq.as_ref() == Some(addr) {
    let b_val = if a == b {
      prims.bool_true.as_ref()?
    } else {
      prims.bool_false.as_ref()?
    };
    Val::mk_ctor(
      b_val.clone(),
      Vec::new(),
      M::Field::<Name>::default(),
      if a == b { 1 } else { 0 },
      0,
      0,
      prims.bool_type.clone()?,
      Vec::new(),
    )
  } else if prims.nat_ble.as_ref() == Some(addr) {
    let b_val = if a <= b {
      prims.bool_true.as_ref()?
    } else {
      prims.bool_false.as_ref()?
    };
    Val::mk_ctor(
      b_val.clone(),
      Vec::new(),
      M::Field::<Name>::default(),
      if a <= b { 1 } else { 0 },
      0,
      0,
      prims.bool_type.clone()?,
      Vec::new(),
    )
  } else if prims.nat_land.as_ref() == Some(addr) {
    nat_val(&a.0 & &b.0)
  } else if prims.nat_lor.as_ref() == Some(addr) {
    nat_val(&a.0 | &b.0)
  } else if prims.nat_xor.as_ref() == Some(addr) {
    nat_val(&a.0 ^ &b.0)
  } else if prims.nat_shift_left.as_ref() == Some(addr) {
    let shift = b.to_u64().unwrap_or(0);
    nat_val(&a.0 << shift)
  } else if prims.nat_shift_right.as_ref() == Some(addr) {
    let shift = b.to_u64().unwrap_or(0);
    nat_val(&a.0 >> shift)
  } else {
    return None;
  };
  Some(result)
}

/// Convert a Nat.zero literal to a Nat.zero constructor Val (non-thunked).
pub fn nat_lit_to_ctor_val<M: MetaMode>(
  n: &Nat,
  prims: &Primitives,
) -> Option<Val<M>> {
  if n.0 == BigUint::ZERO {
    let zero_addr = prims.nat_zero.as_ref()?;
    let nat_addr = prims.nat.as_ref()?;
    Some(Val::mk_ctor(
      zero_addr.clone(),
      Vec::new(),
      M::Field::<Name>::default(),
      0,
      0,
      0,
      nat_addr.clone(),
      Vec::new(),
    ))
  } else {
    None
  }
}

/// Try to reduce a projection on a constructor value that has already been forced.
/// Returns the thunk at the projected field index if successful.
pub fn reduce_val_proj_forced<M: MetaMode>(
  ctor: &Val<M>,
  proj_idx: usize,
  proj_type_addr: &Address,
) -> Option<Thunk<M>> {
  match ctor.inner() {
    ValInner::Ctor {
      induct_addr,
      num_params,
      spine,
      ..
    } => {
      if induct_addr != proj_type_addr {
        return None;
      }
      let field_idx = num_params + proj_idx;
      if field_idx < spine.len() {
        Some(spine[field_idx].clone())
      } else {
        None
      }
    }
    _ => None,
  }
}

/// Get the reducibility hints for a Val's head constant.
pub fn get_delta_info<M: MetaMode>(
  v: &Val<M>,
  env: &KEnv<M>,
) -> Option<ReducibilityHints> {
  match v.inner() {
    ValInner::Neutral {
      head: Head::Const { addr, .. },
      ..
    } => match env.get(addr)? {
      KConstantInfo::Definition(d) => Some(d.hints),
      KConstantInfo::Theorem(_) => Some(ReducibilityHints::Opaque),
      _ => None,
    },
    _ => None,
  }
}

/// Check if a Val is a constructor application of a structure-like inductive.
pub fn is_struct_like_app<M: MetaMode>(
  v: &Val<M>,
  typed_consts: &rustc_hash::FxHashMap<Address, TypedConst<M>>,
) -> bool {
  match v.inner() {
    ValInner::Ctor { induct_addr, .. } => {
      is_struct_like_app_by_addr(induct_addr, typed_consts)
    }
    _ => false,
  }
}

/// Check if an address corresponds to a structure-like inductive.
pub fn is_struct_like_app_by_addr<M: MetaMode>(
  addr: &Address,
  typed_consts: &rustc_hash::FxHashMap<Address, TypedConst<M>>,
) -> bool {
  matches!(
    typed_consts.get(addr),
    Some(TypedConst::Inductive {
      is_struct: true,
      ..
    })
  )
}

// ============================================================================
// KExpr helper functions for validation
// ============================================================================

/// Extract result universe level from an inductive type expression.
/// Walks through forall chain to the final Sort.
pub fn get_ind_result_level<M: MetaMode>(
  ty: &KExpr<M>,
) -> Option<KLevel<M>> {
  match ty.data() {
    KExprData::ForallE(_, body, _, _) => get_ind_result_level(body),
    KExprData::Sort(lvl) => Some(lvl.clone()),
    _ => None,
  }
}

/// Extract the motive's return sort from a recursor type.
/// Walks past `num_params` Pi binders, then walks the motive's domain
/// to the final Sort.
pub fn get_motive_sort<M: MetaMode>(
  rec_type: &KExpr<M>,
  num_params: usize,
) -> Option<KLevel<M>> {
  fn skip_params<M: MetaMode>(
    ty: &KExpr<M>,
    remaining: usize,
  ) -> Option<KLevel<M>> {
    match remaining {
      0 => match ty.data() {
        KExprData::ForallE(motive_dom, _, _, _) => {
          walk_to_sort(motive_dom)
        }
        _ => None,
      },
      n => match ty.data() {
        KExprData::ForallE(_, body, _, _) => {
          skip_params(body, n - 1)
        }
        _ => None,
      },
    }
  }
  fn walk_to_sort<M: MetaMode>(ty: &KExpr<M>) -> Option<KLevel<M>> {
    match ty.data() {
      KExprData::ForallE(_, body, _, _) => walk_to_sort(body),
      KExprData::Sort(lvl) => Some(lvl.clone()),
      _ => None,
    }
  }
  skip_params(rec_type, num_params)
}

/// Get major inductive address from recursor type by walking through
/// params+motives+minors+indices to find the major premise's head constant.
pub fn get_major_induct<M: MetaMode>(
  ty: &KExpr<M>,
  num_params: usize,
  num_motives: usize,
  num_minors: usize,
  num_indices: usize,
) -> Option<Address> {
  let total = num_params + num_motives + num_minors + num_indices;
  fn go<M: MetaMode>(
    ty: &KExpr<M>,
    remaining: usize,
  ) -> Option<Address> {
    match remaining {
      0 => match ty.data() {
        KExprData::ForallE(dom, _, _, _) => {
          dom.get_app_fn().const_addr().cloned()
        }
        _ => None,
      },
      n => match ty.data() {
        KExprData::ForallE(_, body, _, _) => go(body, n - 1),
        _ => None,
      },
    }
  }
  go(ty, total)
}

/// Check if an expression mentions a constant at the given address.
pub fn expr_mentions_const<M: MetaMode>(
  e: &KExpr<M>,
  addr: &Address,
) -> bool {
  match e.data() {
    KExprData::Const(a, _, _) => a == addr,
    KExprData::App(f, a) => {
      expr_mentions_const(f, addr)
        || expr_mentions_const(a, addr)
    }
    KExprData::Lam(ty, body, _, _)
    | KExprData::ForallE(ty, body, _, _) => {
      expr_mentions_const(ty, addr)
        || expr_mentions_const(body, addr)
    }
    KExprData::LetE(ty, val, body, _) => {
      expr_mentions_const(ty, addr)
        || expr_mentions_const(val, addr)
        || expr_mentions_const(body, addr)
    }
    KExprData::Proj(_, _, s, _) => expr_mentions_const(s, addr),
    _ => false,
  }
}

/// Walk a Pi chain past `num_params + num_fields` binders to get the
/// return type.
pub fn get_ctor_return_type<M: MetaMode>(
  ty: &KExpr<M>,
  num_params: usize,
  num_fields: usize,
) -> KExpr<M> {
  let total = num_params + num_fields;
  fn go<M: MetaMode>(ty: &KExpr<M>, n: usize) -> KExpr<M> {
    match n {
      0 => ty.clone(),
      _ => match ty.data() {
        KExprData::ForallE(_, body, _, _) => go(body, n - 1),
        _ => ty.clone(),
      },
    }
  }
  go(ty, total)
}

/// Lift free bvar indices by `n`. Under `depth` binders, bvars < depth
/// are bound and stay; bvars >= depth are free and get shifted by n.
pub fn lift_bvars<M: MetaMode>(
  e: &KExpr<M>,
  n: usize,
  depth: usize,
) -> KExpr<M> {
  if n == 0 {
    return e.clone();
  }
  lift_go(e, n, depth)
}

fn lift_go<M: MetaMode>(
  e: &KExpr<M>,
  n: usize,
  d: usize,
) -> KExpr<M> {
  match e.data() {
    KExprData::BVar(idx, name) => {
      if *idx >= d {
        KExpr::bvar(idx + n, name.clone())
      } else {
        e.clone()
      }
    }
    KExprData::App(f, a) => {
      KExpr::app(lift_go(f, n, d), lift_go(a, n, d))
    }
    KExprData::Lam(ty, body, name, bi) => KExpr::lam(
      lift_go(ty, n, d),
      lift_go(body, n, d + 1),
      name.clone(),
      bi.clone(),
    ),
    KExprData::ForallE(ty, body, name, bi) => KExpr::forall_e(
      lift_go(ty, n, d),
      lift_go(body, n, d + 1),
      name.clone(),
      bi.clone(),
    ),
    KExprData::LetE(ty, val, body, name) => KExpr::let_e(
      lift_go(ty, n, d),
      lift_go(val, n, d),
      lift_go(body, n, d + 1),
      name.clone(),
    ),
    KExprData::Proj(ta, idx, s, tn) => {
      KExpr::proj(ta.clone(), *idx, lift_go(s, n, d), tn.clone())
    }
    KExprData::Sort(_) | KExprData::Const(..) | KExprData::Lit(_) => {
      e.clone()
    }
  }
}

/// Substitute universe level parameters in a level.
fn subst_level<M: MetaMode>(
  l: &KLevel<M>,
  level_subst: &[KLevel<M>],
) -> KLevel<M> {
  if level_subst.is_empty() {
    return l.clone();
  }
  match l.data() {
    KLevelData::Param(i, _) => {
      if *i < level_subst.len() {
        level_subst[*i].clone()
      } else {
        l.clone()
      }
    }
    KLevelData::Succ(inner) => {
      KLevel::succ(subst_level(inner, level_subst))
    }
    KLevelData::Max(a, b) => {
      KLevel::max(subst_level(a, level_subst), subst_level(b, level_subst))
    }
    KLevelData::IMax(a, b) => {
      KLevel::imax(subst_level(a, level_subst), subst_level(b, level_subst))
    }
    KLevelData::Zero => l.clone(),
  }
}

/// Shift bvar indices and level params in an expression from a constructor
/// context to a recursor rule context.
///
/// - `field_depth`: number of field binders above this expr in the ctor type
/// - `bvar_shift`: amount to shift param bvar refs (= numMotives + numMinors)
/// - `level_subst`: level parameter substitution
///
/// Bvar i at depth d is a param ref when i >= d + field_depth.
pub fn shift_ctor_to_rule<M: MetaMode>(
  e: &KExpr<M>,
  field_depth: usize,
  bvar_shift: usize,
  level_subst: &[KLevel<M>],
) -> KExpr<M> {
  if bvar_shift == 0 && level_subst.is_empty() {
    return e.clone();
  }
  shift_go(e, field_depth, bvar_shift, level_subst, 0)
}

fn shift_go<M: MetaMode>(
  e: &KExpr<M>,
  field_depth: usize,
  bvar_shift: usize,
  level_subst: &[KLevel<M>],
  depth: usize,
) -> KExpr<M> {
  match e.data() {
    KExprData::BVar(i, n) => {
      if *i >= depth + field_depth {
        KExpr::bvar(i + bvar_shift, n.clone())
      } else {
        e.clone()
      }
    }
    KExprData::App(f, a) => KExpr::app(
      shift_go(f, field_depth, bvar_shift, level_subst, depth),
      shift_go(a, field_depth, bvar_shift, level_subst, depth),
    ),
    KExprData::Lam(ty, body, n, bi) => KExpr::lam(
      shift_go(ty, field_depth, bvar_shift, level_subst, depth),
      shift_go(body, field_depth, bvar_shift, level_subst, depth + 1),
      n.clone(),
      bi.clone(),
    ),
    KExprData::ForallE(ty, body, n, bi) => KExpr::forall_e(
      shift_go(ty, field_depth, bvar_shift, level_subst, depth),
      shift_go(body, field_depth, bvar_shift, level_subst, depth + 1),
      n.clone(),
      bi.clone(),
    ),
    KExprData::LetE(ty, val, body, n) => KExpr::let_e(
      shift_go(ty, field_depth, bvar_shift, level_subst, depth),
      shift_go(val, field_depth, bvar_shift, level_subst, depth),
      shift_go(body, field_depth, bvar_shift, level_subst, depth + 1),
      n.clone(),
    ),
    KExprData::Proj(ta, idx, s, tn) => KExpr::proj(
      ta.clone(),
      *idx,
      shift_go(s, field_depth, bvar_shift, level_subst, depth),
      tn.clone(),
    ),
    KExprData::Sort(l) => {
      KExpr::sort(subst_level(l, level_subst))
    }
    KExprData::Const(addr, lvls, name) => {
      if level_subst.is_empty() {
        e.clone()
      } else {
        let new_lvls: Vec<_> =
          lvls.iter().map(|l| subst_level(l, level_subst)).collect();
        KExpr::cnst(addr.clone(), new_lvls, name.clone())
      }
    }
    KExprData::Lit(_) => e.clone(),
  }
}

/// Substitute extra nested param bvars in a constructor body expression.
///
/// After peeling `cnp` params from the ctor type, extra param bvars occupy
/// indices `field_depth..field_depth+num_extra-1` at depth 0. Replace them
/// with `vals` and shift shared param bvars down by `num_extra`.
///
/// - `field_depth`: number of field binders enclosing this expr
/// - `num_extra`: number of extra nested params (cnp - np)
/// - `vals`: replacement values (already shifted for the rule context)
pub fn subst_nested_params<M: MetaMode>(
  e: &KExpr<M>,
  field_depth: usize,
  num_extra: usize,
  vals: &[KExpr<M>],
) -> KExpr<M> {
  if num_extra == 0 {
    return e.clone();
  }
  subst_np_go(e, field_depth, num_extra, vals, 0)
}

fn subst_np_go<M: MetaMode>(
  e: &KExpr<M>,
  field_depth: usize,
  num_extra: usize,
  vals: &[KExpr<M>],
  depth: usize,
) -> KExpr<M> {
  match e.data() {
    KExprData::BVar(i, n) => {
      if *i < depth + field_depth {
        // Bound by field/local binder
        e.clone()
      } else {
        let free_idx = i - (depth + field_depth);
        if free_idx < num_extra {
          // Extra nested param: substitute with vals[free_idx] shifted
          // up by depth
          shift_ctor_to_rule(
            &vals[free_idx],
            0,
            depth,
            &[],
          )
        } else {
          // Shared param: shift down
          KExpr::bvar(i - num_extra, n.clone())
        }
      }
    }
    KExprData::App(f, a) => KExpr::app(
      subst_np_go(f, field_depth, num_extra, vals, depth),
      subst_np_go(a, field_depth, num_extra, vals, depth),
    ),
    KExprData::Lam(ty, body, n, bi) => KExpr::lam(
      subst_np_go(ty, field_depth, num_extra, vals, depth),
      subst_np_go(body, field_depth, num_extra, vals, depth + 1),
      n.clone(),
      bi.clone(),
    ),
    KExprData::ForallE(ty, body, n, bi) => KExpr::forall_e(
      subst_np_go(ty, field_depth, num_extra, vals, depth),
      subst_np_go(body, field_depth, num_extra, vals, depth + 1),
      n.clone(),
      bi.clone(),
    ),
    KExprData::LetE(ty, val, body, n) => KExpr::let_e(
      subst_np_go(ty, field_depth, num_extra, vals, depth),
      subst_np_go(val, field_depth, num_extra, vals, depth),
      subst_np_go(body, field_depth, num_extra, vals, depth + 1),
      n.clone(),
    ),
    KExprData::Proj(ta, idx, s, tn) => KExpr::proj(
      ta.clone(),
      *idx,
      subst_np_go(s, field_depth, num_extra, vals, depth),
      tn.clone(),
    ),
    _ => e.clone(),
  }
}
