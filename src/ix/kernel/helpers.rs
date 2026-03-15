//! Non-monadic utility functions on `Val` and `KExpr`.
//!
//! These helpers don't depend on the TypeChecker and can be used freely.

use num_bigint::BigUint;

use crate::ix::address::Address;
use crate::ix::env::{Literal, ReducibilityHints};
use crate::lean::nat::Nat;

use super::types::{
  KConstantInfo, KEnv, KExpr, KExprData, KLevel, KLevelData,
  MetaId, MetaMode, Primitives, TypedConst,
};
use super::value::{Head, Thunk, ThunkEntry, Val, ValInner};

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
pub fn extract_nat_val<M: MetaMode>(v: &Val<M>, prims: &Primitives<M>) -> Option<Nat> {
  match v.inner() {
    ValInner::Lit(Literal::NatVal(n)) => Some(n.clone()),
    ValInner::Ctor {
      id,
      cidx: 0,
      spine,
      ..
    } => {
      if Primitives::<M>::addr_matches(&prims.nat_zero, &id.addr) && spine.is_empty() {
        Some(Nat::from(0u64))
      } else {
        None
      }
    }
    // Handle Nat.succ constructor (cidx=1, 1 field after params)
    ValInner::Ctor {
      cidx: 1,
      induct_addr,
      num_params,
      spine,
      ..
    } => {
      if Primitives::<M>::addr_matches(&prims.nat, induct_addr)
        && spine.len() == num_params + 1
      {
        // The field is the last spine element (after params)
        let inner_thunk = &spine[spine.len() - 1];
        if let ThunkEntry::Evaluated(inner) = &*inner_thunk.entry.borrow() {
          let n = extract_nat_val(inner, prims)?;
          Some(Nat(&n.0 + 1u64))
        } else {
          None
        }
      } else {
        None
      }
    }
    ValInner::Neutral {
      head: Head::Const { id, .. },
      spine,
      ..
    } => {
      if Primitives::<M>::addr_matches(&prims.nat_zero, &id.addr) && spine.is_empty() {
        Some(Nat::from(0u64))
      } else {
        None
      }
    }
    _ => None,
  }
}

/// Check if an address is a nat primitive binary operation.
pub fn is_nat_bin_op<M: MetaMode>(addr: &Address, prims: &Primitives<M>) -> bool {
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
  .any(|p| Primitives::<M>::addr_matches(p, addr))
}

/// Check if a value is Nat.zero (constructor, neutral, or literal 0).
pub fn is_nat_zero_val<M: MetaMode>(v: &Val<M>, prims: &Primitives<M>) -> bool {
  match v.inner() {
    ValInner::Lit(Literal::NatVal(n)) => n.0 == BigUint::ZERO,
    ValInner::Neutral {
      head: Head::Const { id, .. },
      spine,
      ..
    } => Primitives::<M>::addr_matches(&prims.nat_zero, &id.addr) && spine.is_empty(),
    ValInner::Ctor { id, spine, .. } => {
      Primitives::<M>::addr_matches(&prims.nat_zero, &id.addr) && spine.is_empty()
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
  prims: &Primitives<M>,
) -> Option<Thunk<M>> {
  match v.inner() {
    ValInner::Neutral {
      head: Head::Const { id, .. },
      spine,
      ..
    } if Primitives::<M>::addr_matches(&prims.nat_succ, &id.addr) && spine.len() == 1 => {
      Some(spine[0].clone())
    }
    ValInner::Ctor { id, spine, .. }
      if Primitives::<M>::addr_matches(&prims.nat_succ, &id.addr) && spine.len() == 1 =>
    {
      Some(spine[0].clone())
    }
    _ => None,
  }
}

/// Check if an address is nat_succ.
pub fn is_nat_succ<M: MetaMode>(addr: &Address, prims: &Primitives<M>) -> bool {
  Primitives::<M>::addr_matches(&prims.nat_succ, addr)
}

/// Check if an address is nat_pred.
pub fn is_nat_pred<M: MetaMode>(addr: &Address, prims: &Primitives<M>) -> bool {
  Primitives::<M>::addr_matches(&prims.nat_pred, addr)
}

/// Check if an address is any nat primitive (unary or binary).
pub fn is_nat_prim_op<M: MetaMode>(addr: &Address, prims: &Primitives<M>) -> bool {
  is_nat_succ(addr, prims)
    || is_nat_pred(addr, prims)
    || is_nat_bin_op(addr, prims)
}

/// Compute a nat binary primitive operation.
pub fn compute_nat_prim<M: MetaMode>(
  addr: &Address,
  a: &Nat,
  b: &Nat,
  prims: &Primitives<M>,
) -> Option<Val<M>> {
  let nat_val = |n: BigUint| Val::mk_lit(Literal::NatVal(Nat(n)));
  let zero = BigUint::ZERO;

  let matches = |field: &Option<MetaId<M>>| Primitives::<M>::addr_matches(field, addr);

  let result = if matches(&prims.nat_add) {
    nat_val(&a.0 + &b.0)
  } else if matches(&prims.nat_sub) {
    nat_val(if a.0 >= b.0 { &a.0 - &b.0 } else { zero })
  } else if matches(&prims.nat_mul) {
    nat_val(&a.0 * &b.0)
  } else if matches(&prims.nat_pow) {
    // Cap exponent at 2^24 to match the Lean kernel (Helpers.lean:80-82).
    // Without this, huge exponents silently truncate via unwrap_or(0)/as u32.
    let exp = b.to_u64().filter(|&e| e <= 16_777_216)?;
    nat_val(a.0.pow(exp as u32))
  } else if matches(&prims.nat_gcd) {
    nat_val(biguint_gcd(&a.0, &b.0))
  } else if matches(&prims.nat_mod) {
    nat_val(if b.0 == zero {
      a.0.clone()
    } else {
      &a.0 % &b.0
    })
  } else if matches(&prims.nat_div) {
    nat_val(if b.0 == zero {
      zero
    } else {
      &a.0 / &b.0
    })
  } else if matches(&prims.nat_beq) {
    let b_val = if a == b {
      prims.bool_true.as_ref()?
    } else {
      prims.bool_false.as_ref()?
    };
    Val::mk_ctor(
      b_val.clone(),
      Vec::new(),
      if a == b { 1 } else { 0 },
      0,
      0,
      prims.bool_type.as_ref()?.addr.clone(),
      Vec::new(),
    )
  } else if matches(&prims.nat_ble) {
    let b_val = if a <= b {
      prims.bool_true.as_ref()?
    } else {
      prims.bool_false.as_ref()?
    };
    Val::mk_ctor(
      b_val.clone(),
      Vec::new(),
      if a <= b { 1 } else { 0 },
      0,
      0,
      prims.bool_type.as_ref()?.addr.clone(),
      Vec::new(),
    )
  } else if matches(&prims.nat_land) {
    nat_val(&a.0 & &b.0)
  } else if matches(&prims.nat_lor) {
    nat_val(&a.0 | &b.0)
  } else if matches(&prims.nat_xor) {
    nat_val(&a.0 ^ &b.0)
  } else if matches(&prims.nat_shift_left) {
    let shift = b.to_u64()?;
    nat_val(&a.0 << shift)
  } else if matches(&prims.nat_shift_right) {
    let shift = b.to_u64()?;
    nat_val(&a.0 >> shift)
  } else {
    return None;
  };
  Some(result)
}

/// Convert a Nat.zero literal to a Nat.zero constructor Val (non-thunked).
pub fn nat_lit_to_ctor_val<M: MetaMode>(
  n: &Nat,
  prims: &Primitives<M>,
) -> Option<Val<M>> {
  if n.0 == BigUint::ZERO {
    let zero_id = prims.nat_zero.as_ref()?;
    let nat_id = prims.nat.as_ref()?;
    Some(Val::mk_ctor(
      zero_id.clone(),
      Vec::new(),
      0,
      0,
      0,
      nat_id.addr.clone(),
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
  _proj_type_addr: &Address,
) -> Option<Thunk<M>> {
  match ctor.inner() {
    ValInner::Ctor {
      num_params,
      spine,
      ..
    } => {
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
      head: Head::Const { id, .. },
      ..
    } => match env.find(id)? {
      KConstantInfo::Definition(d) => Some(d.hints),
      KConstantInfo::Theorem(_) => Some(ReducibilityHints::Regular(0)),
      _ => None,
    },
    _ => None,
  }
}

/// Check if a Val is a constructor application of a structure-like inductive.
pub fn is_struct_like_app<M: MetaMode>(
  v: &Val<M>,
  typed_consts: &rustc_hash::FxHashMap<MetaId<M>, TypedConst<M>>,
  env: &KEnv<M>,
) -> bool {
  match v.inner() {
    ValInner::Ctor { induct_addr, .. } => {
      is_struct_like_app_by_addr(induct_addr, typed_consts, env)
    }
    _ => false,
  }
}

/// Check if an address corresponds to a structure-like inductive.
pub fn is_struct_like_app_by_addr<M: MetaMode>(
  addr: &Address,
  typed_consts: &rustc_hash::FxHashMap<MetaId<M>, TypedConst<M>>,
  env: &KEnv<M>,
) -> bool {
  if let Some(id) = env.get_id_by_addr(addr) {
    matches!(
      typed_consts.get(id),
      Some(TypedConst::Inductive {
        is_struct: true,
        ..
      })
    )
  } else {
    false
  }
}

/// Check if an address corresponds to a structure-like inductive using raw env
/// metadata (not typed_consts). This matches the lean4 C++ and lean4lean behavior.
pub fn is_struct_like_raw<M: MetaMode>(
  addr: &Address,
  env: &KEnv<M>,
) -> bool {
  match env.find_by_addr(addr) {
    Some(KConstantInfo::Inductive(iv)) => {
      !iv.is_rec
        && iv.num_indices == 0
        && iv.ctors.len() == 1
        && matches!(
          env.get(&iv.ctors[0]),
          Some(KConstantInfo::Constructor(_))
        )
    }
    _ => false,
  }
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
) -> Option<MetaId<M>> {
  let total = num_params + num_motives + num_minors + num_indices;
  fn go<M: MetaMode>(
    ty: &KExpr<M>,
    remaining: usize,
  ) -> Option<MetaId<M>> {
    match remaining {
      0 => match ty.data() {
        KExprData::ForallE(dom, _, _, _) => {
          dom.get_app_fn().const_id().cloned()
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
    KExprData::Const(id, _) => id.addr == *addr,
    KExprData::App(f, a) => {
      expr_mentions_const(f, addr)
        || expr_mentions_const(a, addr)
    }
    KExprData::Lam(ty, body, _, _)
    | KExprData::ForallE(ty, body, _, _) => {
      expr_mentions_const(ty, addr)
        || expr_mentions_const(body, addr)
    }
    KExprData::LetE(ty, val, body, _, _) => {
      expr_mentions_const(ty, addr)
        || expr_mentions_const(val, addr)
        || expr_mentions_const(body, addr)
    }
    KExprData::Proj(_, _, s) => expr_mentions_const(s, addr),
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

/// Get the head constant of a ForallE chain's last domain (the target type).
/// For `∀ (idx...) (x : T args), Sort v`, returns the address of T.
pub fn get_forall_target_head<M: MetaMode>(
  ty: &KExpr<M>,
) -> Option<Address> {
  let mut last_dom = None;
  let mut t = ty.clone();
  loop {
    match t.data() {
      KExprData::ForallE(dom, body, _, _) => {
        last_dom = Some(dom.clone());
        t = body.clone();
      }
      _ => break,
    }
  }
  last_dom.and_then(|dom| dom.get_app_fn().const_id().map(|id| id.addr.clone()))
}

/// Get the head constant of a constructor's return type.
/// Peels `num_params + num_fields` Pi binders, then returns the head.
pub fn get_ctor_return_head<M: MetaMode>(
  ty: &KExpr<M>,
  num_params: usize,
  num_fields: usize,
) -> Option<Address> {
  let ret = get_ctor_return_type(ty, num_params, num_fields);
  ret.get_app_fn().const_id().map(|id| id.addr.clone())
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
    KExprData::LetE(ty, val, body, name, nd) => KExpr::let_e_nd(
      lift_go(ty, n, d),
      lift_go(val, n, d),
      lift_go(body, n, d + 1),
      name.clone(),
      *nd,
    ),
    KExprData::Proj(id, idx, s) => {
      KExpr::proj(id.clone(), *idx, lift_go(s, n, d))
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
    KExprData::LetE(ty, val, body, n, nd) => KExpr::let_e_nd(
      shift_go(ty, field_depth, bvar_shift, level_subst, depth),
      shift_go(val, field_depth, bvar_shift, level_subst, depth),
      shift_go(body, field_depth, bvar_shift, level_subst, depth + 1),
      n.clone(),
      *nd,
    ),
    KExprData::Proj(id, idx, s) => KExpr::proj(
      id.clone(),
      *idx,
      shift_go(s, field_depth, bvar_shift, level_subst, depth),
    ),
    KExprData::Sort(l) => {
      KExpr::sort(subst_level(l, level_subst))
    }
    KExprData::Const(id, lvls) => {
      if level_subst.is_empty() {
        e.clone()
      } else {
        let new_lvls: Vec<_> =
          lvls.iter().map(|l| subst_level(l, level_subst)).collect();
        KExpr::cnst(id.clone(), new_lvls)
      }
    }
    KExprData::Lit(_) => e.clone(),
  }
}

/// Substitute ALL param bvars in a nested constructor body expression.
///
/// After peeling `cnp` params from the ctor type, param bvars occupy
/// indices `field_depth..field_depth+num_params-1` at depth 0 (in reverse
/// order: BVar(field_depth) = last param, BVar(field_depth+num_params-1)
/// = first param). Replaces them with `vals` (in order: vals[0] = first
/// param's value from major premise).
pub fn subst_all_params<M: MetaMode>(
  e: &KExpr<M>,
  field_depth: usize,
  num_params: usize,
  vals: &[KExpr<M>],
) -> KExpr<M> {
  if num_params == 0 {
    return e.clone();
  }
  subst_ap_go(e, field_depth, num_params, vals, 0)
}

fn subst_ap_go<M: MetaMode>(
  e: &KExpr<M>,
  field_depth: usize,
  num_params: usize,
  vals: &[KExpr<M>],
  depth: usize,
) -> KExpr<M> {
  match e.data() {
    KExprData::BVar(i, n) => {
      if *i < depth + field_depth {
        // Bound by field/local binder — keep
        e.clone()
      } else {
        let param_idx = i - (depth + field_depth);
        if param_idx < num_params {
          // Param bvar: substitute with vals[num_params - 1 - param_idx]
          // (BVar(field_depth) = last param = vals[num_params-1], etc.)
          let val_idx = num_params - 1 - param_idx;
          if val_idx < vals.len() {
            shift_ctor_to_rule(&vals[val_idx], 0, depth, &[])
          } else {
            e.clone()
          }
        } else {
          // Beyond params: shift down by num_params
          KExpr::bvar(i - num_params, n.clone())
        }
      }
    }
    KExprData::App(f, a) => KExpr::app(
      subst_ap_go(f, field_depth, num_params, vals, depth),
      subst_ap_go(a, field_depth, num_params, vals, depth),
    ),
    KExprData::Lam(ty, body, n, bi) => KExpr::lam(
      subst_ap_go(ty, field_depth, num_params, vals, depth),
      subst_ap_go(body, field_depth, num_params, vals, depth + 1),
      n.clone(),
      bi.clone(),
    ),
    KExprData::ForallE(ty, body, n, bi) => KExpr::forall_e(
      subst_ap_go(ty, field_depth, num_params, vals, depth),
      subst_ap_go(body, field_depth, num_params, vals, depth + 1),
      n.clone(),
      bi.clone(),
    ),
    KExprData::LetE(ty, val, body, n, nd) => KExpr::let_e_nd(
      subst_ap_go(ty, field_depth, num_params, vals, depth),
      subst_ap_go(val, field_depth, num_params, vals, depth),
      subst_ap_go(body, field_depth, num_params, vals, depth + 1),
      n.clone(),
      *nd,
    ),
    KExprData::Proj(id, idx, s) => KExpr::proj(
      id.clone(),
      *idx,
      subst_ap_go(s, field_depth, num_params, vals, depth),
    ),
    _ => e.clone(),
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
    KExprData::LetE(ty, val, body, n, nd) => KExpr::let_e_nd(
      subst_np_go(ty, field_depth, num_extra, vals, depth),
      subst_np_go(val, field_depth, num_extra, vals, depth),
      subst_np_go(body, field_depth, num_extra, vals, depth + 1),
      n.clone(),
      *nd,
    ),
    KExprData::Proj(id, idx, s) => KExpr::proj(
      id.clone(),
      *idx,
      subst_np_go(s, field_depth, num_extra, vals, depth),
    ),
    _ => e.clone(),
  }
}
