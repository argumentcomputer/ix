//! `.recOn` generation: reorders `.rec` arguments.
//!
//! `.rec` binder order:   params, motives, minors, indices, major
//! `.recOn` binder order: params, motives, indices, major, minors
//!
//! Follows `refs/lean4/src/Lean/Meta/Constructions/RecOn.lean`.

use crate::ix::compile::aux_gen::AuxDef;
use crate::ix::env::{
  BinderInfo, Expr as LeanExpr, ExprData, Level, Name,
  RecursorVal,
};
use lean_ffi::nat::Nat;

/// Generate a `.recOn` definition from a canonical `.rec`.
///
/// Returns `None` if the recursor type cannot be decomposed.
pub(crate) fn _generate_rec_on(name: &Name, rec_val: &RecursorVal) -> Option<AuxDef> {
  let n_params = rec_val.num_params.to_u64()? as usize;
  let n_motives = rec_val.num_motives.to_u64()? as usize;
  let n_minors = rec_val.num_minors.to_u64()? as usize;
  let n_indices = rec_val.num_indices.to_u64()? as usize;
  let n_major = 1usize;

  let ac_size = n_params + n_motives; // params + motives (kept in place)
  let total = ac_size + n_minors + n_indices + n_major;

  // Collect all binders from the rec type.
  let mut binders: Vec<(Name, LeanExpr, BinderInfo)> =
    Vec::with_capacity(total);
  let mut cur = rec_val.cnst.typ.clone();
  for _ in 0..total {
    match cur.as_data() {
      ExprData::ForallE(bname, dom, body, bi, _) => {
        binders.push((bname.clone(), dom.clone(), bi.clone()));
        cur = body.clone();
      },
      _ => return None,
    }
  }
  let return_type = cur; // the body after all binders

  // The new binder order is:
  //   [0..ac_size)                                    = params + motives (same)
  //   [ac_size..ac_size+n_indices+n_major)            = indices + major (moved up)
  //   [ac_size+n_indices+n_major..total)              = minors (moved down)
  //
  // Build a permutation: new_order[new_pos] = old_pos
  let mut new_order: Vec<usize> = Vec::with_capacity(total);
  // params + motives
  for i in 0..ac_size {
    new_order.push(i);
  }
  // indices + major (were at old positions ac_size+n_minors .. total)
  for i in (ac_size + n_minors)..(ac_size + n_minors + n_indices + n_major) {
    new_order.push(i);
  }
  // minors (were at old positions ac_size .. ac_size+n_minors)
  for i in ac_size..(ac_size + n_minors) {
    new_order.push(i);
  }

  // Build inverse permutation: inv_perm[old_pos] = new_pos
  let mut inv_perm = vec![0usize; total];
  for (new_pos, &old_pos) in new_order.iter().enumerate() {
    inv_perm[old_pos] = new_pos;
  }

  // Build the new type: ∀ (reordered binders), return_type[permuted BVars]
  // In the rec type, BVar(0) is the innermost (major), BVar(total-1) is the outermost (first param).
  // After reordering, a binder that was at old_pos now has BVar(total - 1 - new_pos).
  //
  // For each BVar(k) in the original type where k < total:
  //   old_pos = total - 1 - k
  //   new_pos = inv_perm[old_pos]
  //   new_bvar = total - 1 - new_pos

  // Permute BVars in an expression (only free vars, i.e., index >= cutoff).
  let permute = |expr: &LeanExpr, cutoff: usize| -> LeanExpr {
    permute_bvars(expr, &inv_perm, total, cutoff)
  };

  // Build the recOn type with reordered binders.
  let mut rec_on_type = permute(&return_type, 0);
  for i in (0..total).rev() {
    let old_pos = new_order[i];
    let (ref bname, ref dom, ref bi) = binders[old_pos];
    // The domain needs to be permuted with cutoff = total - 1 - old_pos
    // (the number of binders that were INSIDE this one in the original).
    // But we're building from inside-out, and the domain at old_pos had
    // (total - 1 - old_pos) binders below it. After permutation, we need
    // the domain to reference the new positions.
    let _cutoff = total - 1 - old_pos;
    let new_dom =
      permute_bvars_reorder(dom, &new_order, &inv_perm, total, old_pos);
    rec_on_type =
      LeanExpr::all(bname.clone(), new_dom, rec_on_type, bi.clone());
  }

  // Build the recOn value: λ (reordered binders), rec (original-order binders)
  // The value applies rec to args in the ORIGINAL order.
  // In the lambda body (depth = total), each original binder at old_pos
  // is now at new_pos = inv_perm[old_pos], so it's BVar(total - 1 - new_pos).
  let rec_const = LeanExpr::cnst(
    rec_val.cnst.name.clone(),
    rec_val.cnst.level_params.iter().map(|n| Level::param(n.clone())).collect(),
  );
  let mut rec_app = rec_const;
  for &new_pos in inv_perm.iter().take(total) {
    let bvar_idx = (total - 1 - new_pos) as u64;
    rec_app = LeanExpr::app(rec_app, LeanExpr::bvar(Nat::from(bvar_idx)));
  }

  let mut rec_on_value = rec_app;
  for i in (0..total).rev() {
    let old_pos = new_order[i];
    let (ref bname, ref dom, ref bi) = binders[old_pos];
    let new_dom =
      permute_bvars_reorder(dom, &new_order, &inv_perm, total, old_pos);
    rec_on_value =
      LeanExpr::lam(bname.clone(), new_dom, rec_on_value, bi.clone());
  }

  Some(AuxDef {
    name: name.clone(),
    level_params: rec_val.cnst.level_params.clone(),
    typ: rec_on_type,
    value: rec_on_value,
  })
}

/// Permute free BVars in an expression.
///
/// For a BVar(k) where k >= cutoff (free relative to cutoff):
///   old_pos = total - 1 - (k - cutoff)  [which original binder it refers to]
///   new_pos = inv_perm[old_pos]
///   new_k = cutoff + (total - 1 - new_pos)
#[allow(dead_code)]
pub(crate) fn permute_bvars(
  expr: &LeanExpr,
  inv_perm: &[usize],
  total: usize,
  cutoff: usize,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Bvar(idx, _) => {
      let k = idx.to_u64().unwrap_or(0) as usize;
      if k >= cutoff && (k - cutoff) < total {
        let old_pos = total - 1 - (k - cutoff);
        if old_pos < inv_perm.len() {
          let new_pos = inv_perm[old_pos];
          let new_k = cutoff + total - 1 - new_pos;
          LeanExpr::bvar(Nat::from(new_k as u64))
        } else {
          expr.clone()
        }
      } else {
        expr.clone()
      }
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      permute_bvars(f, inv_perm, total, cutoff),
      permute_bvars(a, inv_perm, total, cutoff),
    ),
    ExprData::Lam(name, dom, body, bi, _) => LeanExpr::lam(
      name.clone(),
      permute_bvars(dom, inv_perm, total, cutoff),
      permute_bvars(body, inv_perm, total, cutoff + 1),
      bi.clone(),
    ),
    ExprData::ForallE(name, dom, body, bi, _) => LeanExpr::all(
      name.clone(),
      permute_bvars(dom, inv_perm, total, cutoff),
      permute_bvars(body, inv_perm, total, cutoff + 1),
      bi.clone(),
    ),
    ExprData::LetE(name, ty, val, body, nd, _) => LeanExpr::letE(
      name.clone(),
      permute_bvars(ty, inv_perm, total, cutoff),
      permute_bvars(val, inv_perm, total, cutoff),
      permute_bvars(body, inv_perm, total, cutoff + 1),
      *nd,
    ),
    ExprData::Sort(..)
    | ExprData::Const(..)
    | ExprData::Fvar(..)
    | ExprData::Mvar(..)
    | ExprData::Lit(..) => expr.clone(),
    ExprData::Mdata(kv, inner, _) => {
      LeanExpr::mdata(kv.clone(), permute_bvars(inner, inv_perm, total, cutoff))
    },
    ExprData::Proj(name, idx, s, _) => LeanExpr::proj(
      name.clone(),
      idx.clone(),
      permute_bvars(s, inv_perm, total, cutoff),
    ),
  }
}

/// Permute BVars in a binder domain from the original rec type.
///
/// The domain at `old_pos` in the original rec type has `total - 1 - old_pos`
/// binders below it. We need to remap those free BVars to the new positions.
#[allow(dead_code)]
fn permute_bvars_reorder(
  dom: &LeanExpr,
  _new_order: &[usize],
  inv_perm: &[usize],
  total: usize,
  old_pos: usize,
) -> LeanExpr {
  // In the original type, the domain at old_pos sees binders at positions
  // (old_pos+1)..total as free BVars (BVar(0) = old_pos+1, etc.).
  // After reordering, we need to remap these.
  //
  // Free BVar(k) in the original domain means it refers to old_pos_ref = old_pos + 1 + k.
  // In the new layout, that binder is at new_pos = inv_perm[old_pos_ref].
  // The new BVar index relative to the current position (new_pos_self = inv_perm[old_pos])
  // needs to account for the new ordering.
  //
  // Since we're building the type from inside-out with the new binder order,
  // a binder at new position j sees binders at new positions (j+1)..total below it.
  // If old_pos_ref maps to new_pos_ref, the BVar in the new type is:
  //   (total - 1 - new_pos_ref) relative to the bottom,
  //   but relative to the current position at new_pos_self:
  //   we need (new_pos_self - new_pos_ref - 1) if new_pos_ref < new_pos_self
  //   but this gets complicated. Use the simpler approach:
  //
  // The domain will be placed under (total - 1 - inv_perm[old_pos]) binders
  // in the final type. Free BVar(k) refers to old position old_pos + 1 + k.
  // In the final type, that position is at depth (total - 1 - inv_perm[old_pos + 1 + k]).
  // But the domain itself is at depth (total - 1 - inv_perm[old_pos]).
  // So the relative BVar should be: depth_ref - depth_self - 1... no, this is
  // getting wrong.
  //
  // Actually, let's use the general permute_bvars with cutoff=0 since the domain
  // in the original type has (total - 1 - old_pos) free variables which are exactly
  // the binders at positions old_pos+1..total. These map via inv_perm.
  let _n_free = total - 1 - old_pos; // number of binders INSIDE this one
  permute_bvars(dom, inv_perm, total, 0)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::ConstantVal;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  /// Test recOn generation for a simple Prop inductive: `inductive P : Prop | mk`
  /// rec  : ∀ {motive : P → Prop} (mk : motive P.mk) (t : P), motive t
  /// recOn: ∀ {motive : P → Prop} (t : P) (mk : motive P.mk), motive t
  #[test]
  fn test_rec_on_simple() {
    // Build P.rec type: ∀ {motive : P → Prop} (mk : motive P.mk) (t : P), motive t
    // Using de Bruijn:
    //   motive  = BVar(2) in the body
    //   mk      = BVar(1) in the body
    //   t       = BVar(0) in the body
    //
    // P = Const("P", [])
    let p = LeanExpr::cnst(mk_name("P"), vec![]);
    let prop = LeanExpr::sort(Level::zero());

    // motive type: P → Prop
    let motive_ty =
      LeanExpr::all(mk_name("t"), p.clone(), prop.clone(), BinderInfo::Default);

    // mk type (minor): motive P.mk
    // Under 1 binder (motive), P.mk = Const("P.mk", []), motive = BVar(0)
    let p_mk = LeanExpr::cnst(mk_name("P.mk"), vec![]);
    let mk_ty = LeanExpr::app(LeanExpr::bvar(Nat::from(0u64)), p_mk.clone());

    // major type: P (no BVars needed since P is a constant)
    let major_ty = p.clone();

    // return: motive t = BVar(2) applied to BVar(0)
    let ret = LeanExpr::app(
      LeanExpr::bvar(Nat::from(2u64)),
      LeanExpr::bvar(Nat::from(0u64)),
    );

    // rec type: ∀ {motive : P → Prop} (mk : motive P.mk) (t : P), motive t
    let rec_type = LeanExpr::all(
      mk_name("motive"),
      motive_ty,
      LeanExpr::all(
        mk_name("mk"),
        mk_ty,
        LeanExpr::all(mk_name("t"), major_ty, ret, BinderInfo::Default),
        BinderInfo::Default,
      ),
      BinderInfo::Implicit,
    );

    let rec_val = RecursorVal {
      cnst: ConstantVal {
        name: mk_name("P.rec"),
        level_params: vec![],
        typ: rec_type,
      },
      all: vec![mk_name("P")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![],
      k: true,
      is_unsafe: false,
    };

    let rec_on = _generate_rec_on(&mk_name("P.recOn"), &rec_val)
      .expect("should generate recOn");

    assert_eq!(rec_on.name, mk_name("P.recOn"));

    // recOn type should be: ∀ {motive : P → Prop} (t : P) (mk : motive P.mk), motive t
    // The minors (mk) are moved after indices+major (t).
    // Verify the type has the right binder structure.
    let mut ty = rec_on.typ.clone();
    // First binder: {motive : P → Prop}
    if let ExprData::ForallE(name, _, body, bi, _) = ty.as_data() {
      assert_eq!(name.pretty(), "motive");
      assert_eq!(*bi, BinderInfo::Implicit);
      ty = body.clone();
    } else {
      panic!("expected forall for motive");
    }
    // Second binder: (t : P) — moved from position 2 to position 1
    if let ExprData::ForallE(name, _, body, bi, _) = ty.as_data() {
      assert_eq!(name.pretty(), "t");
      assert_eq!(*bi, BinderInfo::Default);
      ty = body.clone();
    } else {
      panic!("expected forall for t (major)");
    }
    // Third binder: (mk : motive P.mk) — moved from position 1 to position 2
    if let ExprData::ForallE(name, _, _, bi, _) = ty.as_data() {
      assert_eq!(name.pretty(), "mk");
      assert_eq!(*bi, BinderInfo::Default);
    } else {
      panic!("expected forall for mk (minor)");
    }
  }
}
