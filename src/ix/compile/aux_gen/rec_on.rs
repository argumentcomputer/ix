//! `.recOn` generation: reorders `.rec` arguments.
//!
//! `.rec` binder order:   params, motives, minors, indices, major
//! `.recOn` binder order: params, motives, indices, major, minors
//!
//! Uses FVar-based construction: open all rec binders into FVars, reorder
//! the FVar/declaration arrays, then close back with mk_forall/mk_lambda.
//! Follows `refs/lean4/src/Lean/Meta/Constructions/RecOn.lean`.

use crate::ix::compile::aux_gen::AuxDef;
use crate::ix::env::{Level, Name, RecursorVal};

use super::expr_utils::{
  forall_telescope, mk_app_n, mk_const, mk_forall, mk_lambda,
};

/// Generate a `.recOn` definition from a canonical `.rec`.
///
/// Returns `None` if the recursor type cannot be decomposed.
pub(crate) fn generate_rec_on(
  name: &Name,
  rec_val: &RecursorVal,
) -> Option<AuxDef> {
  let n_params = rec_val.num_params.to_u64()? as usize;
  let n_motives = rec_val.num_motives.to_u64()? as usize;
  let n_minors = rec_val.num_minors.to_u64()? as usize;
  let n_indices = rec_val.num_indices.to_u64()? as usize;

  let ac_size = n_params + n_motives; // params + motives (kept in place)
  let total = ac_size + n_minors + n_indices + 1;

  // Open all foralls into FVars (equivalent to Lean's forallTelescope).
  let (fvars, decls, body) =
    forall_telescope(&rec_val.cnst.typ, total, "ro", 0);
  if fvars.len() < total {
    return None;
  }

  // Build rec application: rec fvar[0] fvar[1] ... fvar[n-1] (original order).
  let rec_univs: Vec<Level> = rec_val
    .cnst
    .level_params
    .iter()
    .map(|lp| Level::param(lp.clone()))
    .collect();
  let rec_app = mk_app_n(mk_const(&rec_val.cnst.name, &rec_univs), &fvars);

  // Reorder declarations and FVars:
  //   before: [params, motives, minors, indices, major]
  //   after:  [params, motives, indices, major, minors]
  //
  // This matches RecOn.lean lines 25-29:
  //   vs = xs[*...AC_size]
  //     ++ xs[(AC_size + numMinors) ... (AC_size + numMinors + 1 + numIndices)]
  //     ++ xs[AC_size ... (AC_size + numMinors)]
  let mut reordered = Vec::with_capacity(total);
  reordered.extend_from_slice(&decls[..ac_size]);
  reordered.extend_from_slice(&decls[(ac_size + n_minors)..total]);
  reordered.extend_from_slice(&decls[ac_size..(ac_size + n_minors)]);

  // Close back into BVar form with reordered binders.
  // mk_forall/mk_lambda handle all de Bruijn index calculation automatically.
  let rec_on_type = mk_forall(body, &reordered);
  let rec_on_value = mk_lambda(rec_app, &reordered);

  Some(AuxDef {
    name: name.clone(),
    level_params: rec_val.cnst.level_params.clone(),
    typ: rec_on_type,
    value: rec_on_value,
    // `.recOn` mirrors the recursor's safety — Lean builds it via
    // `mkDefinitionValInferringUnsafe` (`Lean/Meta/Constructions/RecOn.lean:32`)
    // and the inferred safety matches the parent inductive since the value
    // references the inductive's `.rec`.
    is_unsafe: rec_val.is_unsafe,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{BinderInfo, ConstantVal, Expr as LeanExpr, ExprData};
  use lean_ffi::nat::Nat;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  /// Test recOn generation for a simple Prop inductive: `inductive P : Prop | mk`
  /// rec  : ∀ {motive : P → Prop} (mk : motive P.mk) (t : P), motive t
  /// recOn: ∀ {motive : P → Prop} (t : P) (mk : motive P.mk), motive t
  #[test]
  fn test_rec_on_simple() {
    let p = LeanExpr::cnst(mk_name("P"), vec![]);
    let prop = LeanExpr::sort(Level::zero());

    // motive type: P → Prop
    let motive_ty =
      LeanExpr::all(mk_name("t"), p.clone(), prop.clone(), BinderInfo::Default);

    // mk type (minor): motive P.mk  (under 1 binder: motive = BVar(0))
    let p_mk = LeanExpr::cnst(mk_name("P.mk"), vec![]);
    let mk_ty = LeanExpr::app(LeanExpr::bvar(Nat::from(0u64)), p_mk);

    // major type: P
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

    let rec_on = generate_rec_on(&mk_name("P.recOn"), &rec_val)
      .expect("should generate recOn");

    assert_eq!(rec_on.name, mk_name("P.recOn"));

    // recOn type should be: ∀ {motive : P → Prop} (t : P) (mk : motive P.mk), motive t
    // The minors (mk) are moved after indices+major (t).
    let mut ty = rec_on.typ.clone();

    // First binder: {motive : P → Prop}
    if let ExprData::ForallE(name, _, body, bi, _) = ty.as_data() {
      assert_eq!(name.pretty(), "motive");
      assert!(matches!(bi, BinderInfo::Implicit));
      ty = body.clone();
    } else {
      panic!("expected forall for motive");
    }

    // Second binder: (t : P) — moved from position 2 to position 1
    if let ExprData::ForallE(name, _, body, bi, _) = ty.as_data() {
      assert_eq!(name.pretty(), "t");
      assert!(matches!(bi, BinderInfo::Default));
      ty = body.clone();
    } else {
      panic!("expected forall for t (major)");
    }

    // Third binder: (mk : motive P.mk) — moved from position 1 to position 2
    if let ExprData::ForallE(name, _, _, bi, _) = ty.as_data() {
      assert_eq!(name.pretty(), "mk");
      assert!(matches!(bi, BinderInfo::Default));
    } else {
      panic!("expected forall for mk (minor)");
    }
  }

  /// Count the number of leading forall binders.
  fn count_leading_foralls(e: &LeanExpr) -> usize {
    let mut n = 0;
    let mut cur = e.clone();
    while let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      n += 1;
      cur = body.clone();
    }
    n
  }

  /// Collect the ordered list of binder names.
  fn binder_names(e: &LeanExpr) -> Vec<String> {
    let mut names = Vec::new();
    let mut cur = e.clone();
    while let ExprData::ForallE(name, _, body, _, _) = cur.as_data() {
      names.push(name.pretty());
      cur = body.clone();
    }
    names
  }

  /// Collect the ordered list of lambda binder names in the value.
  fn lambda_binder_names(e: &LeanExpr) -> Vec<String> {
    let mut names = Vec::new();
    let mut cur = e.clone();
    while let ExprData::Lam(name, _, body, _, _) = cur.as_data() {
      names.push(name.pretty());
      cur = body.clone();
    }
    names
  }

  #[test]
  fn rec_on_value_and_type_have_same_arity() {
    let p = LeanExpr::cnst(mk_name("P"), vec![]);
    let prop = LeanExpr::sort(Level::zero());
    let motive_ty =
      LeanExpr::all(mk_name("t"), p.clone(), prop.clone(), BinderInfo::Default);
    let mk_ty = LeanExpr::app(
      LeanExpr::bvar(Nat::from(0u64)),
      LeanExpr::cnst(mk_name("P.mk"), vec![]),
    );
    let ret = LeanExpr::app(
      LeanExpr::bvar(Nat::from(2u64)),
      LeanExpr::bvar(Nat::from(0u64)),
    );
    let rec_type = LeanExpr::all(
      mk_name("motive"),
      motive_ty,
      LeanExpr::all(
        mk_name("mk"),
        mk_ty,
        LeanExpr::all(mk_name("t"), p, ret, BinderInfo::Default),
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
    let rec_on = generate_rec_on(&mk_name("P.recOn"), &rec_val).unwrap();
    let type_arity = count_leading_foralls(&rec_on.typ);
    let value_arity = lambda_binder_names(&rec_on.value).len();
    assert_eq!(
      type_arity, value_arity,
      "recOn type and value must have the same leading binder count"
    );
  }

  #[test]
  fn rec_on_preserves_recursor_level_params() {
    // `.recOn`'s level_params must match the parent `.rec`.
    let rec_val = RecursorVal {
      cnst: ConstantVal {
        name: mk_name("T.rec"),
        level_params: vec![mk_name("u"), mk_name("v")],
        typ: LeanExpr::all(
          mk_name("motive"),
          LeanExpr::sort(Level::zero()),
          LeanExpr::all(
            mk_name("mk"),
            LeanExpr::bvar(Nat::from(0u64)),
            LeanExpr::all(
              mk_name("t"),
              LeanExpr::cnst(mk_name("T"), vec![]),
              LeanExpr::bvar(Nat::from(2u64)),
              BinderInfo::Default,
            ),
            BinderInfo::Default,
          ),
          BinderInfo::Implicit,
        ),
      },
      all: vec![mk_name("T")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    };
    let rec_on = generate_rec_on(&mk_name("T.recOn"), &rec_val).unwrap();
    assert_eq!(rec_on.level_params, vec![mk_name("u"), mk_name("v")]);
  }

  #[test]
  fn rec_on_preserves_is_unsafe_bit() {
    let mut rec_val = RecursorVal {
      cnst: ConstantVal {
        name: mk_name("T.rec"),
        level_params: vec![],
        typ: LeanExpr::all(
          mk_name("motive"),
          LeanExpr::sort(Level::zero()),
          LeanExpr::all(
            mk_name("mk"),
            LeanExpr::bvar(Nat::from(0u64)),
            LeanExpr::all(
              mk_name("t"),
              LeanExpr::cnst(mk_name("T"), vec![]),
              LeanExpr::bvar(Nat::from(2u64)),
              BinderInfo::Default,
            ),
            BinderInfo::Default,
          ),
          BinderInfo::Implicit,
        ),
      },
      all: vec![mk_name("T")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    };
    let safe_recon = generate_rec_on(&mk_name("T.recOn"), &rec_val).unwrap();
    assert!(!safe_recon.is_unsafe);

    rec_val.is_unsafe = true;
    let unsafe_recon = generate_rec_on(&mk_name("T.recOn"), &rec_val).unwrap();
    assert!(unsafe_recon.is_unsafe);
  }

  /// Recursor whose type has too few foralls to match the declared
  /// counts → `None` return.
  #[test]
  fn rec_on_insufficient_foralls_returns_none() {
    let rec_val = RecursorVal {
      cnst: ConstantVal {
        name: mk_name("T.rec"),
        level_params: vec![],
        typ: LeanExpr::sort(Level::zero()), // no binders at all
      },
      all: vec![mk_name("T")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(1u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    };
    assert!(generate_rec_on(&mk_name("T.recOn"), &rec_val).is_none());
  }

  #[test]
  fn rec_on_reorders_minors_after_major() {
    // 2-ctor Prop inductive:
    //   inductive T : Prop | A | B
    // rec:   ∀ {motive} (a : motive T.A) (b : motive T.B) (t : T), motive t
    // recOn: ∀ {motive} (t : T) (a : motive T.A) (b : motive T.B), motive t
    let t = LeanExpr::cnst(mk_name("T"), vec![]);
    let prop = LeanExpr::sort(Level::zero());
    let motive_ty =
      LeanExpr::all(mk_name("t"), t.clone(), prop.clone(), BinderInfo::Default);

    // Minor a: motive T.A (motive is BVar(0) at the a-binder position)
    let minor_a = LeanExpr::app(
      LeanExpr::bvar(Nat::from(0u64)),
      LeanExpr::cnst(mk_name("T.A"), vec![]),
    );
    // Minor b: motive T.B (under a, motive is BVar(1))
    let minor_b = LeanExpr::app(
      LeanExpr::bvar(Nat::from(1u64)),
      LeanExpr::cnst(mk_name("T.B"), vec![]),
    );
    // return: motive t  (motive is BVar(3), t is BVar(0))
    let ret = LeanExpr::app(
      LeanExpr::bvar(Nat::from(3u64)),
      LeanExpr::bvar(Nat::from(0u64)),
    );
    let rec_type = LeanExpr::all(
      mk_name("motive"),
      motive_ty,
      LeanExpr::all(
        mk_name("a"),
        minor_a,
        LeanExpr::all(
          mk_name("b"),
          minor_b,
          LeanExpr::all(mk_name("t"), t.clone(), ret, BinderInfo::Default),
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      ),
      BinderInfo::Implicit,
    );

    let rec_val = RecursorVal {
      cnst: ConstantVal {
        name: mk_name("T.rec"),
        level_params: vec![],
        typ: rec_type,
      },
      all: vec![mk_name("T")],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(2u64),
      rules: vec![],
      k: false,
      is_unsafe: false,
    };

    let rec_on = generate_rec_on(&mk_name("T.recOn"), &rec_val).unwrap();
    let names = binder_names(&rec_on.typ);
    // Expected recOn order: [motive, t, a, b]
    assert_eq!(names, vec!["motive", "t", "a", "b"]);
  }
}
