//! Good and bad inductive type tests.

#[cfg(test)]
mod tests {
  use crate::ix::env::{Name, ReducibilityHints};
  use crate::ix::kernel::constant::{KConst, RecRule};
  use crate::ix::kernel::env::KEnv;
  use crate::ix::kernel::mode::Meta;
  use crate::ix::kernel::testing::*;

  // ==========================================================================
  // Batch 3: Bad inductives (Tutorial.lean lines 247–610)
  // ==========================================================================

  /// Helper: build an inductive with no ctors, no recursor, just checking the type
  fn mk_simple_indc(
    env: &mut KEnv<Meta>,
    name: &str,
    lvls: u64,
    level_params: &[Name],
    ty: &ME,
  ) -> MId {
    let block_id = mk_id(name);
    let rec_name = &format!("{name}.rec");
    let rec_id = mk_id(rec_name);
    // Inductive
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(name),
        level_params: level_params.to_owned(),
        lvls,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: ty.clone(),
        ctors: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    // Dummy recursor (check_inductive needs one in the block)
    let mut rec_lvl_params = vec![mk_name("u_rec")];
    rec_lvl_params.extend(level_params.to_owned());
    let rec_ty = npi(
      "motive",
      pi(cnst(name, &[]), sort(param(0))),
      npi("t", cnst(name, &[]), app(var(1), var(0))),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(rec_name),
        level_params: rec_lvl_params,
        k: false,
        is_unsafe: false,
        lvls: lvls + 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env.blocks.insert(block_id.clone(), vec![block_id.clone(), rec_id]);
    block_id
  }

  /// inductBadNonSort: inductive with type = constType (not a Sort)
  #[test]
  fn bad_induct_non_sort_type() {
    let mut env = KEnv::<Meta>::new();
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);

    let id = mk_simple_indc(
      &mut env,
      "inductBadNonSort",
      0,
      &[],
      &cnst("constType", &[]), // not a Sort!
    );
    check_rejects(&env, &id);
  }

  /// inductBadNonSort2: inductive with type = aType (axiom, not a Sort)
  #[test]
  fn bad_induct_non_sort_type2() {
    let mut env = KEnv::<Meta>::new();
    let (at_id, at_c) = mk_axiom("aType", 0, vec![], sort1());
    env.insert(at_id, at_c);

    let id = mk_simple_indc(
      &mut env,
      "inductBadNonSort2",
      0,
      &[],
      &cnst("aType", &[]), // aType : Type, but aType itself is not a Sort
    );
    check_rejects(&env, &id);
  }

  /// inductTooFewParams: claims numParams=2 but type only has 1 arrow
  #[test]
  fn bad_induct_too_few_params() {
    let env = KEnv::<Meta>::new();
    let block_id = mk_id("inductTooFewParams");
    let rec_id = mk_id("inductTooFewParams.rec");
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name("inductTooFewParams"),
        level_params: vec![],
        lvls: 0,
        params: 2, // claims 2 params
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: pi(sort0(), sort0()), // only 1 arrow — Prop → Prop
        ctors: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    // Minimal recursor
    let rec_ty = npi(
      "motive",
      pi(pi(sort0(), sort0()), sort(param(0))),
      npi("t", pi(sort0(), sort0()), app(var(1), var(0))),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name("inductTooFewParams.rec"),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 2,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env.blocks.insert(block_id.clone(), vec![block_id.clone(), rec_id]);
    check_rejects(&env, &block_id);
  }

  /// indNeg: classic negative recursive occurrence: (I → I) → I
  #[test]
  fn bad_induct_negative_occurrence() {
    let env = KEnv::<Meta>::new();
    let n = "indNeg";
    let block_id = mk_id(n);
    let ctor_id = mk_id("indNeg.mk");
    let rec_id = mk_id("indNeg.rec");

    // indNeg : Type
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // indNeg.mk : (indNeg → indNeg) → indNeg
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name("indNeg.mk"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: pi(pi(cnst(n, &[]), cnst(n, &[])), cnst(n, &[])),
      },
    );

    // Dummy recursor
    let motive_ty = pi(cnst(n, &[]), sort(param(0)));
    let minor = npi(
      "f",
      pi(cnst(n, &[]), cnst(n, &[])),
      app(var(1), app(var(0), var(0))),
    );
    let rec_ty = npi(
      "motive",
      motive_ty,
      npi("mk", minor, npi("t", cnst(n, &[]), app(var(2), var(0)))),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name("indNeg.rec"),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  /// typeWithTooHighTypeField: inductive Type 1 with a field of Type 1 (too high)
  #[test]
  fn bad_induct_too_high_field() {
    let env = KEnv::<Meta>::new();
    let n = "typeWithTooHighTypeField";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // typeWithTooHighTypeField : Sort 1 = Type
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(), // Type = Sort 1
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // .mk : Sort 1 → typeWithTooHighTypeField
    // Field of type Sort 1 = Type, but inductive is in Sort 1 = Type.
    // Fields must be < Sort level of inductive, so Type (Sort 1) is too high for Type inductive.
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: pi(sort1(), cnst(n, &[])), // Sort 1 → I
      },
    );

    // Dummy recursor
    let motive_ty = pi(cnst(n, &[]), sort(param(0)));
    let minor = npi(
      "α",
      sort1(),
      app(var(1), app(cnst(&format!("{n}.mk"), &[]), var(0))),
    );
    let rec_ty = npi(
      "motive",
      motive_ty,
      npi("mk", minor, npi("t", cnst(n, &[]), app(var(2), var(0)))),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  // ==========================================================================
  // Batch 3b: More bad inductives (Tutorial.lean lines 280–550)
  // ==========================================================================

  /// inductWrongCtorParams: constructor's result has wrong parameter application
  #[test]
  fn bad_induct_wrong_ctor_params() {
    let env = KEnv::<Meta>::new();
    // axiom aProp : Prop
    let (ap_id, ap_c) = mk_axiom("aProp", 0, vec![], sort0());
    env.insert(ap_id, ap_c);

    let n = "inductWrongCtorParams";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // I : Prop → Type   (1 param)
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: pi(sort0(), sort1()),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : ∀ (x : Type), I aProp   — passes aProp instead of x as param
    // At depth 1 (inside x binder): x = var(0)
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: npi("x", sort1(), app(cnst(n, &[]), cnst("aProp", &[]))),
      },
    );

    // Dummy recursor
    let rec_ty = ipi(
      "motive",
      pi(sort0(), pi(app(cnst(n, &[]), var(0)), sort(param(0)))),
      npi(
        "t",
        sort0(),
        npi("x", app(cnst(n, &[]), var(0)), app(app(var(2), var(1)), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  /// reflOccLeft: recursive occurrence on LEFT of arrow behind further arrows
  /// Constructor: (Nat → (I → Nat)) → I — I appears in negative position
  #[test]
  fn bad_induct_refl_occ_left() {
    let env = KEnv::<Meta>::new();
    // Need Nat as an axiom
    let (nat_id, nat_c) = mk_axiom("Nat", 0, vec![], sort1());
    env.insert(nat_id, nat_c);

    let n = "reflOccLeft";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (Nat → (I → Nat)) → I
    // The field type is Nat → (I → Nat), I occurs in negative position (left of inner arrow)
    let field_ty = pi(cnst("Nat", &[]), pi(cnst(n, &[]), cnst("Nat", &[])));
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: pi(field_ty, cnst(n, &[])),
      },
    );

    // Dummy recursor
    let rec_ty = npi(
      "motive",
      pi(cnst(n, &[]), sort(param(0))),
      npi(
        "mk",
        pi(
          pi(cnst("Nat", &[]), pi(cnst(n, &[]), cnst("Nat", &[]))),
          app(var(1), cnst(n, &[])),
        ),
        npi("t", cnst(n, &[]), app(var(2), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  /// reflOccInIndex: recursive occurrence in INDEX position behind arrow
  /// I : Type → Type, ctor mk : (α : Type) → (Nat → I (I α)) → I α
  #[test]
  fn bad_induct_refl_occ_in_index() {
    let env = KEnv::<Meta>::new();
    let (nat_id, nat_c) = mk_axiom("Nat", 0, vec![], sort1());
    env.insert(nat_id, nat_c);

    let n = "reflOccInIndex";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // I : Type → Type (0 params, 1 index)
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 1,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: npi("α", sort1(), sort1()),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (α : Type) → (Nat → I (I α)) → I α
    // At depth 1 (inside α): α = var(0)
    // field: Nat → I (I α) — I applied to (I α), recursive in index
    let i_alpha = app(cnst(n, &[]), var(0)); // I α
    let i_i_alpha = app(cnst(n, &[]), i_alpha); // I (I α)
    let _field_ty = pi(cnst("Nat", &[]), i_i_alpha); // Nat → I (I α), shifts inside pi
    // But inside the field pi: Nat binder is var(0), α = var(1)
    // So we need: pi(Nat, I(I(var(1)))) — var(1) = α shifted
    let i_alpha_s = app(cnst(n, &[]), var(1));
    let i_i_alpha_s = app(cnst(n, &[]), i_alpha_s);
    let field_ty_correct = pi(cnst("Nat", &[]), i_i_alpha_s);
    let result = app(cnst(n, &[]), var(1)); // I α, with α shifted by field binder
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: npi("α", sort1(), pi(field_ty_correct, result)),
      },
    );

    // Dummy recursor
    let rec_ty = npi(
      "motive",
      pi(sort1(), pi(app(cnst(n, &[]), var(0)), sort(param(0)))),
      npi(
        "t",
        sort1(),
        npi("x", app(cnst(n, &[]), var(0)), app(app(var(2), var(1)), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 1,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  // ==========================================================================
  // Batch 8: More bad inductives (Tutorial.lean lines 347–557)
  // ==========================================================================

  /// inductWrongCtorResParams: constructor result has parameters swapped
  /// I : Prop → Prop → Type, mk : (x : Prop) → (y : Prop) → I y x  (swapped!)
  #[test]
  fn bad_induct_wrong_ctor_res_params() {
    let env = KEnv::<Meta>::new();
    let n = "inductWrongCtorResParams";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // I : Prop → Prop → Type (2 params)
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 2,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: npi("x", sort0(), npi("y", sort0(), sort1())),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (x : Prop) → (y : Prop) → I y x   (params swapped in result!)
    // depth 2: x=var(1), y=var(0)
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 2,
        fields: 0,
        ty: npi(
          "x",
          sort0(),
          npi("y", sort0(), app(app(cnst(n, &[]), var(0)), var(1))),
        ), // I y x — swapped
      },
    );

    let rec_ty = npi(
      "x",
      sort0(),
      npi(
        "y",
        sort0(),
        ipi(
          "motive",
          pi(app(app(cnst(n, &[]), var(1)), var(0)), sort(param(0))),
          npi("t", app(app(cnst(n, &[]), var(2)), var(1)), app(var(1), var(0))),
        ),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 2,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  /// reduceCtorType: constructor type is `id Type I` instead of manifest `I`
  /// The kernel should NOT reduce the constructor's overall type.
  #[test]
  fn bad_reduce_ctor_type() {
    let env = KEnv::<Meta>::new();
    // id1 : Sort 1 → Sort 1 := fun x => x
    let (id1_id, id1_c) = mk_defn(
      "id1",
      0,
      vec![],
      pi(sort(usucc(uzero())), sort(usucc(uzero()))),
      nlam("x", sort(usucc(uzero())), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id1_id, id1_c);

    let n = "reduceCtorType";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : id1 I   (should be just I, not wrapped in id1)
    // id1 I reduces to I, but the kernel shouldn't reduce the ctor type
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: app(cnst("id1", &[]), cnst(n, &[])), // id1 I instead of I
      },
    );

    let rec_ty = npi(
      "motive",
      pi(cnst(n, &[]), sort(param(0))),
      npi(
        "mk",
        app(var(0), cnst(&format!("{n}.mk"), &[])),
        npi("t", cnst(n, &[]), app(var(2), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  /// indNegReducible: negative occurrence hidden behind reducible def
  /// constType aType I → I  where constType x y = x, so this reduces to aType → I
  /// But the kernel should catch the negative occurrence before reducing.
  #[test]
  fn bad_induct_neg_reducible() {
    let env = KEnv::<Meta>::new();
    // constType : Type → Type → Type := fun x y => x
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);
    // aType : Type
    let (at_id, at_c) = mk_axiom("aType", 0, vec![], sort1());
    env.insert(at_id, at_c);

    let n = "indNegReducible";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (constType aType I → I) → I
    // constType aType I = aType (first arg), so field type is (aType → I)
    // But before reduction: constType aType I has I in head-normal form's first arg
    // The kernel checks HNF and sees I in the function domain = negative occurrence
    let ct_app =
      app(app(cnst("constType", &[]), cnst("aType", &[])), cnst(n, &[]));
    let field_ty = pi(ct_app, cnst(n, &[])); // (constType aType I) → I
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: pi(field_ty, cnst(n, &[])),
      },
    );

    let rec_ty = npi(
      "motive",
      pi(cnst(n, &[]), sort(param(0))),
      npi(
        "mk",
        pi(
          pi(
            pi(
              app(
                app(cnst("constType", &[]), cnst("aType", &[])),
                cnst(n, &[]),
              ),
              cnst(n, &[]),
            ),
            cnst(n, &[]),
          ),
          app(var(1), cnst(n, &[])),
        ),
        npi("t", cnst(n, &[]), app(var(2), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  // ==========================================================================
  // Batch 9: Good inductives with universe constraints (Tutorial.lean 558–610)
  // ==========================================================================

  /// predWithTypeField : Prop — inductive Prop with a Type field (allowed for Props)
  #[test]
  fn good_pred_with_type_field() {
    let env = KEnv::<Meta>::new();
    let n = "PredWithTypeField";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // PredWithTypeField : Prop
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort0(), // Prop
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : Type → PredWithTypeField  (field is Type, allowed for Prop inductives)
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: npi("α", sort1(), cnst(n, &[])),
      },
    );

    // Recursor (can only eliminate into Prop for this kind of inductive)
    let rec_ty = ipi(
      "motive",
      pi(cnst(n, &[]), sort0()),
      npi(
        "mk",
        npi(
          "α",
          sort1(),
          app(var(1), app(cnst(&format!("{n}.mk"), &[]), var(0))),
        ),
        npi("t", cnst(n, &[]), app(var(2), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![], // no extra level param — eliminates only into Prop
        k: false,
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_accepts(&env, &block_id);
  }

  /// typeWithTypeField : Type 1 — inductive Type 1 with a Type field (allowed)
  #[test]
  fn good_type_with_type_field() {
    let env = KEnv::<Meta>::new();
    let n = "TypeWithTypeField";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // TypeWithTypeField : Sort 2 = Type 1
    let sort2 = sort(usucc(usucc(uzero())));
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort2, // Type 1
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : Type → TypeWithTypeField  (field is Type = Sort 1, OK for Type 1 inductive)
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 1,
        ty: npi("α", sort1(), cnst(n, &[])),
      },
    );

    let rec_ty = ipi(
      "motive",
      pi(cnst(n, &[]), sort(param(0))),
      npi(
        "mk",
        npi(
          "α",
          sort1(),
          app(var(1), app(cnst(&format!("{n}.mk"), &[]), var(0))),
        ),
        npi("t", cnst(n, &[]), app(var(2), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_accepts(&env, &block_id);
  }

  // ==========================================================================
  // Batch 11: inductInIndex, inductWrongCtorResLevel (Tutorial.lean 377–436)
  // ==========================================================================

  /// inductWrongCtorResLevel: constructor result applies inductive with
  /// swapped level params [u2, u1] instead of [u1, u2]
  #[test]
  fn bad_induct_wrong_ctor_res_level() {
    let env = KEnv::<Meta>::new();
    let n = "inductWrongCtorResLevel";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // I.{u1, u2} : Prop → Prop → Type (2 params, 2 level params)
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![mk_name("u1"), mk_name("u2")],
        lvls: 2,
        params: 2,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: npi("x", sort0(), npi("y", sort0(), sort1())),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk.{u1, u2} : (x : Prop) → (y : Prop) → I.{u2, u1} x y
    // Note: level params are SWAPPED in the result: [u2, u1] instead of [u1, u2]
    // depth 2: x=var(1), y=var(0)
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![mk_name("u1"), mk_name("u2")],
        is_unsafe: false,
        lvls: 2,
        induct: block_id.clone(),
        cidx: 0,
        params: 2,
        fields: 0,
        ty: npi(
          "x",
          sort0(),
          npi(
            "y",
            sort0(),
            // I.{u2, u1} x y — level params swapped!
            app(app(cnst(n, &[param(1), param(0)]), var(1)), var(0)),
          ),
        ),
      },
    );

    // Dummy recursor
    let rec_ty = npi(
      "x",
      sort0(),
      npi(
        "y",
        sort0(),
        ipi(
          "motive",
          pi(
            app(app(cnst(n, &[param(0), param(1)]), var(1)), var(0)),
            sort(param(2)),
          ),
          npi(
            "t",
            app(app(cnst(n, &[param(0), param(1)]), var(2)), var(1)),
            app(var(1), var(0)),
          ),
        ),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u_rec"), mk_name("u1"), mk_name("u2")],
        k: false,
        is_unsafe: false,
        lvls: 3,
        params: 2,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  /// inductInIndex: constructor result has inductive applied to itself in index position
  /// I : Prop → Prop, mk : I (I aProp)  — recursive occurrence in index
  #[test]
  fn bad_induct_in_index() {
    let env = KEnv::<Meta>::new();
    let (ap_id, ap_c) = mk_axiom("aProp", 0, vec![], sort0());
    env.insert(ap_id, ap_c);

    let n = "inductInIndex";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // I : Prop → Prop (0 params, 1 index)
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 1,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: pi(sort0(), sort0()),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : I (I aProp)  — I applied with I(aProp) as index
    let i_aprop = app(cnst(n, &[]), cnst("aProp", &[]));
    let i_i_aprop = app(cnst(n, &[]), i_aprop);
    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: i_i_aprop,
      },
    );

    let rec_ty = ipi(
      "motive",
      npi("x", sort0(), pi(app(cnst(n, &[]), var(0)), sort0())),
      npi(
        "x",
        sort0(),
        npi("t", app(cnst(n, &[]), var(0)), app(app(var(2), var(1)), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![],
        k: false,
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 1,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );
    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_rejects(&env, &block_id);
  }

  // ==========================================================================
  // Batch 14: Inductive with dup level params (Tutorial.lean 282–296)
  // ==========================================================================

  /// inductLevelParam: inductive with duplicate level params [u, u]
  #[test]
  fn bad_induct_dup_level_params() {
    let mut env = KEnv::<Meta>::new();
    let id = mk_simple_indc(
      &mut env,
      "inductLevelParam",
      2,                             // 2 level params
      &[mk_name("u"), mk_name("u")], // duplicate!
      &sort1(),
    );
    check_rejects(&env, &id);
  }

  // ==========================================================================
  // Batch 17: BoolProp — Prop inductive with 2 ctors, large elim restriction
  // (Tutorial.lean 658–663)
  // ==========================================================================

  /// BoolProp : Prop with 2 constructors — recursor can only eliminate into Prop
  #[test]
  fn good_bool_prop_rec() {
    let env = KEnv::<Meta>::new();

    let n = "BoolProp";
    let block_id = mk_id(n);
    let a_id = mk_id("BoolProp.a");
    let b_id = mk_id("BoolProp.b");
    let rec_id = mk_id("BoolProp.rec");

    // BoolProp : Prop
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort0(), // Prop
        ctors: vec![a_id.clone(), b_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    env.insert(
      a_id.clone(),
      KConst::Ctor {
        name: mk_name("BoolProp.a"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: cnst(n, &[]),
      },
    );

    env.insert(
      b_id.clone(),
      KConst::Ctor {
        name: mk_name("BoolProp.b"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 1,
        params: 0,
        fields: 0,
        ty: cnst(n, &[]),
      },
    );

    // BoolProp.rec : ∀ {motive : BoolProp → Prop}
    //   (a : motive BoolProp.a) (b : motive BoolProp.b) (x : BoolProp), motive x
    // Note: eliminates into Prop only (no level param), because 2 ctors for a Prop inductive
    let motive_ty = pi(cnst(n, &[]), sort0()); // BoolProp → Prop
    let minor_a = app(var(0), cnst("BoolProp.a", &[]));
    let minor_b = app(var(1), cnst("BoolProp.b", &[]));
    let rec_ty = ipi(
      "motive",
      motive_ty.clone(),
      npi(
        "a",
        minor_a.clone(),
        npi("b", minor_b.clone(), npi("x", cnst(n, &[]), app(var(3), var(0)))),
      ),
    );

    let rule_a_rhs = nlam(
      "motive",
      motive_ty.clone(),
      nlam("ha", minor_a.clone(), nlam("hb", minor_b.clone(), var(1))),
    );
    let rule_b_rhs = nlam(
      "motive",
      motive_ty,
      nlam("ha", minor_a, nlam("hb", minor_b, var(0))),
    );

    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name("BoolProp.rec"),
        level_params: vec![],
        k: false,
        is_unsafe: false,
        lvls: 0, // no level param — Prop only
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          RecRule { fields: 0, rhs: rule_a_rhs },
          RecRule { fields: 0, rhs: rule_b_rhs },
        ],
        lean_all: vec![block_id.clone()],
      },
    );

    env.blocks.insert(
      block_id.clone(),
      vec![block_id.clone(), a_id, b_id, rec_id.clone()],
    );

    // Check the inductive
    check_accepts(&env, &block_id);
    // Check the recursor
    check_accepts(&env, &rec_id);
  }

  // ==========================================================================
  // Batch 19: reduceCtorParam — good inductive where ctor param type needs reduction
  // (Tutorial.lean 468–485)
  // ==========================================================================

  /// reduceCtorParam: inductive I : Type → Type with ctor
  ///   mk : (α : id Type) → (constType (I α) (I α)) → I α
  /// The kernel should reduce `id Type` → Type and `constType (I α) (I α)` → I α
  /// in ctor parameter positions.
  #[test]
  fn good_reduce_ctor_param() {
    let env = KEnv::<Meta>::new();

    // id1 : Sort 1 → Sort 1 := fun x => x
    let (id1_id, id1_c) = mk_defn(
      "id1",
      0,
      vec![],
      pi(sort(usucc(uzero())), sort(usucc(uzero()))),
      nlam("x", sort(usucc(uzero())), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id1_id, id1_c);

    // constType : Type → Type → Type := fun x y => x
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);

    let n = "reduceCtorParam";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // reduceCtorParam : Type → Type (1 param)
    // is_rec = true because field `constType (I α) (I α)` reduces to `I α` (recursive)
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: pi(sort1(), sort1()),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (α : id1 Type) → (constType (I α) (I α)) → I α
    // id1 Type reduces to Type, constType (I α) (I α) reduces to I α
    // depth 1 (inside α binder): α=var(0)
    // The param type is `id1 Type` = `app(cnst("id1"), sort1())`
    // The field type is `constType (I α) (I α)` at depth 1:
    //   app(app(cnst("constType"), app(cnst(n), var(0))), app(cnst(n), var(0)))
    // Inside the field pi (depth 2): α=var(1), field binder=var(0)
    // Result: I α at depth 2 = app(cnst(n), var(1))
    let id1_type = app(cnst("id1", &[]), sort1());
    let i_alpha = app(cnst(n, &[]), var(0));
    let field_ty = app(app(cnst("constType", &[]), i_alpha.clone()), i_alpha);
    let result = app(cnst(n, &[]), var(1)); // I α shifted by field binder

    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: npi("α", id1_type, pi(field_ty, result)),
      },
    );

    // Recursor
    let motive_ty =
      npi("α", sort1(), pi(app(cnst(n, &[]), var(0)), sort(param(0))));
    let minor = npi(
      "α",
      sort1(),
      npi(
        "x",
        app(
          app(cnst("constType", &[]), app(cnst(n, &[]), var(0))),
          app(cnst(n, &[]), var(0)),
        ),
        app(app(var(2), var(1)), app(cnst(&format!("{n}.mk"), &[]), var(0))),
      ),
    );
    let rec_ty = ipi(
      "motive",
      motive_ty,
      npi(
        "mk",
        minor,
        npi(
          "α",
          sort1(),
          npi("t", app(cnst(n, &[]), var(0)), app(app(var(3), var(1)), var(0))),
        ),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_accepts(&env, &block_id);
  }

  // ==========================================================================
  // reduceCtorParamRefl: reflexive inductive with reducible ctor param types
  // (Tutorial.lean 1095–1107)
  // ==========================================================================

  /// reduceCtorParamRefl: I : Type → Type, 1 param
  /// mk : (α : id Type) → (α → constType (I α) (I α)) → I α
  /// Field type α → constType (I α) (I α) reduces to α → I α (reflexive occurrence).
  /// Kernel should reduce ctor param types and accept this reflexive inductive.
  #[test]
  fn good_reduce_ctor_param_refl() {
    let env = KEnv::<Meta>::new();

    // id1 : Sort 1 → Sort 1 := fun x => x
    let (id1_id, id1_c) = mk_defn(
      "id1",
      0,
      vec![],
      pi(sort(usucc(uzero())), sort(usucc(uzero()))),
      nlam("x", sort(usucc(uzero())), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id1_id, id1_c);

    // constType : Type → Type → Type := fun x y => x
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);

    let n = "reduceCtorParamRefl";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    // I : Type → Type (1 param), reflexive
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: true,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: pi(sort1(), sort1()),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (α : id1 Type) → (α → constType (I α) (I α)) → I α
    // Param type: id1 Type (reduces to Type)
    // Field type: α → constType (I α) (I α) where α=var(0) at depth 1
    // Inside field pi (depth 2): x=var(0), α=var(1)
    //   constType (I α) (I α) = constType (I var(1)) (I var(1)) reduces to I var(1)
    let id1_type = app(cnst("id1", &[]), sort1());
    let i_alpha = app(cnst(n, &[]), var(1)); // I α at depth 2
    let ct_i_i = app(app(cnst("constType", &[]), i_alpha.clone()), i_alpha);
    let field_ty = pi(var(0), ct_i_i); // α → constType (I α) (I α) at depth 1
    // result: I α at depth 2 (inside field binder)
    let result = app(cnst(n, &[]), var(1));

    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: npi("α", id1_type, pi(field_ty, result)),
      },
    );

    // Minimal recursor
    let rec_ty = ipi(
      "motive",
      npi("α", sort1(), pi(app(cnst(n, &[]), var(0)), sort(param(0)))),
      npi(
        "α",
        sort1(),
        npi("t", app(cnst(n, &[]), var(0)), app(app(var(2), var(1)), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_accepts(&env, &block_id);
  }

  /// reduceCtorParamRefl2: variant where constType (I α) α reduces to I α (not I α, I α)
  /// mk : (α : id Type) → (α → constType (I α) α) → I α
  /// Field: α → constType (I α) α reduces to α → I α (reflexive)
  #[test]
  fn good_reduce_ctor_param_refl2() {
    let env = KEnv::<Meta>::new();

    let (id1_id, id1_c) = mk_defn(
      "id1",
      0,
      vec![],
      pi(sort(usucc(uzero())), sort(usucc(uzero()))),
      nlam("x", sort(usucc(uzero())), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id1_id, id1_c);
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);

    let n = "reduceCtorParamRefl2";
    let block_id = mk_id(n);
    let ctor_id = mk_id(&format!("{n}.mk"));
    let rec_id = mk_id(&format!("{n}.rec"));

    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: true,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: pi(sort1(), sort1()),
        ctors: vec![ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // mk : (α : id1 Type) → (α → constType (I α) α) → I α
    // d1: α=var(0). id1 Type as domain.
    // d2 (inside field pi): x=var(0), α=var(1)
    //   constType (I α) α = constType (I var(1)) var(1) → reduces to I var(1)
    let id1_type = app(cnst("id1", &[]), sort1());
    let i_alpha_d2 = app(cnst(n, &[]), var(1)); // I α at depth 2
    let ct_i_a = app(app(cnst("constType", &[]), i_alpha_d2), var(1)); // constType (I α) α
    let field_ty = pi(var(0), ct_i_a); // α → constType (I α) α at d1
    let result = app(cnst(n, &[]), var(1)); // I α at d2

    env.insert(
      ctor_id.clone(),
      KConst::Ctor {
        name: mk_name(&format!("{n}.mk")),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 1,
        fields: 1,
        ty: npi("α", id1_type, pi(field_ty, result)),
      },
    );

    let rec_ty = ipi(
      "motive",
      npi("α", sort1(), pi(app(cnst(n, &[]), var(0)), sort(param(0)))),
      npi(
        "α",
        sort1(),
        npi("t", app(cnst(n, &[]), var(0)), app(app(var(2), var(1)), var(0))),
      ),
    );
    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name(&format!("{n}.rec")),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id.clone(), ctor_id, rec_id]);
    check_accepts(&env, &block_id);
  }
}
