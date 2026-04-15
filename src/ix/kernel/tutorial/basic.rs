//! Basic definitions, levels, lets, forall checks, and level params.

#[cfg(test)]
mod tests {
  use std::sync::Arc;

  use crate::ix::env::ReducibilityHints;
  use crate::ix::kernel::env::KEnv;
  use crate::ix::kernel::mode::Meta;
  use crate::ix::kernel::testing::*;

  // ==========================================================================
  // Batch 1: Basic definitions (Tutorial.lean lines 16–60)
  // ==========================================================================

  /// good_def basicDef : Type := Prop
  #[test]
  fn good_basic_def() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (id, c) = mk_defn(
      "basicDef",
      0,
      vec![],
      sort1(),
      sort0(),
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// bad_def badDef : Prop := Type
  /// Value `Type` has type `Type 1`, not `Prop`.
  #[test]
  fn bad_def_type_mismatch() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (id, c) =
      mk_defn("badDef", 0, vec![], sort0(), sort1(), ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_rejects(&env, &id);
  }

  /// good_def arrowType : Type := Prop → Prop
  #[test]
  fn good_arrow_type() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (id, c) = mk_defn(
      "arrowType",
      0,
      vec![],
      sort1(),
      pi(sort0(), sort0()), // Prop → Prop
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// good_def dependentType : Prop := ∀ (p : Prop), p
  #[test]
  fn good_dependent_type() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (id, c) = mk_defn(
      "dependentType",
      0,
      vec![],
      sort0(),
      npi("p", sort0(), var(0)), // ∀ (p : Prop), p
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// good_def constType : Type → Type → Type := fun x y => x
  #[test]
  fn good_const_type() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (id, c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())), // Type → Type → Type
      nlam("x", sort1(), nlam("y", sort1(), var(1))), // fun x y => x
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// good_def betaReduction : constType Prop (Prop → Prop) := ∀ p : Prop, p
  /// Requires `constType` in env. `constType Prop (Prop → Prop)` reduces to `Prop`.
  #[test]
  fn good_beta_reduction() {
    let env = Arc::new(KEnv::<Meta>::new());
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

    // betaReduction : constType Prop (Prop → Prop) := ∀ p : Prop, p
    // constType Prop (Prop → Prop) β-reduces to Prop
    let ty = app(app(cnst("constType", &[]), sort0()), pi(sort0(), sort0()));
    let (id, c) = mk_defn(
      "betaReduction",
      0,
      vec![],
      ty,
      npi("p", sort0(), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// good_def betaReduction2 : ∀ (p : Prop), constType Prop (Prop → Prop) := fun p => p
  #[test]
  fn good_beta_reduction2() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);

    // ∀ (p : Prop), constType Prop (Prop → Prop)
    let ct_applied =
      app(app(cnst("constType", &[]), sort0()), pi(sort0(), sort0()));
    let ty = npi("p", sort0(), ct_applied);
    let val = nlam("p", sort0(), var(0));
    let (id, c) =
      mk_defn("betaReduction2", 0, vec![], ty, val, ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// good_def forallSortWhnf : Prop := ∀ (p : id Prop) (x : p), p
  /// `id Prop` must WHNF to `Prop` (a Sort) for the forall to typecheck.
  #[test]
  fn good_forall_sort_whnf() {
    let env = Arc::new(KEnv::<Meta>::new());
    // id : Type → Type := fun x => x
    let (id_id, id_c) = mk_defn(
      "id",
      0,
      vec![],
      pi(sort1(), sort1()),
      nlam("x", sort1(), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id_id, id_c);

    // forallSortWhnf : Prop := ∀ (p : id Prop) (x : p), p
    let id_prop = app(cnst("id", &[]), sort0()); // id Prop
    let val = npi("p", id_prop, npi("x", var(0), var(1)));
    let (id, c) = mk_defn(
      "forallSortWhnf",
      0,
      vec![],
      sort0(),
      val,
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// bad_def nonTypeType : constType := Prop
  /// `constType` is `Type → Type → Type`, not a Sort — can't be a type annotation.
  #[test]
  fn bad_non_type_type() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (ct_id, ct_c) = mk_defn(
      "constType",
      0,
      vec![],
      pi(sort1(), pi(sort1(), sort1())),
      nlam("x", sort1(), nlam("y", sort1(), var(1))),
      ReducibilityHints::Abbrev,
    );
    env.insert(ct_id, ct_c);

    // nonTypeType : constType := Prop
    // constType is (Type → Type → Type), not a Sort
    let (id, c) = mk_defn(
      "nonTypeType",
      0,
      vec![],
      cnst("constType", &[]), // not a sort!
      sort0(),
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_rejects(&env, &id);
  }

  // ==========================================================================
  // Batch 2: Level computation (Tutorial.lean lines 62–118)
  // ==========================================================================

  /// levelComp1 : Sort 1 := Sort (imax 1 0)
  /// imax 1 0 = 0 (because second arg is 0), so Sort(imax 1 0) = Sort 0 = Prop
  /// But type is Sort 1 = Type, so Prop : Type is correct.
  #[test]
  fn good_level_comp1() {
    let env = Arc::new(KEnv::<Meta>::new());
    let ty = sort(usucc(uzero())); // Sort 1
    let val = sort(uimax(usucc(uzero()), uzero())); // Sort (imax 1 0)
    let (id, c) =
      mk_defn("levelComp1", 0, vec![], ty, val, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// levelComp2 : Sort 2 := Sort (imax 0 1)
  /// imax 0 1 = max 0 1 = 1 (since second arg is nonzero), so Sort(imax 0 1) = Sort 1 = Type.
  /// Type : Sort 2 is correct.
  #[test]
  fn good_level_comp2() {
    let env = Arc::new(KEnv::<Meta>::new());
    let ty = sort(usucc(usucc(uzero()))); // Sort 2
    let val = sort(uimax(uzero(), usucc(uzero()))); // Sort (imax 0 1)
    let (id, c) =
      mk_defn("levelComp2", 0, vec![], ty, val, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// levelComp3 : Sort 3 := Sort (imax 2 1)
  /// imax 2 1 = max 2 1 = 2, so Sort(imax 2 1) = Sort 2. Sort 2 : Sort 3.
  #[test]
  fn good_level_comp3() {
    let env = Arc::new(KEnv::<Meta>::new());
    let ty = sort(usucc(usucc(usucc(uzero())))); // Sort 3
    let val = sort(uimax(usucc(usucc(uzero())), usucc(uzero()))); // Sort (imax 2 1)
    let (id, c) =
      mk_defn("levelComp3", 0, vec![], ty, val, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// levelComp4.{u} : Type 0 := Sort (imax u 0)
  /// imax u 0 = 0 for all u (second arg is zero), so Sort(imax u 0) = Prop.
  /// Prop : Type 0 is correct.
  #[test]
  fn good_level_comp4() {
    let env = Arc::new(KEnv::<Meta>::new());
    let ty = sort(usucc(uzero())); // Type 0 = Sort 1
    let val = sort(uimax(param(0), uzero())); // Sort (imax u 0)
    let (id, c) = mk_defn(
      "levelComp4",
      1,
      vec![mk_name("u")],
      ty,
      val,
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// levelComp5.{u} : Type u := Sort (imax u u)
  /// imax u u = u (if u=0 then 0, else max u u = u).
  /// Sort u : Type u = Sort (u+1).
  #[test]
  fn good_level_comp5() {
    let env = Arc::new(KEnv::<Meta>::new());
    let ty = sort(usucc(param(0))); // Type u = Sort (u+1)
    let val = sort(uimax(param(0), param(0))); // Sort (imax u u)
    let (id, c) = mk_defn(
      "levelComp5",
      1,
      vec![mk_name("u")],
      ty,
      val,
      ReducibilityHints::Abbrev,
    );
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// imax1 : (p : Prop) → Prop := fun p => Type → p
  /// Inside the lambda, p : Prop, so (Type → p) : Sort(imax 2 1) but
  /// actually the type of (Type → p) where p : Prop uses imax:
  /// Type : Sort 2, p : Sort 0, so (Type → p) : Sort (imax 2 0) = Sort 0 = Prop.
  /// Wait, p is a variable of type Prop. The forall (Type → p) has domain Sort 2
  /// and codomain p (which is in Sort 0 since p : Prop). So the forall is
  /// in Sort(imax 2 0) = Sort 0 = Prop. So fun p => (Type → p) : Prop → Prop.
  /// And (p : Prop) → Prop : Prop.
  #[test]
  fn good_imax1() {
    let env = Arc::new(KEnv::<Meta>::new());
    // (p : Prop) → Prop
    let ty = npi("p", sort0(), sort0());
    // fun p => Type → p
    // Inside lambda: p is var(0). Inside the pi body, p shifts to var(1).
    let val = nlam("p", sort0(), pi(sort1(), var(1)));
    let (id, c) =
      mk_defn("imax1", 0, vec![], ty, val, ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// imax2 : (α : Type) → Type 1 := fun α => Type → α
  /// Inside lambda: α is var(0) : Type = Sort 1.
  /// (Type → α) has domain Type : Sort 2 and codomain α : Sort 1.
  /// So (Type → α) : Sort(imax 2 1) = Sort(max 2 1) = Sort 2 = Type 1.
  /// fun α => (Type → α) : (α : Type) → Type 1.
  #[test]
  fn good_imax2() {
    let env = Arc::new(KEnv::<Meta>::new());
    // (α : Type) → Type 1
    let ty = npi("α", sort1(), sort(usucc(usucc(uzero()))));
    // fun α => Type → α
    let val = nlam("α", sort1(), pi(sort1(), var(0)));
    let (id, c) =
      mk_defn("imax2", 0, vec![], ty, val, ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Batch 2b: Variable inference & def-eq (Tutorial.lean lines 119–125)
  // ==========================================================================

  /// inferVar : ∀ (f : Prop) (g : f), f := fun f g => g
  #[test]
  fn good_infer_var() {
    let env = Arc::new(KEnv::<Meta>::new());
    // ∀ (f : Prop) (g : f), f
    let ty = npi("f", sort0(), npi("g", var(0), var(1)));
    // fun f g => g
    let val = nlam("f", sort0(), nlam("g", var(0), var(0)));
    let (id, c) =
      mk_defn("inferVar", 0, vec![], ty, val, ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// defEqLambda : ∀ (f : (Prop → Prop) → Prop) (g : (a : Prop → Prop) → f a),
  ///   f (fun p => p → p) := fun f g => g (fun p => p → p)
  #[test]
  fn good_def_eq_lambda() {
    let env = Arc::new(KEnv::<Meta>::new());
    // f : (Prop → Prop) → Prop
    let f_ty = pi(pi(sort0(), sort0()), sort0());
    // g : (a : Prop → Prop) → f a
    // Under f binder: f is var(0)
    // g : ∀ (a : Prop → Prop), app(var(1), var(0))
    let g_ty = npi("a", pi(sort0(), sort0()), app(var(1), var(0)));
    // result: f (fun p => p → p)
    let pp = nlam("p", sort0(), pi(var(0), var(1))); // fun p => p → p
    let result = app(var(1), pp.clone());
    let ty = npi("f", f_ty.clone(), npi("g", g_ty, result));
    // fun f g => g (fun p => p → p)
    let val = nlam(
      "f",
      f_ty,
      nlam(
        "g",
        npi("a", pi(sort0(), sort0()), app(var(1), var(0))),
        app(var(0), pp),
      ),
    );
    let (id, c) =
      mk_defn("defEqLambda", 0, vec![], ty, val, ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Batch 2c: Let declarations (Tutorial.lean lines 159–196)
  // ==========================================================================

  /// letType : Sort 1 := let x : Sort 1 := Sort 0; x
  /// The let reduces: x = Sort 0, so the value is Sort 0 : Sort 1.
  #[test]
  fn good_let_type() {
    let env = Arc::new(KEnv::<Meta>::new());
    let ty = sort1();
    // let x : Sort 1 := Sort 0; x (= bvar 0)
    let val = let_(sort1(), sort0(), var(0));
    let (id, c) =
      mk_defn("letType", 0, vec![], ty, val, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// letTypeDep : aDepProp (Sort 0) := let x : Sort 1 := Sort 0; mkADepProp x
  /// Requires aDepProp and mkADepProp axioms.
  #[test]
  fn good_let_type_dep() {
    let env = Arc::new(KEnv::<Meta>::new());
    // axiom aDepProp : Type → Prop
    let (adp_id, adp_c) = mk_axiom("aDepProp", 0, vec![], pi(sort1(), sort0()));
    env.insert(adp_id, adp_c);
    // axiom mkADepProp : ∀ t, aDepProp t
    let (mkadp_id, mkadp_c) = mk_axiom(
      "mkADepProp",
      0,
      vec![],
      npi("t", sort1(), app(cnst("aDepProp", &[]), var(0))),
    );
    env.insert(mkadp_id, mkadp_c);

    // letTypeDep : aDepProp (Sort 0) := let x : Sort 1 := Sort 0; mkADepProp x
    let ty = app(cnst("aDepProp", &[]), sort0());
    let val = let_(sort1(), sort0(), app(cnst("mkADepProp", &[]), var(0)));
    let (id, c) =
      mk_defn("letTypeDep", 0, vec![], ty, val, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// letRed : (let x : Sort 1 := Sort 0; x) := aProp
  /// The type has a let that reduces to Sort 0 = Prop. aProp : Prop.
  #[test]
  fn good_let_red() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (ap_id, ap_c) = mk_axiom("aProp", 0, vec![], sort0());
    env.insert(ap_id, ap_c);

    // type: let x : Sort 1 := Sort 0; x — reduces to Sort 0 = Prop
    let ty = let_(sort1(), sort0(), var(0));
    let val = cnst("aProp", &[]);
    let (id, c) =
      mk_defn("letRed", 0, vec![], ty, val, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Batch 6: Duplicate level params (Tutorial.lean line 98–106)
  // ==========================================================================

  /// tut06_bad01: definition with duplicate level params [u, u]
  #[test]
  fn bad_duplicate_level_params() {
    let env = Arc::new(KEnv::<Meta>::new());
    let (id, c) = mk_defn(
      "tut06_bad01",
      2,                                // claims 2 level params
      vec![mk_name("u"), mk_name("u")], // duplicate!
      sort(usucc(uzero())),             // Sort 1
      sort0(),                          // Sort 0
      ReducibilityHints::Opaque,
    );
    env.insert(id.clone(), c);
    check_rejects(&env, &id);
  }

  // ==========================================================================
  // Batch 7: forallSortBad and nonPropThm (Tutorial.lean lines 41–61)
  // ==========================================================================

  /// forallSortBad: value has a forall whose domain is id Type Prop, which
  /// reduces to Prop (a Sort) — but the outer structure uses it wrong.
  /// The value is: ∀ (_ : id Type Prop), ∀ (_ : bvar0), ∀ (_ : bvar0), bvar1
  /// After reducing id Type Prop → Prop:
  ///   ∀ (_ : Prop), ∀ (_ : bvar0), ∀ (_ : bvar0), bvar1
  /// bvar0 in the 2nd forall refers to a Prop variable, which is not a Sort.
  /// But with the unreduced `id Type Prop`, the domain `bvar0` might look different.
  /// The test is: type = Sort 0, value has this arrow expression.
  /// The kernel should check that each forall's domain is a Sort (after WHNF).
  /// The innermost domain `bvar0` refers to a variable of type Prop, not a Sort.
  #[test]
  fn bad_forall_sort_bad() {
    let env = Arc::new(KEnv::<Meta>::new());
    // id : {α : Sort u} → α → α, simplified as Type → Type → Type... no.
    // id.{2} : Sort 2 → Sort 2 := fun x => x
    // id.{2} (Sort 1) (Sort 0) = Sort 0 = Prop
    // Let's use: id_univ2 : Sort 2 → Sort 2 := fun x => x
    let (id2_id, id2_c) = mk_defn(
      "id2",
      0,
      vec![],
      pi(sort(usucc(usucc(uzero()))), sort(usucc(usucc(uzero())))), // Sort 2 → Sort 2
      nlam("x", sort(usucc(usucc(uzero()))), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id2_id, id2_c);

    // forallSortBad : Prop := ∀ (_ : id2 (Sort 1) applied to Sort 0... )
    // Actually simpler: the domain is (id2 Prop) which reduces to Prop.
    // Then the next domain is bvar(0) which is a Prop value, NOT a Sort.
    //
    // value = ∀ (_ : id2 Prop), ∀ (_ : bvar0), bvar1
    // After WHNF of `id2 Prop` → Prop. Then domain 2 is bvar0 : Prop (not a Sort).
    // Wait, id2 : Sort 2 → Sort 2. Prop = Sort 0 : Sort 1, not Sort 2.
    // So id2 Prop would fail (Prop : Sort 1, not Sort 2).
    //
    // Let's use a simpler approach: id at level 1.
    // id1 : Sort 1 → Sort 1 := fun x => x
    // id1 Prop = Prop (since Prop : Sort 1)
    let (id1_id, id1_c) = mk_defn(
      "id1",
      0,
      vec![],
      pi(sort(usucc(uzero())), sort(usucc(uzero()))), // Sort 1 → Sort 1
      nlam("x", sort(usucc(uzero())), var(0)),
      ReducibilityHints::Abbrev,
    );
    env.insert(id1_id, id1_c);

    // value = ∀ (_ : id1 Prop), ∀ (_ : bvar0), bvar1
    // id1 Prop reduces to Prop (a Sort). First forall OK.
    // Second forall: domain = bvar0 (the variable of type Prop). Not a Sort!
    let id1_prop = app(cnst("id1", &[]), sort0());
    // ∀ (_ : id1 Prop), ∀ (_ : bvar0), ∀ (_ : bvar0), bvar1
    // depth 1: _1 : Prop (from id1 Prop)
    // depth 2: _2 : _1 (var(0) at depth 1 = _1, a Prop variable). _2 has type _1 : Prop.
    // depth 3: domain = bvar0 = _2 (var(0) at depth 2). _2 has type _1 (Prop value).
    //   infer(_2) = _1. ensure_sort(_1) must fail: _1 is a Prop variable, not a Sort.
    let value = npi(
      "_",
      id1_prop, // ∀ _1 : id1 Prop, ...
      npi(
        "_",
        var(0), // ∀ _2 : _1, ... (_1 : Prop, so _2 has a Prop-typed type)
        npi(
          "_",
          var(0), // ∀ _3 : _2, ... — _2's type is _1 (a Prop var, NOT Sort)
          var(1),
        ),
      ),
    ); // _2

    let (id, c) = mk_defn(
      "forallSortBad",
      0,
      vec![],
      sort0(),
      value,
      ReducibilityHints::Opaque,
    );
    env.insert(id.clone(), c);
    check_rejects(&env, &id);
  }

  // ==========================================================================
  // Batch 15: levelParams test (Tutorial.lean 93–96)
  // ==========================================================================

  /// levelParams: levelParamF.{u} Prop (Prop → Prop) := ∀ p : Prop, p
  /// where levelParamF.{u} : Sort u → Sort u → Sort u := fun α β => α
  #[test]
  fn good_level_params() {
    let env = Arc::new(KEnv::<Meta>::new());
    // levelParamF.{u} : Sort u → Sort u → Sort u := fun α β => α
    let lpf_ty = pi(sort(param(0)), pi(sort(param(0)), sort(param(0))));
    // Inside the pi's: at depth 2, α=var(1), β=var(0). Return α = var(1).
    let lpf_val = nlam("α", sort(param(0)), nlam("β", sort(param(0)), var(1)));
    let (lpf_id, lpf_c) = mk_defn(
      "levelParamF",
      1,
      vec![mk_name("u")],
      lpf_ty,
      lpf_val,
      ReducibilityHints::Abbrev,
    );
    env.insert(lpf_id, lpf_c);

    // levelParams : levelParamF.{0} Prop (Prop → Prop) := ∀ p : Prop, p
    // levelParamF.{0} Prop (Prop → Prop) reduces to Prop (first arg)
    // Lean infers levelParamF.{1} since Prop : Type = Sort 1
    let ty = app(
      app(cnst("levelParamF", &[usucc(uzero())]), sort0()),
      pi(sort0(), sort0()),
    );
    let val = npi("p", sort0(), var(0));
    let (id, c) =
      mk_defn("levelParams", 0, vec![], ty, val, ReducibilityHints::Abbrev);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Batch 18: nonPropThm (Tutorial.lean 55–61)
  // ==========================================================================

  /// nonPropThm: theorem whose type is Sort 0, value is Prop → bvar0
  /// A theorem's type must itself be a Prop (Sort 0), but the VALUE's
  /// inferred type must match. Here type = Sort 0 but value = Prop → bvar0
  /// which has type Sort 1 (a function type), not Sort 0.
  #[test]
  fn bad_non_prop_thm() {
    let env = Arc::new(KEnv::<Meta>::new());
    // type = Sort 0 = Prop
    // value = Prop → bvar0 = ∀ (_ : Prop), bvar0
    // But inside the pi body bvar0 refers to the pi's variable (of type Prop).
    // infer(value) = Sort(imax 1 0) = Sort 0 = Prop... wait.
    // Actually: domain Prop : Sort 1, so l_a = 1.
    // Codomain: bvar0 has type Prop. infer(bvar0) = Prop = Sort 0, l_b = 0.
    // Pi type: Sort(imax 1 0) = Sort 0 = Prop.
    // So the value HAS type Prop, same as the declared type. This should be accepted.
    //
    // Hmm, looking at the tutorial more carefully: the value is
    //   arrow (.sort 0) (.bvar 0)
    // where .bvar 0 in the ARROW BODY refers to the arrow's own bound var.
    // So this is ∀ (_ : Prop), _ where _ is the bound var itself.
    // The bound var has type Prop. infer(bvar0) = Prop = Sort 0.
    // For this to be valid as a pi body, we need the body's type to be a Sort.
    // Sort 0 IS a Sort. So the pi is well-typed: Sort(imax 1 0) = Sort 0 = Prop.
    //
    // But the tutorial says this is BAD because "The type of a theorem has to be a proposition."
    // The theorem's type IS Sort 0 = Prop. And the value also has type Prop.
    // Maybe the BAD part is that a theorem's declared type must be a proposition
    // (i.e., have type Prop), but Sort 0 itself has type Sort 1, not Prop.
    //
    // Actually: the declared type of the theorem is `.sort 0`. The TYPE OF `.sort 0` is
    // `.sort 1`. For a theorem, we check `infer(ty)` and `ensure_sort` — that gives level 1.
    // Then we should additionally check that this level IS 0 (Prop).
    // The kernel currently doesn't enforce "theorem types must be Prop."
    //
    // This is a theorem-specific check that the zero kernel may not implement.
    let ty = sort0(); // Sort 0 = Prop
    let val = pi(sort0(), var(0)); // Prop → bvar0
    let (id, c) = mk_thm("nonPropThm", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    // The lean kernel requires theorems' types to be Prop (level 0).
    // Sort 0 has type Sort 1, so the theorem type is in Sort 1, not Prop.
    check_rejects(&env, &id);
  }
}
