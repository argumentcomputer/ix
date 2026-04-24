//! Recursor reduction tests: Peano arithmetic, Bool.rec, Nat.rec.

#[cfg(test)]
mod tests {
  use std::sync::Arc;

  use crate::ix::env::{Name, ReducibilityHints};
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::constant::RecRule;
  use crate::ix::kernel::env::KEnv;
  use crate::ix::kernel::mode::Meta;
  use crate::ix::kernel::testing::*;

  // ==========================================================================
  // Batch 5: Peano arithmetic (Tutorial.lean lines 127–153)
  // ==========================================================================

  /// Build a Church-numeral Peano env:
  /// PN := ∀ α, (α → α) → α → α
  /// PN.zero : PN := fun α s z => z
  /// PN.succ : PN → PN := fun n α s z => s (n α s z)
  fn peano_env() -> Arc<KEnv<Meta>> {
    let env = Arc::new(KEnv::<Meta>::new());
    // PN := ∀ α, (α → α) → α → α
    // = ∀ (α : Type), (α → α) → α → α
    // depth 0: α=var(0). (α → α) = pi(var(0), var(1)). α → α at depth 1.
    // Full: npi("α", sort1(), pi(pi(var(0), var(1)), pi(var(1), var(2))))
    let pn_ty = sort1(); // PN : Type
    let _pn_val = npi(
      "α",
      sort1(),
      pi(
        pi(var(0), var(1)), // (α → α) at depth 1: α shifted to var(1)
        pi(
          var(1), // α at depth 2: α = var(2)... wait
          var(2),
        ),
      ),
    ); // α at depth 3
    // Actually: ∀ (α : Type), (α → α) → α → α
    // = npi("α", Sort 1, npi("s", pi(var(0), var(1)), npi("z", var(1), var(2))))
    // depth 0 (outside): nothing
    // depth 1 (inside α): α = var(0)
    //   s_ty = α → α = pi(var(0), var(1)) — inside pi: α shifts to var(1)
    // depth 2 (inside s): s = var(0), α = var(1)
    //   z_ty = α = var(1)
    // depth 3 (inside z): z = var(0), s = var(1), α = var(2)
    //   result = α = var(2)
    let pn_val2 =
      npi("α", sort1(), npi("s", pi(var(0), var(1)), npi("z", var(1), var(2))));
    let (pn_id, pn_c) =
      mk_defn("PN", 0, vec![], pn_ty, pn_val2, ReducibilityHints::Abbrev);
    env.insert(pn_id, pn_c);

    // PN.zero : PN := fun α s z => z
    let (z_id, z_c) = mk_defn(
      "PN.zero",
      0,
      vec![],
      cnst("PN", &[]),
      nlam(
        "α",
        sort1(),
        nlam("s", pi(var(0), var(1)), nlam("z", var(1), var(0))),
      ),
      ReducibilityHints::Abbrev,
    );
    env.insert(z_id, z_c);

    // PN.succ : PN → PN := fun n α s z => s (n α s z)
    // depth 4: z=var(0), s=var(1), α=var(2), n=var(3)
    // n α s z = app(app(app(var(3), var(2)), var(1)), var(0))
    // s (n α s z) = app(var(1), app(app(app(var(3), var(2)), var(1)), var(0)))
    let succ_body = app(var(1), apps(var(3), &[var(2), var(1), var(0)]));
    let (s_id, s_c) = mk_defn(
      "PN.succ",
      0,
      vec![],
      pi(cnst("PN", &[]), cnst("PN", &[])),
      nlam(
        "n",
        cnst("PN", &[]),
        nlam(
          "α",
          sort1(),
          nlam("s", pi(var(0), var(1)), nlam("z", var(1), succ_body)),
        ),
      ),
      ReducibilityHints::Abbrev,
    );
    env.insert(s_id, s_c);

    // PN.add : PN → PN → PN := fun n m α s z => n α s (m α s z)
    // depth 5: z=0, s=1, α=2, m=3, n=4
    let add_body =
      apps(var(4), &[var(2), var(1), apps(var(3), &[var(2), var(1), var(0)])]);
    let (a_id, a_c) = mk_defn(
      "PN.add",
      0,
      vec![],
      pi(cnst("PN", &[]), pi(cnst("PN", &[]), cnst("PN", &[]))),
      nlam(
        "n",
        cnst("PN", &[]),
        nlam(
          "m",
          cnst("PN", &[]),
          nlam(
            "α",
            sort1(),
            nlam("s", pi(var(0), var(1)), nlam("z", var(1), add_body)),
          ),
        ),
      ),
      ReducibilityHints::Abbrev,
    );
    env.insert(a_id, a_c);

    // PN.mul : PN → PN → PN := fun n m α s z => n α (m α s) z
    // depth 5: z=0, s=1, α=2, m=3, n=4
    // m α s = app(app(var(3), var(2)), var(1))
    let mul_body =
      apps(var(4), &[var(2), app(app(var(3), var(2)), var(1)), var(0)]);
    let (m_id, m_c) = mk_defn(
      "PN.mul",
      0,
      vec![],
      pi(cnst("PN", &[]), pi(cnst("PN", &[]), cnst("PN", &[]))),
      nlam(
        "n",
        cnst("PN", &[]),
        nlam(
          "m",
          cnst("PN", &[]),
          nlam(
            "α",
            sort1(),
            nlam("s", pi(var(0), var(1)), nlam("z", var(1), mul_body)),
          ),
        ),
      ),
      ReducibilityHints::Abbrev,
    );
    env.insert(m_id, m_c);

    // Convenience: PN.lit0 .. PN.lit4
    let lit0 = cnst("PN.zero", &[]);
    let lit1 = app(cnst("PN.succ", &[]), lit0.clone());
    let lit2 = app(cnst("PN.succ", &[]), lit1.clone());
    let lit4 =
      app(cnst("PN.succ", &[]), app(cnst("PN.succ", &[]), lit2.clone()));
    for (name, val) in [
      ("PN.lit0", lit0),
      ("PN.lit1", lit1),
      ("PN.lit2", lit2.clone()),
      ("PN.lit4", lit4),
    ] {
      let (id, c) = mk_defn(
        name,
        0,
        vec![],
        cnst("PN", &[]),
        val,
        ReducibilityHints::Abbrev,
      );
      env.insert(id, c);
    }

    add_eq_axioms(&env);
    env
  }

  /// peano1 : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit2 := fun t v => v PN.lit2
  #[test]
  fn good_peano1() {
    let env = peano_env();
    let ty = npi(
      "t",
      pi(cnst("PN", &[]), sort0()),
      npi(
        "v",
        npi("n", cnst("PN", &[]), app(var(1), var(0))),
        app(var(1), cnst("PN.lit2", &[])),
      ),
    );
    let val = nlam(
      "t",
      pi(cnst("PN", &[]), sort0()),
      nlam(
        "v",
        npi("n", cnst("PN", &[]), app(var(1), var(0))),
        app(var(0), cnst("PN.lit2", &[])),
      ),
    );
    let env2 = env;
    let (id, c) = mk_thm("peano1", 0, vec![], ty, val);
    env2.insert(id.clone(), c);
    check_accepts(&env2, &id);
  }

  /// peano2 : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit2 := fun t v => v (PN.add PN.lit1 PN.lit1)
  /// Tests that 1 + 1 reduces to 2 via Church numeral reduction.
  #[test]
  fn good_peano2() {
    let env = peano_env();
    let ty = npi(
      "t",
      pi(cnst("PN", &[]), sort0()),
      npi(
        "v",
        npi("n", cnst("PN", &[]), app(var(1), var(0))),
        app(var(1), cnst("PN.lit2", &[])),
      ),
    );
    // Value uses add lit1 lit1 instead of lit2
    let one_plus_one =
      app(app(cnst("PN.add", &[]), cnst("PN.lit1", &[])), cnst("PN.lit1", &[]));
    let val = nlam(
      "t",
      pi(cnst("PN", &[]), sort0()),
      nlam(
        "v",
        npi("n", cnst("PN", &[]), app(var(1), var(0))),
        app(var(0), one_plus_one),
      ),
    );
    let env2 = env;
    let (id, c) = mk_thm("peano2", 0, vec![], ty, val);
    env2.insert(id.clone(), c);
    check_accepts(&env2, &id);
  }

  /// peano3 : ∀ (t : PN → Prop) (v : (n : PN) → t n), t PN.lit4 := fun t v => v (PN.mul PN.lit2 PN.lit2)
  /// Tests that 2 * 2 reduces to 4 via Church numeral reduction.
  #[test]
  fn good_peano3() {
    let env = peano_env();
    let ty = npi(
      "t",
      pi(cnst("PN", &[]), sort0()),
      npi(
        "v",
        npi("n", cnst("PN", &[]), app(var(1), var(0))),
        app(var(1), cnst("PN.lit4", &[])),
      ),
    );
    let two_times_two =
      app(app(cnst("PN.mul", &[]), cnst("PN.lit2", &[])), cnst("PN.lit2", &[]));
    let val = nlam(
      "t",
      pi(cnst("PN", &[]), sort0()),
      nlam(
        "v",
        npi("n", cnst("PN", &[]), app(var(1), var(0))),
        app(var(0), two_times_two),
      ),
    );
    let env2 = env;
    let (id, c) = mk_thm("peano3", 0, vec![], ty, val);
    env2.insert(id.clone(), c);
    check_accepts(&env2, &id);
  }

  // ==========================================================================
  // Batch 13: Bool inductive + recursor reduction (Tutorial.lean 206, 693)
  // ==========================================================================

  /// Build Bool environment with working recursor rules.
  fn bool_env() -> Arc<KEnv<Meta>> {
    let env = Arc::new(KEnv::<Meta>::new());
    let n = "Bool";
    let block_id = mk_id(n);
    let false_id = mk_id("Bool.false");
    let true_id = mk_id("Bool.true");
    let rec_id = mk_id("Bool.rec");

    // Bool : Type
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
        ctors: vec![false_id.clone(), true_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // Bool.false : Bool
    env.insert(
      false_id.clone(),
      KConst::Ctor {
        name: mk_name("Bool.false"),
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

    // Bool.true : Bool
    env.insert(
      true_id.clone(),
      KConst::Ctor {
        name: mk_name("Bool.true"),
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

    // Bool.rec : ∀ {motive : Bool → Sort u} (false : motive Bool.false) (true : motive Bool.true) (t : Bool), motive t
    let motive_ty = pi(cnst(n, &[]), sort(param(0)));
    let minor_false = app(var(0), cnst("Bool.false", &[]));
    let minor_true = app(var(1), cnst("Bool.true", &[]));
    let rec_ty = ipi(
      "motive",
      motive_ty.clone(),
      npi(
        "false",
        minor_false.clone(),
        npi(
          "true",
          minor_true.clone(),
          npi("t", cnst(n, &[]), app(var(3), var(0))),
        ),
      ),
    );

    // Rule 0 (false): λ motive hf ht, hf
    let rule_false_rhs = nlam(
      "motive",
      motive_ty.clone(),
      nlam("hf", minor_false.clone(), nlam("ht", minor_true.clone(), var(1))),
    );
    // Rule 1 (true): λ motive hf ht, ht
    let rule_true_rhs = nlam(
      "motive",
      motive_ty,
      nlam("hf", minor_false, nlam("ht", minor_true, var(0))),
    );

    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name("Bool.rec"),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          RecRule { ctor: Name::anon(), fields: 0, rhs: rule_false_rhs },
          RecRule { ctor: Name::anon(), fields: 0, rhs: rule_true_rhs },
        ],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id, false_id, true_id, rec_id]);
    add_eq_axioms(&env);
    env
  }

  /// boolRecEqns: Bool.rec false_val true_val false = false_val
  ///           ∧ Bool.rec false_val true_val true  = true_val
  #[test]
  fn good_bool_rec_reduction() {
    let env = bool_env();

    // Test: Bool.rec (motive := fun _ => Bool) Bool.false Bool.true Bool.false = Bool.false
    // i.e., the recursor on false returns the false-case value
    //
    // ∀ {motive : Bool → Sort 1} (hf : motive Bool.false) (ht : motive Bool.true),
    //   Eq.{1} (motive Bool.false) (Bool.rec hf ht Bool.false) hf
    //
    // Simplified: test with concrete motive = fun _ => Bool
    let motive = nlam("_", cnst("Bool", &[]), cnst("Bool", &[])); // fun _ => Bool
    let rec_app = apps(
      cnst("Bool.rec", &[usucc(uzero())]),
      &[
        motive.clone(),
        cnst("Bool.false", &[]), // false case returns Bool.false
        cnst("Bool.true", &[]),  // true case returns Bool.true
        cnst("Bool.false", &[]), // major: false
      ],
    );
    // After reduction: Bool.rec ... false = false-case = Bool.false
    let ty = eq_expr(
      usucc(uzero()),
      cnst("Bool", &[]),
      rec_app,
      cnst("Bool.false", &[]),
    );
    let val =
      eq_refl_expr(usucc(uzero()), cnst("Bool", &[]), cnst("Bool.false", &[]));
    let (id, c) = mk_thm("boolRecFalse", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// Bool.rec on true returns the true-case value
  #[test]
  fn good_bool_rec_reduction_true() {
    let env = bool_env();

    let motive = nlam("_", cnst("Bool", &[]), cnst("Bool", &[]));
    let rec_app = apps(
      cnst("Bool.rec", &[usucc(uzero())]),
      &[
        motive,
        cnst("Bool.false", &[]),
        cnst("Bool.true", &[]),
        cnst("Bool.true", &[]), // major: true
      ],
    );
    let ty = eq_expr(
      usucc(uzero()),
      cnst("Bool", &[]),
      rec_app,
      cnst("Bool.true", &[]),
    );
    let val =
      eq_refl_expr(usucc(uzero()), cnst("Bool", &[]), cnst("Bool.true", &[]));
    let (id, c) = mk_thm("boolRecTrue", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Batch 16: Nat inductive + recursor reduction (Tutorial.lean 231, 710–718)
  // ==========================================================================

  /// Build N (Nat-like) environment with working recursor rules.
  fn nat_env() -> Arc<KEnv<Meta>> {
    let env = Arc::new(KEnv::<Meta>::new());
    let n = "N";
    let block_id = mk_id(n);
    let zero_id = mk_id("N.zero");
    let succ_id = mk_id("N.succ");
    let rec_id = mk_id("N.rec");

    let nat = || cnst(n, &[]);

    // N : Type
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![zero_id.clone(), succ_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // N.zero : N
    env.insert(
      zero_id.clone(),
      KConst::Ctor {
        name: mk_name("N.zero"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: nat(),
      },
    );

    // N.succ : N → N
    env.insert(
      succ_id.clone(),
      KConst::Ctor {
        name: mk_name("N.succ"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: pi(nat(), nat()),
      },
    );

    // N.rec : ∀ {motive : N → Sort u} (zero : motive N.zero)
    //           (succ : ∀ (a : N), motive a → motive a.succ) (t : N), motive t
    let motive_ty = pi(nat(), sort(param(0)));
    let minor_zero = app(var(0), cnst("N.zero", &[]));
    // succ minor: ∀ (a : N) (ih : motive a), motive (N.succ a)
    // depth of succ minor (inside motive binder): motive = var(1)
    // Inside the succ forall: a=var(0), motive=var(2)
    // Inside the ih forall: ih=var(0), a=var(1), motive=var(3)
    let minor_succ = npi(
      "a",
      nat(),
      npi(
        "ih",
        app(var(2), var(0)),
        app(var(3), app(cnst("N.succ", &[]), var(1))),
      ),
    );
    let rec_ty = ipi(
      "motive",
      motive_ty.clone(),
      npi(
        "zero",
        minor_zero.clone(),
        npi("succ", minor_succ.clone(), npi("t", nat(), app(var(3), var(0)))),
      ),
    );

    // Rule 0 (zero, 0 fields): λ motive h_zero h_succ, h_zero
    let rule_zero_rhs = nlam(
      "motive",
      motive_ty.clone(),
      nlam(
        "h_zero",
        minor_zero.clone(),
        nlam("h_succ", minor_succ.clone(), var(1)),
      ),
    );

    // Rule 1 (succ, 1 field): λ motive h_zero h_succ n, h_succ n (N.rec motive h_zero h_succ n)
    // depth 4: n=var(0), h_succ=var(1), h_zero=var(2), motive=var(3)
    let nat_rec = cnst("N.rec", &[param(0)]);
    let ih = apps(nat_rec, &[var(3), var(2), var(1), var(0)]);
    let rule_succ_rhs = nlam(
      "motive",
      motive_ty,
      nlam(
        "h_zero",
        minor_zero,
        nlam(
          "h_succ",
          minor_succ,
          nlam("n", nat(), app(app(var(1), var(0)), ih)),
        ),
      ),
    );

    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name("N.rec"),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          RecRule { ctor: Name::anon(), fields: 0, rhs: rule_zero_rhs },
          RecRule { ctor: Name::anon(), fields: 1, rhs: rule_succ_rhs },
        ],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id, zero_id, succ_id, rec_id]);
    add_eq_axioms(&env);
    env
  }

  /// N.add defined via N.rec:
  /// N.add := N.rec (fun m => m) (fun n ih m => (ih m).succ)
  /// Tests: N.add N.zero m = m  ∧  N.add (N.succ n) m = N.succ (N.add n m)
  #[test]
  fn good_n_rec_reduction() {
    let env = nat_env();

    let nat = || cnst("N", &[]);

    // N.add : N → N → N :=
    //   N.rec.{1} (motive := fun _ => N → N)
    //     (fun m => m)                          -- zero case
    //     (fun n ih m => N.succ (ih m))         -- succ case
    let motive = nlam("_", nat(), pi(nat(), nat())); // fun _ => N → N

    // zero case: fun m => m
    let zero_case = nlam("m", nat(), var(0));

    // succ case: fun n ih m => N.succ (ih m)
    // depth 3: m=var(0), ih=var(1) : N → N, n=var(2) : N
    let succ_case = nlam(
      "n",
      nat(),
      nlam(
        "ih",
        pi(nat(), nat()),
        nlam("m", nat(), app(cnst("N.succ", &[]), app(var(1), var(0)))),
      ),
    );

    let add_val =
      apps(cnst("N.rec", &[usucc(uzero())]), &[motive, zero_case, succ_case]);
    let (add_id, add_c) = mk_defn(
      "N.add",
      0,
      vec![],
      pi(nat(), pi(nat(), nat())),
      add_val,
      ReducibilityHints::Abbrev,
    );
    env.insert(add_id, add_c);

    // Test 1: ∀ m, N.add N.zero m = m
    // N.add N.zero = (N.rec ...) N.zero → reduces zero case → fun m => m
    // So N.add N.zero m = m
    let ty1 = npi(
      "m",
      nat(),
      eq_expr(
        usucc(uzero()),
        nat(),
        app(app(cnst("N.add", &[]), cnst("N.zero", &[])), var(0)),
        var(0),
      ),
    );
    let val1 = nlam("m", nat(), eq_refl_expr(usucc(uzero()), nat(), var(0)));
    let (id1, c1) = mk_thm("nAddZero", 0, vec![], ty1, val1);
    env.insert(id1.clone(), c1);
    check_accepts(&env, &id1);
  }

  /// N.add N.succ reduction: N.add (N.succ n) m = N.succ (N.add n m)
  #[test]
  fn good_n_rec_reduction_succ() {
    let env = nat_env();
    let nat = || cnst("N", &[]);

    let motive = nlam("_", nat(), pi(nat(), nat()));
    let zero_case = nlam("m", nat(), var(0));
    let succ_case = nlam(
      "n",
      nat(),
      nlam(
        "ih",
        pi(nat(), nat()),
        nlam("m", nat(), app(cnst("N.succ", &[]), app(var(1), var(0)))),
      ),
    );

    let add_val =
      apps(cnst("N.rec", &[usucc(uzero())]), &[motive, zero_case, succ_case]);
    let (add_id, add_c) = mk_defn(
      "N.add",
      0,
      vec![],
      pi(nat(), pi(nat(), nat())),
      add_val,
      ReducibilityHints::Abbrev,
    );
    env.insert(add_id, add_c);

    // Test 2: ∀ n m, N.add (N.succ n) m = N.succ (N.add n m)
    // depth 2: n=var(1), m=var(0)
    let lhs =
      app(app(cnst("N.add", &[]), app(cnst("N.succ", &[]), var(1))), var(0));
    let rhs =
      app(cnst("N.succ", &[]), app(app(cnst("N.add", &[]), var(1)), var(0)));
    let ty2 = npi(
      "n",
      nat(),
      npi("m", nat(), eq_expr(usucc(uzero()), nat(), lhs, rhs)),
    );
    let val2 = nlam(
      "n",
      nat(),
      nlam(
        "m",
        nat(),
        eq_refl_expr(
          usucc(uzero()),
          nat(),
          app(
            cnst("N.succ", &[]),
            app(app(cnst("N.add", &[]), var(1)), var(0)),
          ),
        ),
      ),
    );
    let (id2, c2) = mk_thm("nAddSucc", 0, vec![], ty2, val2);
    env.insert(id2.clone(), c2);
    check_accepts(&env, &id2);
  }

  // ==========================================================================
  // RTree: reflexive inductive (Tutorial.lean 1145–1159)
  // ==========================================================================

  /// Build an environment with Bool + RTree (reflexive inductive).
  /// RTree : Type, RTree.leaf : RTree, RTree.node : (Bool → RTree) → RTree
  fn rtree_env() -> Arc<KEnv<Meta>> {
    let env = bool_env();

    let n = "RTree";
    let block_id = mk_id(n);
    let leaf_id = mk_id("RTree.leaf");
    let node_id = mk_id("RTree.node");
    let rec_id = mk_id("RTree.rec");

    let rt = || cnst(n, &[]);

    // RTree : Type
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: true,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![leaf_id.clone(), node_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // RTree.leaf : RTree
    env.insert(
      leaf_id.clone(),
      KConst::Ctor {
        name: mk_name("RTree.leaf"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: rt(),
      },
    );

    // RTree.node : (Bool → RTree) → RTree
    env.insert(
      node_id.clone(),
      KConst::Ctor {
        name: mk_name("RTree.node"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: block_id.clone(),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: npi("children", pi(cnst("Bool", &[]), rt()), rt()),
      },
    );

    // RTree.rec : ∀ {motive : RTree → Sort u}
    //   (leaf : motive RTree.leaf)
    //   (node : ∀ (children : Bool → RTree), (∀ b, motive (children b)) → motive (RTree.node children))
    //   (t : RTree), motive t
    let motive_ty = pi(rt(), sort(param(0)));
    // depth 1 (inside motive): motive = var(0)
    let minor_leaf = app(var(0), cnst("RTree.leaf", &[]));
    // minor_node at depth 2 (inside motive, leaf): motive = var(1)
    // ∀ (children : Bool → RTree), (∀ b, motive (children b)) → motive (RTree.node children)
    // depth 3 (inside children): children = var(0), motive = var(2)
    // ih: ∀ (b : Bool), motive (children b) — depth 4: b=var(0), children=var(1), motive=var(3)
    let ih_ty = npi("b", cnst("Bool", &[]), app(var(3), app(var(1), var(0))));
    // depth 4 (inside ih): ih=var(0), children=var(1), motive=var(3)
    let node_result = app(var(3), app(cnst("RTree.node", &[]), var(1)));
    let minor_node =
      npi("children", pi(cnst("Bool", &[]), rt()), pi(ih_ty, node_result));
    let rec_ty = ipi(
      "motive",
      motive_ty.clone(),
      npi(
        "leaf",
        minor_leaf.clone(),
        npi("node", minor_node.clone(), npi("t", rt(), app(var(3), var(0)))),
      ),
    );

    // Rule 0 (leaf, 0 fields): λ motive h_leaf h_node, h_leaf
    let rule_leaf_rhs = nlam(
      "motive",
      motive_ty.clone(),
      nlam(
        "h_leaf",
        minor_leaf.clone(),
        nlam("h_node", minor_node.clone(), var(1)),
      ),
    );

    // Rule 1 (node, 1 field): λ motive h_leaf h_node children,
    //   h_node children (fun b => RTree.rec motive h_leaf h_node (children b))
    // depth 4: children=var(0), h_node=var(1), h_leaf=var(2), motive=var(3)
    let rec_call_ih = nlam(
      "b",
      cnst("Bool", &[]),
      // depth 5: b=var(0), children=var(1), h_node=var(2), h_leaf=var(3), motive=var(4)
      apps(
        cnst("RTree.rec", &[param(0)]),
        &[var(4), var(3), var(2), app(var(1), var(0))],
      ),
    );
    let rule_node_rhs = nlam(
      "motive",
      motive_ty,
      nlam(
        "h_leaf",
        minor_leaf,
        nlam(
          "h_node",
          minor_node,
          nlam(
            "children",
            pi(cnst("Bool", &[]), rt()),
            app(app(var(1), var(0)), rec_call_ih),
          ),
        ),
      ),
    );

    env.insert(
      rec_id.clone(),
      KConst::Recr {
        name: mk_name("RTree.rec"),
        level_params: vec![mk_name("u")],
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          RecRule { ctor: Name::anon(), fields: 0, rhs: rule_leaf_rhs },
          RecRule { ctor: Name::anon(), fields: 1, rhs: rule_node_rhs },
        ],
        lean_all: vec![block_id.clone()],
      },
    );

    env
      .blocks
      .insert(block_id.clone(), vec![block_id, leaf_id, node_id, rec_id]);
    env
  }

  /// RTree.left : RTree → RTree :=
  ///   RTree.rec .leaf (fun children _ih => children true) t
  /// rtreeRecReduction : ∀ (t1 t2 : RTree), (RTree.node (Bool.rec t2 t1)).left = t1
  #[test]
  fn good_rtree_rec_reduction() {
    let env = rtree_env();

    let rt = || cnst("RTree", &[]);

    // RTree.left : RTree → RTree :=
    //   fun t => RTree.rec (motive := fun _ => RTree) .leaf
    //     (fun children _ih => children true) t
    let motive = nlam("_", rt(), rt());
    let leaf_case = cnst("RTree.leaf", &[]);
    // node case: fun children ih => children Bool.true
    // depth 2: ih=var(0), children=var(1)
    let ih_ty = npi("b", cnst("Bool", &[]), rt()); // simplified: ∀ b, RTree
    let node_case = nlam(
      "children",
      pi(cnst("Bool", &[]), rt()),
      nlam("_ih", ih_ty, app(var(1), cnst("Bool.true", &[]))),
    );

    let left_val = nlam(
      "t",
      rt(),
      apps(
        cnst("RTree.rec", &[usucc(uzero())]),
        &[motive, leaf_case, node_case, var(0)],
      ),
    );
    let (left_id, left_c) = mk_defn(
      "RTree.left",
      0,
      vec![],
      pi(rt(), rt()),
      left_val,
      ReducibilityHints::Abbrev,
    );
    env.insert(left_id, left_c);

    // Test: ∀ (t1 t2 : RTree), (RTree.node (Bool.rec t2 t1)).left = t1
    // Bool.rec.{1} (fun _ => RTree) t2 t1 : Bool → RTree
    // Then RTree.node applied to this, then .left
    // depth 2: t1=var(1), t2=var(0)... wait, t1 first then t2:
    // ∀ (t1 : RTree) (t2 : RTree), ...
    // depth 2: t2=var(0), t1=var(1)
    let bool_rec_app = apps(
      cnst("Bool.rec", &[usucc(uzero())]),
      &[
        nlam("_", cnst("Bool", &[]), rt()), // motive: fun _ => RTree
        var(0),                             // false case = t2
        var(1),                             // true case = t1
      ],
    );
    // RTree.node (Bool.rec ...) : RTree
    let node_app = app(cnst("RTree.node", &[]), bool_rec_app);
    // RTree.left (RTree.node ...) should reduce to t1
    let lhs = app(cnst("RTree.left", &[]), node_app);
    let ty = npi(
      "t1",
      rt(),
      npi("t2", rt(), eq_expr(usucc(uzero()), rt(), lhs, var(1))),
    );
    let val = nlam(
      "t1",
      rt(),
      nlam("t2", rt(), eq_refl_expr(usucc(uzero()), rt(), var(1))),
    );

    let (id, c) = mk_thm("rtreeRecReduction", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Nat literal tests (Tutorial.lean 930–951)
  // ==========================================================================

  /// aNatLit : Nat := .lit (.natVal 0)
  /// Type checking a Nat literal — needs Primitives wired up.
  #[test]
  fn good_nat_lit() {
    let env = nat_env();
    let nat = || cnst("N", &[]);

    // We need to use the actual Nat type for nat literals.
    // The zero kernel's infer_nat_type uses prims.nat to construct the type.
    // We use N as our Nat, so we need prims.nat = mk_id("N").
    // aNatLit : N := NatVal(0)
    use crate::ix::address::Address;
    use lean_ffi::nat::Nat;
    let nat_0 = ME::nat(Nat::from(0u64), Address::hash(b"natval_0"));
    let (id, c) =
      mk_defn("aNatLit", 0, vec![], nat(), nat_0, ReducibilityHints::Opaque);
    env.insert(id.clone(), c);
    let mut prims = test_prims(&env);
    prims.nat = mk_id("N");
    prims.nat_zero = mk_id("N.zero");
    prims.nat_succ = mk_id("N.succ");
    check_accepts_with_prims(&env, &id, prims);
  }

  /// natLitEq : Eq N 3 (N.succ (N.succ (N.succ N.zero))) := Eq.refl 3
  /// Nat literal 3 must reduce to succ(succ(succ(zero))).
  #[test]
  fn good_nat_lit_eq() {
    let env = nat_env();
    let nat = || cnst("N", &[]);

    use crate::ix::address::Address;
    use lean_ffi::nat::Nat;

    let nat_3 = ME::nat(Nat::from(3u64), Address::hash(b"natval_3"));
    let succ_succ_succ_zero = app(
      cnst("N.succ", &[]),
      app(cnst("N.succ", &[]), app(cnst("N.succ", &[]), cnst("N.zero", &[]))),
    );

    // Eq.{1} N 3 (succ (succ (succ zero)))
    let ty = eq_expr(usucc(uzero()), nat(), nat_3.clone(), succ_succ_succ_zero);
    // Eq.refl.{1} N 3
    let val = eq_refl_expr(usucc(uzero()), nat(), nat_3);

    let (id, c) = mk_thm("natLitEq", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    let mut prims = test_prims(&env);
    prims.nat = mk_id("N");
    prims.nat_zero = mk_id("N.zero");
    prims.nat_succ = mk_id("N.succ");
    check_accepts_with_prims(&env, &id, prims);
  }

  // ==========================================================================
  // Prod + projection reduction (Tutorial.lean 701–705, 902–903)
  // ==========================================================================

  /// Build Prod.{u,v} : Type u → Type v → Type (max u v) environment.
  fn prod_env() -> Arc<KEnv<Meta>> {
    let env = Arc::new(KEnv::<Meta>::new());
    add_eq_axioms(&env);

    // Also need Bool for projection tests
    let bool_id = mk_id("Bool");
    let false_id = mk_id("Bool.false");
    let true_id = mk_id("Bool.true");
    env.insert(
      bool_id.clone(),
      KConst::Indc {
        name: mk_name("Bool"),
        level_params: vec![],
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: bool_id.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![false_id.clone(), true_id.clone()],
        lean_all: vec![bool_id.clone()],
      },
    );
    env.insert(
      false_id.clone(),
      KConst::Ctor {
        name: mk_name("Bool.false"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: bool_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: cnst("Bool", &[]),
      },
    );
    env.insert(
      true_id.clone(),
      KConst::Ctor {
        name: mk_name("Bool.true"),
        level_params: vec![],
        is_unsafe: false,
        lvls: 0,
        induct: bool_id.clone(),
        cidx: 1,
        params: 0,
        fields: 0,
        ty: cnst("Bool", &[]),
      },
    );
    env.blocks.insert(bool_id, vec![mk_id("Bool"), false_id, true_id]);

    let n = "Prod";
    let block_id = mk_id(n);
    let mk_ctor_id = mk_id("Prod.mk");
    let rec_ctor_id = mk_id("Prod.rec");

    // Prod.{u,v} : Type u → Type v → Type (max u v)
    // param(0) = u, param(1) = v
    let prod_ty = npi(
      "α",
      sort(usucc(param(0))),
      npi("β", sort(usucc(param(1))), sort(usucc(umax(param(0), param(1))))),
    );
    env.insert(
      block_id.clone(),
      KConst::Indc {
        name: mk_name(n),
        level_params: vec![mk_name("u"), mk_name("v")],
        lvls: 2,
        params: 2,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_id.clone(),
        member_idx: 0,
        ty: prod_ty,
        ctors: vec![mk_ctor_id.clone()],
        lean_all: vec![block_id.clone()],
      },
    );

    // Prod.mk.{u,v} : {α : Type u} → {β : Type v} → α → β → Prod α β
    // depth 2 (inside α, β implicit): α=var(1), β=var(0)
    // depth 4 (inside fst, snd): fst=var(1), snd=var(0), β=var(2), α=var(3)
    let mk_ty = ipi(
      "α",
      sort(usucc(param(0))),
      ipi(
        "β",
        sort(usucc(param(1))),
        npi(
          "fst",
          var(1),
          npi(
            "snd",
            var(1),
            app(app(cnst(n, &[param(0), param(1)]), var(3)), var(2)),
          ),
        ),
      ),
    );
    env.insert(
      mk_ctor_id.clone(),
      KConst::Ctor {
        name: mk_name("Prod.mk"),
        level_params: vec![mk_name("u"), mk_name("v")],
        is_unsafe: false,
        lvls: 2,
        induct: block_id.clone(),
        cidx: 0,
        params: 2,
        fields: 2,
        ty: mk_ty,
      },
    );

    // Prod.rec.{u,v,w} with k=true (structure)
    // ∀ {α : Type u} {β : Type v} {motive : Prod α β → Sort w}
    //   (mk : ∀ (fst : α) (snd : β), motive (Prod.mk fst snd))
    //   (t : Prod α β), motive t
    //
    // d2 (inside α, β): α=var(1), β=var(0)
    let prod_ab_d2 = app(app(cnst(n, &[param(0), param(1)]), var(1)), var(0));
    let motive_ty = pi(prod_ab_d2, sort(param(2)));
    // d3 (inside motive): motive=var(0), β=var(1), α=var(2)
    // minor mk: ∀ (fst : α) (snd : β), motive (Prod.mk fst snd)
    // d5 (inside fst, snd): snd=var(0), fst=var(1), motive=var(2), β=var(3), α=var(4)
    let mk_app = apps(
      cnst("Prod.mk", &[param(0), param(1)]),
      &[var(4), var(3), var(1), var(0)],
    );
    let minor_mk = npi("fst", var(2), npi("snd", var(2), app(var(2), mk_app)));
    // d4 (inside mk): mk=var(0), motive=var(1), β=var(2), α=var(3)
    let prod_ab_d4 = app(app(cnst(n, &[param(0), param(1)]), var(3)), var(2));
    // d5 (inside t): t=var(0), mk=var(1), motive=var(2), β=var(3), α=var(4)
    let rec_ty = ipi(
      "α",
      sort(usucc(param(0))),
      ipi(
        "β",
        sort(usucc(param(1))),
        ipi(
          "motive",
          motive_ty,
          npi(
            "mk",
            minor_mk.clone(),
            npi("t", prod_ab_d4, app(var(2), var(0))),
          ),
        ),
      ),
    );

    // Rule: Prod.mk case (2 fields)
    // rhs: λ {α} {β} (motive) (mk_case) (fst) (snd), mk_case fst snd
    // depth 6: snd=var(0), fst=var(1), mk_case=var(2), motive=var(3), β=var(4), α=var(5)
    let prod_ab_r = app(app(cnst(n, &[param(0), param(1)]), var(1)), var(0));
    let motive_ty_r = pi(prod_ab_r, sort(param(2)));
    let mk_app_r = apps(
      cnst("Prod.mk", &[param(0), param(1)]),
      &[var(4), var(3), var(1), var(0)],
    );
    let minor_mk_r =
      npi("fst", var(2), npi("snd", var(2), app(var(2), mk_app_r)));
    // rhs: λ {α} {β} motive mk_case fst snd, mk_case fst snd
    // d4 (after α,β,motive,mk_case): mk_case=0, motive=1, β=2, α=3
    //   fst domain: α = var(3)
    // d5 (after fst): fst=0, mk_case=1, motive=2, β=3, α=4
    //   snd domain: β = var(3)
    // d6 (body): snd=0, fst=1, mk_case=2, motive=3, β=4, α=5
    //   mk_case fst snd = app(app(var(2), var(1)), var(0))
    let rule_rhs = ME::lam(
      mk_name("α"),
      crate::ix::env::BinderInfo::Implicit,
      sort(usucc(param(0))),
      ME::lam(
        mk_name("β"),
        crate::ix::env::BinderInfo::Implicit,
        sort(usucc(param(1))),
        nlam(
          "motive",
          motive_ty_r,
          nlam(
            "mk_case",
            minor_mk_r,
            nlam(
              "fst",
              var(3),
              nlam("snd", var(3), app(app(var(2), var(1)), var(0))),
            ),
          ),
        ),
      ),
    );

    env.insert(
      rec_ctor_id.clone(),
      KConst::Recr {
        name: mk_name("Prod.rec"),
        level_params: vec![mk_name("u"), mk_name("v"), mk_name("w")],
        k: true,
        is_unsafe: false,
        lvls: 3,
        params: 2,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block_id.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![RecRule { ctor: Name::anon(), fields: 2, rhs: rule_rhs }],
        lean_all: vec![block_id.clone()],
      },
    );

    env.blocks.insert(block_id, vec![mk_id("Prod"), mk_ctor_id, rec_ctor_id]);
    env
  }

  /// projRed : (Prod.mk true false).2 = false
  /// Projection .proj Prod 1 (Prod.mk true false) reduces to false.
  #[test]
  fn good_proj_red() {
    let env = prod_env();

    // Prod.mk.{0,0} Bool Bool true false : Prod Bool Bool
    let pair = apps(
      cnst("Prod.mk", &[uzero(), uzero()]),
      &[
        cnst("Bool", &[]),
        cnst("Bool", &[]),
        cnst("Bool.true", &[]),
        cnst("Bool.false", &[]),
      ],
    );
    // .proj Prod 1 pair = false
    let proj = ME::prj(mk_id("Prod"), 1, pair);
    // Eq.{1} Bool (.proj Prod 1 (mk true false)) false
    let ty =
      eq_expr(usucc(uzero()), cnst("Bool", &[]), proj, cnst("Bool.false", &[]));
    let val =
      eq_refl_expr(usucc(uzero()), cnst("Bool", &[]), cnst("Bool.false", &[]));

    let (id, c) = mk_thm("projRed", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// structEta : ∀ (x : Prod Bool Bool), x = Prod.mk (.proj Prod 0 x) (.proj Prod 1 x)
  /// Structure eta: a value of a structure type equals the constructor applied to its projections.
  #[test]
  fn good_struct_eta() {
    let env = prod_env();

    let prod_bb = app(
      app(cnst("Prod", &[uzero(), uzero()]), cnst("Bool", &[])),
      cnst("Bool", &[]),
    );

    // depth 1: x=var(0) : Prod Bool Bool
    let proj0 = ME::prj(mk_id("Prod"), 0, var(0));
    let proj1 = ME::prj(mk_id("Prod"), 1, var(0));
    let reconstructed = apps(
      cnst("Prod.mk", &[uzero(), uzero()]),
      &[cnst("Bool", &[]), cnst("Bool", &[]), proj0, proj1],
    );

    // ∀ (x : Prod Bool Bool), Eq.{1} (Prod Bool Bool) x (Prod.mk (x.1) (x.2))
    let ty = npi(
      "x",
      prod_bb.clone(),
      eq_expr(usucc(uzero()), prod_bb.clone(), var(0), reconstructed),
    );

    // fun x => Eq.refl.{1} (Prod Bool Bool) x
    let val =
      nlam("x", prod_bb.clone(), eq_refl_expr(usucc(uzero()), prod_bb, var(0)));

    let (id, c) = mk_thm("structEta", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  /// prodRecEqns: Prod.rec f (Prod.mk true false) = f true false = true
  #[test]
  fn good_prod_rec_reduction() {
    let env = prod_env();
    let u1 = usucc(uzero());

    let prod_bb = app(
      app(cnst("Prod", &[uzero(), uzero()]), cnst("Bool", &[])),
      cnst("Bool", &[]),
    );
    let motive = nlam("_", prod_bb, cnst("Bool", &[]));
    let f_case =
      nlam("a", cnst("Bool", &[]), nlam("b", cnst("Bool", &[]), var(1)));
    let pair = apps(
      cnst("Prod.mk", &[uzero(), uzero()]),
      &[
        cnst("Bool", &[]),
        cnst("Bool", &[]),
        cnst("Bool.true", &[]),
        cnst("Bool.false", &[]),
      ],
    );
    let rec_app = apps(
      cnst("Prod.rec", &[uzero(), uzero(), u1.clone()]),
      &[cnst("Bool", &[]), cnst("Bool", &[]), motive, f_case, pair],
    );
    let ty =
      eq_expr(u1.clone(), cnst("Bool", &[]), rec_app, cnst("Bool.true", &[]));
    let val = eq_refl_expr(u1, cnst("Bool", &[]), cnst("Bool.true", &[]));

    let (id, c) = mk_thm("prodRecEqns", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts(&env, &id);
  }

  // ==========================================================================
  // Quotient tests (Tutorial.lean 1185–1224)
  // ==========================================================================

  /// Add Eq as a full inductive (not just axioms) — needed for Quot.lift validation.
  fn add_eq_inductive(env: &KEnv<Meta>) {
    let eq_id = mk_id("Eq");
    let refl_id = mk_id("Eq.refl");
    let eq_rec_id = mk_id("Eq.rec");

    let eq_ty =
      ipi("α", sort(param(0)), npi("a", var(0), npi("b", var(1), sort0())));
    env.insert(
      eq_id.clone(),
      KConst::Indc {
        name: mk_name("Eq"),
        level_params: vec![mk_name("u")],
        lvls: 1,
        params: 2,
        indices: 1,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: eq_id.clone(),
        member_idx: 0,
        ty: eq_ty,
        ctors: vec![refl_id.clone()],
        lean_all: vec![eq_id.clone()],
      },
    );

    let eq_refl_ty = ipi(
      "α",
      sort(param(0)),
      npi(
        "a",
        var(0),
        apps(cnst("Eq", &[param(0)]), &[var(1), var(0), var(0)]),
      ),
    );
    env.insert(
      refl_id.clone(),
      KConst::Ctor {
        name: mk_name("Eq.refl"),
        level_params: vec![mk_name("u")],
        is_unsafe: false,
        lvls: 1,
        induct: eq_id.clone(),
        cidx: 0,
        params: 2,
        fields: 0,
        ty: eq_refl_ty,
      },
    );

    // Minimal Eq.rec (k=true)
    let eq_a_aprime = apps(cnst("Eq", &[param(1)]), &[var(2), var(1), var(0)]);
    let motive_ty = npi("a'", var(1), pi(eq_a_aprime, sort(param(0))));
    let eq_refl_a = apps(cnst("Eq.refl", &[param(1)]), &[var(2), var(1)]);
    let minor_refl = app(app(var(0), var(1)), eq_refl_a);
    let eq_a_aprime_d5 =
      apps(cnst("Eq", &[param(1)]), &[var(4), var(3), var(0)]);
    let result = app(app(var(3), var(1)), var(0));
    let eq_rec_ty = ipi(
      "α",
      sort(param(1)),
      ipi(
        "a",
        var(0),
        ipi(
          "motive",
          motive_ty,
          npi(
            "refl",
            minor_refl,
            ipi("a'", var(3), npi("t", eq_a_aprime_d5, result)),
          ),
        ),
      ),
    );
    env.insert(
      eq_rec_id.clone(),
      KConst::Recr {
        name: mk_name("Eq.rec"),
        level_params: vec![mk_name("u"), mk_name("u_1")],
        k: true,
        is_unsafe: false,
        lvls: 2,
        params: 2,
        indices: 1,
        motives: 1,
        minors: 1,
        block: eq_id.clone(),
        member_idx: 0,
        ty: eq_rec_ty,
        rules: vec![],
        lean_all: vec![eq_id.clone()],
      },
    );
    env.blocks.insert(eq_id, vec![mk_id("Eq"), refl_id, eq_rec_id]);
  }

  /// Build Quot environment: Quot, Quot.mk, Quot.lift, Quot.ind as KConst::Quot.
  /// Also includes Eq as full inductive (needed for Quot.lift validation).
  fn quot_env() -> Arc<KEnv<Meta>> {
    let env = Arc::new(KEnv::<Meta>::new());
    add_eq_inductive(&env);

    use crate::ix::env::QuotKind;

    // Quot.{u} : {α : Sort u} → (α → α → Prop) → Sort u
    // depth 1 (inside α): α = var(0)
    let quot_ty = ipi(
      "α",
      sort(param(0)),
      pi(pi(var(0), pi(var(1), sort0())), sort(param(0))),
    );
    env.insert(
      mk_id("Quot"),
      KConst::Quot {
        name: mk_name("Quot"),
        level_params: vec![mk_name("u")],
        kind: QuotKind::Type,
        lvls: 1,
        ty: quot_ty,
      },
    );

    // Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot r
    // depth 2 (inside α, r): α=var(1), r=var(0)
    // depth 3 (inside a): a=var(0), r=var(1), α=var(2)
    //   Quot α r = app(app(Quot.{u}, var(2)), var(1))
    let quot_mk_ty = ipi(
      "α",
      sort(param(0)),
      npi(
        "r",
        pi(var(0), pi(var(1), sort0())),
        npi("a", var(1), app(app(cnst("Quot", &[param(0)]), var(2)), var(1))),
      ),
    );
    env.insert(
      mk_id("Quot.mk"),
      KConst::Quot {
        name: mk_name("Quot.mk"),
        level_params: vec![mk_name("u")],
        kind: QuotKind::Ctor,
        lvls: 1,
        ty: quot_mk_ty,
      },
    );

    // Quot.lift.{u,v} :
    //   {α : Sort u} → {r : α → α → Prop} → {β : Sort v} →
    //   (f : α → β) → (h : ∀ a b, r a b → f a = f b) → Quot r → β
    //
    // d0: α
    // d1: r. α=var(0)
    // d2: β. r=var(0), α=var(1)
    // d3: f. β=var(0), r=var(1), α=var(2). f : α → β = pi(var(2), var(1))
    //   Inside f's pi: var(0)=arg, var(1)=β, var(2)=r, var(3)=α. body=var(1)=β ✓
    // d4: h. f=var(0), β=var(1), r=var(2), α=var(3)
    //   h : ∀ (a b : α), r a b → Eq.{v} β (f a) (f b)
    //   d5: a. a=var(0), f=var(1), β=var(2), r=var(3), α=var(4)
    //   d6: b. b=var(0), a=var(1), f=var(2), β=var(3), r=var(4), α=var(5)
    //     r a b = app(app(var(4), var(1)), var(0))
    //     d7: (inside r a b →)
    //       f a = app(var(3), var(2)), f b = app(var(3), var(1))
    //       Eq.{v} β (f a) (f b) = eq_expr(param(1), var(4), app(var(3), var(2)), app(var(3), var(1)))
    //   h_ty = npi("a", var(3), npi("b", var(4),
    //     pi(app(app(var(4), var(1)), var(0)),
    //       eq_expr(param(1), var(4), app(var(3), var(2)), app(var(3), var(1))))))
    // d5: (inside h). h=var(0), f=var(1), β=var(2), r=var(3), α=var(4)
    //   Quot r → β: pi(Quot α r, β)
    //   Quot α r = app(app(Quot.{u}, var(4)), var(3))
    //   d6: (inside pi) β = var(3)
    let f_ty = pi(var(2), var(1)); // α → β at d3
    let h_ty = npi(
      "a",
      var(3),
      npi(
        "b",
        var(4),
        pi(
          app(app(var(4), var(1)), var(0)),
          eq_expr(param(1), var(4), app(var(3), var(2)), app(var(3), var(1))),
        ),
      ),
    );
    let _quot_r_3 = (); // unused, remove old
    let quot_lift_ty = ipi(
      "α",
      sort(param(0)),
      ipi(
        "r",
        pi(var(0), pi(var(1), sort0())),
        ipi(
          "β",
          sort(param(1)),
          npi(
            "f",
            f_ty,
            npi(
              "h",
              h_ty,
              pi(app(app(cnst("Quot", &[param(0)]), var(4)), var(3)), var(3)),
            ),
          ),
        ),
      ),
    );
    env.insert(
      mk_id("Quot.lift"),
      KConst::Quot {
        name: mk_name("Quot.lift"),
        level_params: vec![mk_name("u"), mk_name("v")],
        kind: QuotKind::Lift,
        lvls: 2,
        ty: quot_lift_ty,
      },
    );

    // Quot.ind.{u} :
    //   {α : Sort u} → {r : α → α → Prop} → {β : Quot r → Prop} →
    //   (mk : ∀ a, β (Quot.mk r a)) → (q : Quot r) → β q
    //
    // d0: α
    // d1: r. α=var(0)
    // d2: β. r=var(0), α=var(1). β : Quot α r → Prop
    //   Quot α r at d2 = app(app(Quot.{u}, var(1)), var(0))
    let quot_r_d2 = app(app(cnst("Quot", &[param(0)]), var(1)), var(0));
    let beta_ty = pi(quot_r_d2, sort0());
    // d3: mk. β=var(0), r=var(1), α=var(2)
    //   mk : ∀ (a : α), β (Quot.mk r a)
    //   d4: a. a=var(0), β=var(1), r=var(2), α=var(3)
    //     Quot.mk.{u} α r a = apps(Quot.mk, [var(3), var(2), var(0)])
    let quot_mk_r_a =
      apps(cnst("Quot.mk", &[param(0)]), &[var(3), var(2), var(0)]);
    let mk_minor = npi("a", var(2), app(var(1), quot_mk_r_a));
    // d4: q. mk=var(0), β=var(1), r=var(2), α=var(3)
    //   Quot α r at d4 = app(app(Quot.{u}, var(3)), var(2))
    let quot_r_d4 = app(app(cnst("Quot", &[param(0)]), var(3)), var(2));
    // d5: (inside q). q=var(0), mk=var(1), β=var(2), r=var(3), α=var(4)
    let result = app(var(2), var(0)); // β q
    let quot_ind_ty = ipi(
      "α",
      sort(param(0)),
      ipi(
        "r",
        pi(var(0), pi(var(1), sort0())),
        ipi("β", beta_ty, npi("mk", mk_minor, npi("q", quot_r_d4, result))),
      ),
    );
    env.insert(
      mk_id("Quot.ind"),
      KConst::Quot {
        name: mk_name("Quot.ind"),
        level_params: vec![mk_name("u")],
        kind: QuotKind::Ind,
        lvls: 1,
        ty: quot_ind_ty,
      },
    );

    env
  }

  fn quot_prims(
    env: &KEnv<Meta>,
  ) -> crate::ix::kernel::primitive::Primitives<Meta> {
    let mut prims = test_prims(env);
    prims.quot_type = mk_id("Quot");
    prims.quot_ctor = mk_id("Quot.mk");
    prims.quot_lift = mk_id("Quot.lift");
    prims.quot_ind = mk_id("Quot.ind");
    prims.eq = mk_id("Eq");
    prims.eq_refl = mk_id("Eq.refl");
    prims
  }

  /// quotMkType: type assertion for Quot.mk
  #[test]
  fn good_quot_mk_type() {
    let env = quot_env();
    check_accepts_with_prims(&env, &mk_id("Quot.mk"), quot_prims(&env));
  }

  /// quotLiftType: type assertion for Quot.lift
  #[test]
  fn good_quot_lift_type() {
    let env = quot_env();
    check_accepts_with_prims(&env, &mk_id("Quot.lift"), quot_prims(&env));
  }

  /// quotIndType: type assertion for Quot.ind
  #[test]
  fn good_quot_ind_type() {
    let env = quot_env();
    check_accepts_with_prims(&env, &mk_id("Quot.ind"), quot_prims(&env));
  }

  /// quotLiftReduction: Quot.lift f h (Quot.mk r a) = f a
  #[test]
  fn good_quot_lift_reduction() {
    let env = quot_env();
    let prims = quot_prims(&env);

    // We need a concrete type for testing. Use Bool (as axiom).
    let (bool_id, bool_c) = mk_axiom("Bool", 0, vec![], sort1());
    env.insert(bool_id, bool_c);
    let (true_id, true_c) = mk_axiom("Bool.true", 0, vec![], cnst("Bool", &[]));
    env.insert(true_id, true_c);

    // r : Bool → Bool → Prop (axiom)
    let (r_id, r_c) = mk_axiom(
      "r",
      0,
      vec![],
      pi(cnst("Bool", &[]), pi(cnst("Bool", &[]), sort0())),
    );
    env.insert(r_id, r_c);

    // f : Bool → Bool (axiom)
    let (f_id, f_c) =
      mk_axiom("f", 0, vec![], pi(cnst("Bool", &[]), cnst("Bool", &[])));
    env.insert(f_id, f_c);

    // h : ∀ (a b : Bool), r a b → Eq.{1} Bool (f a) (f b)
    // d0: a. a=var(0)
    // d1: b. b=var(0), a=var(1)
    //   r a b (pi domain at d2): r=cnst, a=var(1), b=var(0) ✓
    // d2: (inside pi for r a b →). proof=var(0), b=var(1), a=var(2)
    //   Eq.{1} Bool (f a) (f b): f a = app(f, var(2)), f b = app(f, var(1))
    let r_ab = app(app(cnst("r", &[]), var(1)), var(0));
    let h_ty = npi(
      "a",
      cnst("Bool", &[]),
      npi(
        "b",
        cnst("Bool", &[]),
        pi(
          r_ab,
          eq_expr(
            usucc(uzero()),
            cnst("Bool", &[]),
            app(cnst("f", &[]), var(2)), // f a — a is var(2) at depth 3
            app(cnst("f", &[]), var(1)),
          ), // f b — b is var(1) at depth 3
        ),
      ),
    );
    let (h_id, h_c) = mk_axiom("h", 0, vec![], h_ty);
    env.insert(h_id, h_c);

    // Quot.lift f h (Quot.mk r Bool.true) = f Bool.true
    let quot_mk_app = apps(
      cnst("Quot.mk", &[usucc(uzero())]),
      &[cnst("Bool", &[]), cnst("r", &[]), cnst("Bool.true", &[])],
    );
    let lift_app = apps(
      cnst("Quot.lift", &[usucc(uzero()), usucc(uzero())]),
      &[
        cnst("Bool", &[]), // α
        cnst("r", &[]),    // r
        cnst("Bool", &[]), // β
        cnst("f", &[]),    // f
        cnst("h", &[]),    // h
        quot_mk_app,       // Quot.mk r Bool.true
      ],
    );
    let f_true = app(cnst("f", &[]), cnst("Bool.true", &[]));

    // Eq.{1} Bool (Quot.lift f h (Quot.mk r true)) (f true)
    let ty =
      eq_expr(usucc(uzero()), cnst("Bool", &[]), lift_app, f_true.clone());
    let val = eq_refl_expr(usucc(uzero()), cnst("Bool", &[]), f_true);

    let (id, c) = mk_thm("quotLiftReduction", 0, vec![], ty, val);
    env.insert(id.clone(), c);
    check_accepts_with_prims(&env, &id, prims);
  }
}
