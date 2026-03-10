//! Unit tests for Kernel2 NbE type checker.
//!
//! These tests mirror the Lean tests in `Tests/Ix/Kernel2/Unit.lean`.
//! They use synthetic environments (no IO, no Ixon loading) to test
//! eval, quote, whnf, isDefEq, infer, and type-checking.

#[cfg(test)]
mod tests {
  use rustc_hash::FxHashMap;

  use crate::ix::address::Address;
  use crate::ix::env::{
    BinderInfo, DefinitionSafety, Literal, QuotKind, ReducibilityHints,
  };
  use crate::ix::kernel::tc::TypeChecker;
  use crate::ix::kernel::types::*;
  use crate::ix::kernel::value::{Head, ValInner};
  use crate::lean::nat::Nat;

  // ==========================================================================
  // Helpers
  // ==========================================================================

  fn mk_addr(seed: u16) -> Address {
    Address::hash(&[seed as u8, (seed >> 8) as u8, 0xAA, 0xBB])
  }

  fn anon() -> Name {
    Name::anon()
  }

  fn bv(n: usize) -> KExpr<Meta> {
    KExpr::bvar(n, anon())
  }
  fn level_of_nat(n: u32) -> KLevel<Meta> {
    let mut l = KLevel::zero();
    for _ in 0..n {
      l = KLevel::succ(l);
    }
    l
  }
  fn srt(n: u32) -> KExpr<Meta> {
    KExpr::sort(level_of_nat(n))
  }
  fn prop() -> KExpr<Meta> {
    KExpr::sort(KLevel::zero())
  }
  fn ty() -> KExpr<Meta> {
    srt(1)
  }
  fn lam(dom: KExpr<Meta>, body: KExpr<Meta>) -> KExpr<Meta> {
    KExpr::lam(dom, body, anon(), BinderInfo::Default)
  }
  fn pi(dom: KExpr<Meta>, body: KExpr<Meta>) -> KExpr<Meta> {
    KExpr::forall_e(dom, body, anon(), BinderInfo::Default)
  }
  fn app(f: KExpr<Meta>, a: KExpr<Meta>) -> KExpr<Meta> {
    KExpr::app(f, a)
  }
  fn cst(addr: &Address) -> KExpr<Meta> {
    KExpr::cnst(addr.clone(), vec![], anon())
  }
  fn cst_l(addr: &Address, lvls: Vec<KLevel<Meta>>) -> KExpr<Meta> {
    KExpr::cnst(addr.clone(), lvls, anon())
  }
  fn nat_lit(n: u64) -> KExpr<Meta> {
    KExpr::lit(Literal::NatVal(Nat::from(n)))
  }
  fn str_lit(s: &str) -> KExpr<Meta> {
    KExpr::lit(Literal::StrVal(s.to_string()))
  }
  fn let_e(typ: KExpr<Meta>, val: KExpr<Meta>, body: KExpr<Meta>) -> KExpr<Meta> {
    KExpr::let_e(typ, val, body, anon())
  }
  fn proj_e(type_addr: &Address, idx: usize, strct: KExpr<Meta>) -> KExpr<Meta> {
    KExpr::proj(type_addr.clone(), idx, strct, anon())
  }

  /// Build Primitives with consistent test addresses.
  fn test_prims() -> Primitives {
    Primitives {
      nat: Some(Address::hash(b"Nat")),
      nat_zero: Some(Address::hash(b"Nat.zero")),
      nat_succ: Some(Address::hash(b"Nat.succ")),
      nat_add: Some(Address::hash(b"Nat.add")),
      nat_pred: Some(Address::hash(b"Nat.pred")),
      nat_sub: Some(Address::hash(b"Nat.sub")),
      nat_mul: Some(Address::hash(b"Nat.mul")),
      nat_pow: Some(Address::hash(b"Nat.pow")),
      nat_gcd: Some(Address::hash(b"Nat.gcd")),
      nat_mod: Some(Address::hash(b"Nat.mod")),
      nat_div: Some(Address::hash(b"Nat.div")),
      nat_bitwise: Some(Address::hash(b"Nat.bitwise")),
      nat_beq: Some(Address::hash(b"Nat.beq")),
      nat_ble: Some(Address::hash(b"Nat.ble")),
      nat_land: Some(Address::hash(b"Nat.land")),
      nat_lor: Some(Address::hash(b"Nat.lor")),
      nat_xor: Some(Address::hash(b"Nat.xor")),
      nat_shift_left: Some(Address::hash(b"Nat.shiftLeft")),
      nat_shift_right: Some(Address::hash(b"Nat.shiftRight")),
      bool_type: Some(Address::hash(b"Bool")),
      bool_true: Some(Address::hash(b"Bool.true")),
      bool_false: Some(Address::hash(b"Bool.false")),
      string: Some(Address::hash(b"String")),
      string_mk: Some(Address::hash(b"String.mk")),
      char_type: Some(Address::hash(b"Char")),
      char_mk: Some(Address::hash(b"Char.ofNat")),
      string_of_list: Some(Address::hash(b"String.mk")),
      list: Some(Address::hash(b"List")),
      list_nil: Some(Address::hash(b"List.nil")),
      list_cons: Some(Address::hash(b"List.cons")),
      eq: Some(Address::hash(b"Eq")),
      eq_refl: Some(Address::hash(b"Eq.refl")),
      quot_type: None,
      quot_ctor: None,
      quot_lift: None,
      quot_ind: None,
      reduce_bool: None,
      reduce_nat: None,
      eager_reduce: None,
    }
  }

  // -- Test runners --

  /// Evaluate an expression, then quote it back.
  fn eval_quote(
    env: &KEnv<Meta>,
    prims: &Primitives,
    e: &KExpr<Meta>,
  ) -> Result<KExpr<Meta>, String> {
    let mut tc = TypeChecker::new(env, prims);
    let val = tc.eval(e, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    tc.quote(&val, 0).map_err(|e| format!("{e}"))
  }

  /// Evaluate, WHNF, then quote.
  fn whnf_quote(
    env: &KEnv<Meta>,
    prims: &Primitives,
    e: &KExpr<Meta>,
  ) -> Result<KExpr<Meta>, String> {
    let mut tc = TypeChecker::new(env, prims);
    let val = tc.eval(e, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    let w = tc.whnf_val(&val, 0).map_err(|e| format!("{e}"))?;
    tc.quote(&w, 0).map_err(|e| format!("{e}"))
  }

  /// Evaluate, WHNF, then quote — with quotient initialization.
  fn whnf_quote_qi(
    env: &KEnv<Meta>,
    prims: &Primitives,
    e: &KExpr<Meta>,
    quot_init: bool,
  ) -> Result<KExpr<Meta>, String> {
    let mut tc = TypeChecker::new(env, prims);
    tc.quot_init = quot_init;
    let val = tc.eval(e, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    let w = tc.whnf_val(&val, 0).map_err(|e| format!("{e}"))?;
    tc.quote(&w, 0).map_err(|e| format!("{e}"))
  }

  /// Check definitional equality of two expressions.
  fn is_def_eq(
    env: &KEnv<Meta>,
    prims: &Primitives,
    a: &KExpr<Meta>,
    b: &KExpr<Meta>,
  ) -> Result<bool, String> {
    let mut tc = TypeChecker::new(env, prims);
    let va = tc.eval(a, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    let vb = tc.eval(b, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    tc.is_def_eq(&va, &vb).map_err(|e| format!("{e}"))
  }

  /// Infer the type of an expression, then quote.
  fn infer_quote(
    env: &KEnv<Meta>,
    prims: &Primitives,
    e: &KExpr<Meta>,
  ) -> Result<KExpr<Meta>, String> {
    let mut tc = TypeChecker::new(env, prims);
    let (_, typ_val) = tc.infer(e).map_err(|e| format!("{e}"))?;
    let depth = tc.depth();
    tc.quote(&typ_val, depth).map_err(|e| format!("{e}"))
  }

  /// Get the head const address of a WHNF result.
  fn whnf_head_addr(
    env: &KEnv<Meta>,
    prims: &Primitives,
    e: &KExpr<Meta>,
  ) -> Result<Option<Address>, String> {
    let mut tc = TypeChecker::new(env, prims);
    let val = tc.eval(e, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    let w = tc.whnf_val(&val, 0).map_err(|e| format!("{e}"))?;
    match w.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        ..
      } => Ok(Some(addr.clone())),
      ValInner::Ctor { addr, .. } => Ok(Some(addr.clone())),
      _ => Ok(None),
    }
  }

  // -- Env builders --

  fn add_def(
    env: &mut KEnv<Meta>,
    addr: &Address,
    typ: KExpr<Meta>,
    value: KExpr<Meta>,
    num_levels: usize,
    hints: ReducibilityHints,
  ) {
    env.insert(
      addr.clone(),
      KConstantInfo::Definition(KDefinitionVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        value,
        hints,
        safety: DefinitionSafety::Safe,
        all: vec![addr.clone()],
      }),
    );
  }

  fn add_axiom(env: &mut KEnv<Meta>, addr: &Address, typ: KExpr<Meta>) {
    env.insert(
      addr.clone(),
      KConstantInfo::Axiom(KAxiomVal {
        cv: KConstantVal {
          num_levels: 0,
          typ,
          name: anon(),
          level_params: vec![],
        },
        is_unsafe: false,
      }),
    );
  }

  fn add_opaque(env: &mut KEnv<Meta>, addr: &Address, typ: KExpr<Meta>, value: KExpr<Meta>) {
    env.insert(
      addr.clone(),
      KConstantInfo::Opaque(KOpaqueVal {
        cv: KConstantVal {
          num_levels: 0,
          typ,
          name: anon(),
          level_params: vec![],
        },
        value,
        is_unsafe: false,
        all: vec![addr.clone()],
      }),
    );
  }

  fn add_theorem(env: &mut KEnv<Meta>, addr: &Address, typ: KExpr<Meta>, value: KExpr<Meta>) {
    env.insert(
      addr.clone(),
      KConstantInfo::Theorem(KTheoremVal {
        cv: KConstantVal {
          num_levels: 0,
          typ,
          name: anon(),
          level_params: vec![],
        },
        value,
        all: vec![addr.clone()],
      }),
    );
  }

  fn add_inductive(
    env: &mut KEnv<Meta>,
    addr: &Address,
    typ: KExpr<Meta>,
    ctors: Vec<Address>,
    num_params: usize,
    num_indices: usize,
    is_rec: bool,
    num_levels: usize,
    all: Vec<Address>,
  ) {
    env.insert(
      addr.clone(),
      KConstantInfo::Inductive(KInductiveVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        num_params,
        num_indices,
        all,
        ctors,
        num_nested: 0,
        is_rec,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
  }

  fn add_ctor(
    env: &mut KEnv<Meta>,
    addr: &Address,
    induct: &Address,
    typ: KExpr<Meta>,
    cidx: usize,
    num_params: usize,
    num_fields: usize,
    num_levels: usize,
  ) {
    env.insert(
      addr.clone(),
      KConstantInfo::Constructor(KConstructorVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        induct: induct.clone(),
        cidx,
        num_params,
        num_fields,
        is_unsafe: false,
      }),
    );
  }

  fn add_rec(
    env: &mut KEnv<Meta>,
    addr: &Address,
    num_levels: usize,
    typ: KExpr<Meta>,
    all: Vec<Address>,
    num_params: usize,
    num_indices: usize,
    num_motives: usize,
    num_minors: usize,
    rules: Vec<KRecursorRule<Meta>>,
    k: bool,
  ) {
    env.insert(
      addr.clone(),
      KConstantInfo::Recursor(KRecursorVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        k,
        is_unsafe: false,
      }),
    );
  }

  fn add_quot(
    env: &mut KEnv<Meta>,
    addr: &Address,
    typ: KExpr<Meta>,
    kind: QuotKind,
    num_levels: usize,
  ) {
    env.insert(
      addr.clone(),
      KConstantInfo::Quotient(KQuotVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        kind,
      }),
    );
  }

  // -- Shared environments --

  /// Build MyNat inductive. Returns (env, natInd, zero, succ, rec).
  fn build_my_nat_env(
    mut env: KEnv<Meta>,
  ) -> (KEnv<Meta>, Address, Address, Address, Address) {
    let nat_ind = mk_addr(50);
    let zero = mk_addr(51);
    let succ = mk_addr(52);
    let rec = mk_addr(53);
    let nat_type = ty();
    let nat_const = cst(&nat_ind);

    add_inductive(
      &mut env,
      &nat_ind,
      nat_type,
      vec![zero.clone(), succ.clone()],
      0,
      0,
      false,
      0,
      vec![nat_ind.clone()],
    );
    add_ctor(&mut env, &zero, &nat_ind, nat_const.clone(), 0, 0, 0, 0);
    let succ_type = pi(nat_const.clone(), nat_const.clone());
    add_ctor(&mut env, &succ, &nat_ind, succ_type, 1, 0, 1, 0);

    // rec : (motive : MyNat → Type) → motive zero → ((n:MyNat) → motive n → motive (succ n)) → (t:MyNat) → motive t
    let rec_type = pi(
      pi(nat_const.clone(), ty()),
      pi(
        app(bv(0), cst(&zero)),
        pi(
          pi(
            nat_const.clone(),
            pi(
              app(bv(2), bv(0)),
              app(bv(3), app(cst(&succ), bv(1))),
            ),
          ),
          pi(nat_const.clone(), app(bv(3), bv(0))),
        ),
      ),
    );

    // Rule for zero: nfields=0, rhs = λ motive base step => base
    let zero_rhs = lam(ty(), lam(bv(0), lam(ty(), bv(1))));
    // Rule for succ: nfields=1, rhs = λ motive base step n => step n (rec motive base step n)
    let succ_rhs = lam(
      ty(),
      lam(
        bv(0),
        lam(
          ty(),
          lam(
            nat_const.clone(),
            app(
              app(bv(1), bv(0)),
              app(
                app(app(app(cst(&rec), bv(3)), bv(2)), bv(1)),
                bv(0),
              ),
            ),
          ),
        ),
      ),
    );

    add_rec(
      &mut env,
      &rec,
      0,
      rec_type,
      vec![nat_ind.clone()],
      0,
      0,
      1,
      2,
      vec![
        KRecursorRule {
          ctor: zero.clone(),
          nfields: 0,
          rhs: zero_rhs,
        },
        KRecursorRule {
          ctor: succ.clone(),
          nfields: 1,
          rhs: succ_rhs,
        },
      ],
      false,
    );

    (env, nat_ind, zero, succ, rec)
  }

  /// Build MyTrue : Prop with intro and K-recursor.
  fn build_my_true_env(
    mut env: KEnv<Meta>,
  ) -> (KEnv<Meta>, Address, Address, Address) {
    let true_ind = mk_addr(120);
    let intro = mk_addr(121);
    let rec = mk_addr(122);
    let true_const = cst(&true_ind);

    add_inductive(
      &mut env,
      &true_ind,
      prop(),
      vec![intro.clone()],
      0,
      0,
      false,
      0,
      vec![true_ind.clone()],
    );
    add_ctor(&mut env, &intro, &true_ind, true_const.clone(), 0, 0, 0, 0);

    // rec : (motive : MyTrue → Prop) → motive intro → (t : MyTrue) → motive t
    let rec_type = pi(
      pi(true_const.clone(), prop()),
      pi(
        app(bv(0), cst(&intro)),
        pi(true_const.clone(), app(bv(2), bv(0))),
      ),
    );
    let rule_rhs =
      lam(pi(true_const.clone(), prop()), lam(prop(), bv(0)));

    add_rec(
      &mut env,
      &rec,
      0,
      rec_type,
      vec![true_ind.clone()],
      0,
      0,
      1,
      1,
      vec![KRecursorRule {
        ctor: intro.clone(),
        nfields: 0,
        rhs: rule_rhs,
      }],
      true, // K=true
    );

    (env, true_ind, intro, rec)
  }

  /// Build Pair : Type → Type → Type with Pair.mk.
  fn build_pair_env(
    mut env: KEnv<Meta>,
  ) -> (KEnv<Meta>, Address, Address) {
    let pair_ind = mk_addr(160);
    let pair_ctor = mk_addr(161);

    add_inductive(
      &mut env,
      &pair_ind,
      pi(ty(), pi(ty(), ty())),
      vec![pair_ctor.clone()],
      2,
      0,
      false,
      0,
      vec![pair_ind.clone()],
    );

    // mk : (α β : Type) → α → β → Pair α β
    let ctor_type = pi(
      ty(),
      pi(
        ty(),
        pi(
          bv(1),
          pi(bv(1), app(app(cst(&pair_ind), bv(3)), bv(2))),
        ),
      ),
    );
    add_ctor(&mut env, &pair_ctor, &pair_ind, ctor_type, 0, 2, 2, 0);

    (env, pair_ind, pair_ctor)
  }

  fn empty_env() -> KEnv<Meta> {
    FxHashMap::default()
  }

  // ==========================================================================
  // Tests
  // ==========================================================================

  // -- eval+quote roundtrip --

  #[test]
  fn eval_quote_sort_roundtrip() {
    let env = empty_env();
    let prims = test_prims();
    assert_eq!(eval_quote(&env, &prims, &prop()).unwrap(), prop());
    assert_eq!(eval_quote(&env, &prims, &ty()).unwrap(), ty());
  }

  #[test]
  fn eval_quote_lit_roundtrip() {
    let env = empty_env();
    let prims = test_prims();
    assert_eq!(
      eval_quote(&env, &prims, &nat_lit(42)).unwrap(),
      nat_lit(42)
    );
    assert_eq!(
      eval_quote(&env, &prims, &str_lit("hello")).unwrap(),
      str_lit("hello")
    );
  }

  #[test]
  fn eval_quote_lambda_roundtrip() {
    let env = empty_env();
    let prims = test_prims();
    let id_lam = lam(ty(), bv(0));
    assert_eq!(eval_quote(&env, &prims, &id_lam).unwrap(), id_lam);
    let const_lam = lam(ty(), nat_lit(5));
    assert_eq!(eval_quote(&env, &prims, &const_lam).unwrap(), const_lam);
  }

  #[test]
  fn eval_quote_pi_roundtrip() {
    let env = empty_env();
    let prims = test_prims();
    let p = pi(ty(), bv(0));
    assert_eq!(eval_quote(&env, &prims, &p).unwrap(), p);
    let p2 = pi(ty(), ty());
    assert_eq!(eval_quote(&env, &prims, &p2).unwrap(), p2);
  }

  // -- beta reduction --

  #[test]
  fn beta_id_applied() {
    let env = empty_env();
    let prims = test_prims();
    // (λx. x) 5 = 5
    let e = app(lam(ty(), bv(0)), nat_lit(5));
    assert_eq!(eval_quote(&env, &prims, &e).unwrap(), nat_lit(5));
  }

  #[test]
  fn beta_const_applied() {
    let env = empty_env();
    let prims = test_prims();
    // (λx. 42) 5 = 42
    let e = app(lam(ty(), nat_lit(42)), nat_lit(5));
    assert_eq!(eval_quote(&env, &prims, &e).unwrap(), nat_lit(42));
  }

  #[test]
  fn beta_fst_snd() {
    let env = empty_env();
    let prims = test_prims();
    // (λx. λy. x) 1 2 = 1
    let fst = app(
      app(lam(ty(), lam(ty(), bv(1))), nat_lit(1)),
      nat_lit(2),
    );
    assert_eq!(eval_quote(&env, &prims, &fst).unwrap(), nat_lit(1));
    // (λx. λy. y) 1 2 = 2
    let snd = app(
      app(lam(ty(), lam(ty(), bv(0))), nat_lit(1)),
      nat_lit(2),
    );
    assert_eq!(eval_quote(&env, &prims, &snd).unwrap(), nat_lit(2));
  }

  #[test]
  fn beta_nested() {
    let env = empty_env();
    let prims = test_prims();
    // (λf. λx. f x) (λy. y) 7 = 7
    let e = app(
      app(
        lam(ty(), lam(ty(), app(bv(1), bv(0)))),
        lam(ty(), bv(0)),
      ),
      nat_lit(7),
    );
    assert_eq!(eval_quote(&env, &prims, &e).unwrap(), nat_lit(7));
  }

  #[test]
  fn beta_partial_application() {
    let env = empty_env();
    let prims = test_prims();
    // (λx. λy. x) 3 = λy. 3
    let e = app(lam(ty(), lam(ty(), bv(1))), nat_lit(3));
    assert_eq!(
      eval_quote(&env, &prims, &e).unwrap(),
      lam(ty(), nat_lit(3))
    );
  }

  // -- let reduction --

  #[test]
  fn let_reduction() {
    let env = empty_env();
    let prims = test_prims();
    // let x := 5 in x = 5
    assert_eq!(
      eval_quote(&env, &prims, &let_e(ty(), nat_lit(5), bv(0))).unwrap(),
      nat_lit(5)
    );
    // let x := 5 in 42 = 42
    assert_eq!(
      eval_quote(&env, &prims, &let_e(ty(), nat_lit(5), nat_lit(42)))
        .unwrap(),
      nat_lit(42)
    );
    // let x := 3 in let y := 7 in x = 3
    assert_eq!(
      eval_quote(
        &env,
        &prims,
        &let_e(ty(), nat_lit(3), let_e(ty(), nat_lit(7), bv(1)))
      )
      .unwrap(),
      nat_lit(3)
    );
    // let x := 3 in let y := 7 in y = 7
    assert_eq!(
      eval_quote(
        &env,
        &prims,
        &let_e(ty(), nat_lit(3), let_e(ty(), nat_lit(7), bv(0)))
      )
      .unwrap(),
      nat_lit(7)
    );
  }

  // -- Nat primitive reduction --

  #[test]
  fn nat_add() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(prims.nat_add.as_ref().unwrap()), nat_lit(2)),
      nat_lit(3),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(5));
  }

  #[test]
  fn nat_mul() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(prims.nat_mul.as_ref().unwrap()), nat_lit(4)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(20));
  }

  #[test]
  fn nat_sub() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(prims.nat_sub.as_ref().unwrap()), nat_lit(10)),
      nat_lit(3),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(7));
    // Truncated: 3 - 10 = 0
    let e2 = app(
      app(cst(prims.nat_sub.as_ref().unwrap()), nat_lit(3)),
      nat_lit(10),
    );
    assert_eq!(whnf_quote(&env, &prims, &e2).unwrap(), nat_lit(0));
  }

  #[test]
  fn nat_pow() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(prims.nat_pow.as_ref().unwrap()), nat_lit(2)),
      nat_lit(10),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(1024));
  }

  #[test]
  fn nat_succ() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(cst(prims.nat_succ.as_ref().unwrap()), nat_lit(41));
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(42));
  }

  #[test]
  fn nat_mod_div() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(prims.nat_mod.as_ref().unwrap()), nat_lit(17)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(2));
    let e2 = app(
      app(cst(prims.nat_div.as_ref().unwrap()), nat_lit(17)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e2).unwrap(), nat_lit(3));
  }

  #[test]
  fn nat_beq_ble() {
    let env = empty_env();
    let prims = test_prims();
    let beq_true = app(
      app(cst(prims.nat_beq.as_ref().unwrap()), nat_lit(5)),
      nat_lit(5),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &beq_true).unwrap(),
      cst(prims.bool_true.as_ref().unwrap())
    );
    let beq_false = app(
      app(cst(prims.nat_beq.as_ref().unwrap()), nat_lit(5)),
      nat_lit(6),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &beq_false).unwrap(),
      cst(prims.bool_false.as_ref().unwrap())
    );
    let ble_true = app(
      app(cst(prims.nat_ble.as_ref().unwrap()), nat_lit(3)),
      nat_lit(5),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &ble_true).unwrap(),
      cst(prims.bool_true.as_ref().unwrap())
    );
    let ble_false = app(
      app(cst(prims.nat_ble.as_ref().unwrap()), nat_lit(5)),
      nat_lit(3),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &ble_false).unwrap(),
      cst(prims.bool_false.as_ref().unwrap())
    );
  }

  // -- large nat --

  #[test]
  fn large_nat() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(prims.nat_pow.as_ref().unwrap()), nat_lit(2)),
      nat_lit(63),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &e).unwrap(),
      nat_lit(9223372036854775808)
    );
  }

  // -- nat primitives extended --

  #[test]
  fn nat_gcd_land_lor_xor_shift() {
    let env = empty_env();
    let prims = test_prims();
    // gcd 12 8 = 4
    let e = app(
      app(cst(prims.nat_gcd.as_ref().unwrap()), nat_lit(12)),
      nat_lit(8),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(4));
    // land 10 12 = 8
    let e = app(
      app(cst(prims.nat_land.as_ref().unwrap()), nat_lit(10)),
      nat_lit(12),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(8));
    // lor 10 5 = 15
    let e = app(
      app(cst(prims.nat_lor.as_ref().unwrap()), nat_lit(10)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(15));
    // xor 10 12 = 6
    let e = app(
      app(cst(prims.nat_xor.as_ref().unwrap()), nat_lit(10)),
      nat_lit(12),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(6));
    // shiftLeft 1 10 = 1024
    let e = app(
      app(cst(prims.nat_shift_left.as_ref().unwrap()), nat_lit(1)),
      nat_lit(10),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(1024));
    // shiftRight 1024 3 = 128
    let e = app(
      app(
        cst(prims.nat_shift_right.as_ref().unwrap()),
        nat_lit(1024),
      ),
      nat_lit(3),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(128));
  }

  // -- nat edge cases --

  #[test]
  fn nat_edge_cases() {
    let env = empty_env();
    let prims = test_prims();
    // div 0 0 = 0
    let e = app(
      app(cst(prims.nat_div.as_ref().unwrap()), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // mod 0 0 = 0
    let e = app(
      app(cst(prims.nat_mod.as_ref().unwrap()), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // gcd 0 0 = 0
    let e = app(
      app(cst(prims.nat_gcd.as_ref().unwrap()), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // sub 0 0 = 0
    let e = app(
      app(cst(prims.nat_sub.as_ref().unwrap()), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // pow 0 0 = 1
    let e = app(
      app(cst(prims.nat_pow.as_ref().unwrap()), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(1));
    // mul 0 999 = 0
    let e = app(
      app(cst(prims.nat_mul.as_ref().unwrap()), nat_lit(0)),
      nat_lit(999),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // chained: (3*4) + (10-3) = 19
    let inner1 = app(
      app(cst(prims.nat_mul.as_ref().unwrap()), nat_lit(3)),
      nat_lit(4),
    );
    let inner2 = app(
      app(cst(prims.nat_sub.as_ref().unwrap()), nat_lit(10)),
      nat_lit(3),
    );
    let chained =
      app(app(cst(prims.nat_add.as_ref().unwrap()), inner1), inner2);
    assert_eq!(whnf_quote(&env, &prims, &chained).unwrap(), nat_lit(19));
  }

  // -- delta unfolding --

  #[test]
  fn delta_unfolding() {
    let prims = test_prims();
    let def_addr = mk_addr(1);
    let add_body = app(
      app(cst(prims.nat_add.as_ref().unwrap()), nat_lit(2)),
      nat_lit(3),
    );
    let mut env = empty_env();
    add_def(
      &mut env,
      &def_addr,
      ty(),
      add_body,
      0,
      ReducibilityHints::Abbrev,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &cst(&def_addr)).unwrap(),
      nat_lit(5)
    );

    // Chain: myTen := Nat.add myFive myFive
    let ten_addr = mk_addr(2);
    let ten_body = app(
      app(cst(prims.nat_add.as_ref().unwrap()), cst(&def_addr)),
      cst(&def_addr),
    );
    add_def(
      &mut env,
      &ten_addr,
      ty(),
      ten_body,
      0,
      ReducibilityHints::Abbrev,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &cst(&ten_addr)).unwrap(),
      nat_lit(10)
    );
  }

  // -- delta lambda --

  #[test]
  fn delta_lambda() {
    let prims = test_prims();
    let id_addr = mk_addr(10);
    let mut env = empty_env();
    add_def(
      &mut env,
      &id_addr,
      pi(ty(), ty()),
      lam(ty(), bv(0)),
      0,
      ReducibilityHints::Abbrev,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &app(cst(&id_addr), nat_lit(42))).unwrap(),
      nat_lit(42)
    );

    let const_addr = mk_addr(11);
    add_def(
      &mut env,
      &const_addr,
      pi(ty(), pi(ty(), ty())),
      lam(ty(), lam(ty(), bv(1))),
      0,
      ReducibilityHints::Abbrev,
    );
    assert_eq!(
      whnf_quote(
        &env,
        &prims,
        &app(app(cst(&const_addr), nat_lit(1)), nat_lit(2))
      )
      .unwrap(),
      nat_lit(1)
    );
  }

  // -- opaque constants --

  #[test]
  fn opaque_constants() {
    let prims = test_prims();
    let opaque_addr = mk_addr(100);
    let mut env = empty_env();
    add_opaque(&mut env, &opaque_addr, ty(), nat_lit(5));
    // Opaque stays stuck
    assert_eq!(
      whnf_quote(&env, &prims, &cst(&opaque_addr)).unwrap(),
      cst(&opaque_addr)
    );

    // Theorem unfolds
    let thm_addr = mk_addr(102);
    add_theorem(&mut env, &thm_addr, ty(), nat_lit(5));
    assert_eq!(
      whnf_quote(&env, &prims, &cst(&thm_addr)).unwrap(),
      nat_lit(5)
    );
  }

  // -- universe polymorphism --

  #[test]
  fn universe_poly() {
    let prims = test_prims();
    let id_addr = mk_addr(110);
    let lvl_param = KLevel::param(0, anon());
    let param_sort = KExpr::sort(lvl_param);
    let mut env = empty_env();
    add_def(
      &mut env,
      &id_addr,
      pi(param_sort.clone(), param_sort.clone()),
      lam(param_sort, bv(0)),
      1,
      ReducibilityHints::Abbrev,
    );

    // id.{1} Type = Type
    let lvl1 = KLevel::succ(KLevel::zero());
    let applied = app(cst_l(&id_addr, vec![lvl1]), ty());
    assert_eq!(whnf_quote(&env, &prims, &applied).unwrap(), ty());

    // id.{0} Prop = Prop
    let applied0 = app(cst_l(&id_addr, vec![KLevel::zero()]), prop());
    assert_eq!(whnf_quote(&env, &prims, &applied0).unwrap(), prop());
  }

  // -- projection reduction --

  #[test]
  fn projection_reduction() {
    let prims = test_prims();
    let (env, pair_ind, pair_ctor) = build_pair_env(empty_env());
    // Pair.mk Nat Nat 3 7
    let mk_expr = app(
      app(
        app(app(cst(&pair_ctor), ty()), ty()),
        nat_lit(3),
      ),
      nat_lit(7),
    );
    let proj0 = proj_e(&pair_ind, 0, mk_expr.clone());
    assert_eq!(eval_quote(&env, &prims, &proj0).unwrap(), nat_lit(3));
    let proj1 = proj_e(&pair_ind, 1, mk_expr);
    assert_eq!(eval_quote(&env, &prims, &proj1).unwrap(), nat_lit(7));
  }

  // -- stuck terms --

  #[test]
  fn stuck_terms() {
    let prims = test_prims();
    let ax_addr = mk_addr(30);
    let mut env = empty_env();
    add_axiom(&mut env, &ax_addr, ty());
    // Axiom stays stuck
    assert_eq!(
      whnf_quote(&env, &prims, &cst(&ax_addr)).unwrap(),
      cst(&ax_addr)
    );
    // Nat.add axiom 5: the second arg is a nat literal (not Nat.succ),
    // so step-case reduction does not fire (extract_succ_pred only matches
    // structural succ, not literals — to avoid O(n) peeling). The expression
    // stays stuck with nat_add as the head.
    let stuck_add = app(
      app(cst(prims.nat_add.as_ref().unwrap()), cst(&ax_addr)),
      nat_lit(5),
    );
    assert_eq!(
      whnf_head_addr(&env, &prims, &stuck_add).unwrap(),
      Some(prims.nat_add.clone().unwrap())
    );

    // Nat.add axiom (Nat.succ axiom): second arg IS structural succ,
    // so step-case fires: add x (succ y) → succ (add x y)
    let succ_axiom = app(cst(prims.nat_succ.as_ref().unwrap()), cst(&ax_addr));
    let stuck_add_succ = app(
      app(cst(prims.nat_add.as_ref().unwrap()), cst(&ax_addr)),
      succ_axiom,
    );
    assert_eq!(
      whnf_head_addr(&env, &prims, &stuck_add_succ).unwrap(),
      Some(prims.nat_succ.clone().unwrap())
    );
  }

  // -- nested beta+delta --

  #[test]
  fn nested_beta_delta() {
    let prims = test_prims();
    let double_addr = mk_addr(40);
    let double_body = lam(
      ty(),
      app(
        app(cst(prims.nat_add.as_ref().unwrap()), bv(0)),
        bv(0),
      ),
    );
    let mut env = empty_env();
    add_def(
      &mut env,
      &double_addr,
      pi(ty(), ty()),
      double_body,
      0,
      ReducibilityHints::Abbrev,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &app(cst(&double_addr), nat_lit(21)))
        .unwrap(),
      nat_lit(42)
    );

    // quadruple := λx. double (double x)
    let quad_addr = mk_addr(41);
    let quad_body = lam(
      ty(),
      app(cst(&double_addr), app(cst(&double_addr), bv(0))),
    );
    add_def(
      &mut env,
      &quad_addr,
      pi(ty(), ty()),
      quad_body,
      0,
      ReducibilityHints::Abbrev,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &app(cst(&quad_addr), nat_lit(10)))
        .unwrap(),
      nat_lit(40)
    );
  }

  // -- higher-order --

  #[test]
  fn higher_order() {
    let env = empty_env();
    let prims = test_prims();
    let succ_fn =
      lam(ty(), app(cst(prims.nat_succ.as_ref().unwrap()), bv(0)));
    let twice = lam(
      pi(ty(), ty()),
      lam(ty(), app(bv(1), app(bv(1), bv(0)))),
    );
    let e = app(app(twice, succ_fn), nat_lit(0));
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(2));
  }

  // -- iota reduction --

  #[test]
  fn iota_reduction() {
    let prims = test_prims();
    let (env, _nat_ind, zero, succ, rec) =
      build_my_nat_env(empty_env());
    let nat_const = cst(&_nat_ind);
    let motive = lam(nat_const.clone(), ty());
    let base = nat_lit(0);
    let step = lam(
      nat_const.clone(),
      lam(ty(), app(cst(prims.nat_succ.as_ref().unwrap()), bv(0))),
    );

    // rec motive 0 step zero = 0
    let rec_zero = app(
      app(app(app(cst(&rec), motive.clone()), base.clone()), step.clone()),
      cst(&zero),
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_zero).unwrap(), nat_lit(0));

    // rec motive 0 step (succ zero) = 1
    let rec_one = app(
      app(app(app(cst(&rec), motive.clone()), base.clone()), step.clone()),
      app(cst(&succ), cst(&zero)),
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_one).unwrap(), nat_lit(1));
  }

  // -- recursive iota --

  #[test]
  fn recursive_iota() {
    let prims = test_prims();
    let (env, _nat_ind, zero, succ, rec) =
      build_my_nat_env(empty_env());
    let nat_const = cst(&_nat_ind);
    let motive = lam(nat_const.clone(), ty());
    let base = nat_lit(0);
    let step = lam(
      nat_const.clone(),
      lam(ty(), app(cst(prims.nat_succ.as_ref().unwrap()), bv(0))),
    );

    // rec on succ(succ(zero)) = 2
    let two = app(cst(&succ), app(cst(&succ), cst(&zero)));
    let rec_two = app(
      app(app(app(cst(&rec), motive.clone()), base.clone()), step.clone()),
      two,
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_two).unwrap(), nat_lit(2));

    // rec on succ^3(zero) = 3
    let three = app(
      cst(&succ),
      app(cst(&succ), app(cst(&succ), cst(&zero))),
    );
    let rec_three = app(
      app(app(app(cst(&rec), motive), base), step),
      three,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &rec_three).unwrap(),
      nat_lit(3)
    );
  }

  // -- K-reduction --

  #[test]
  fn k_reduction() {
    let prims = test_prims();
    let (env, true_ind, intro, rec) =
      build_my_true_env(empty_env());
    let true_const = cst(&true_ind);
    let motive = lam(true_const.clone(), prop());
    let h = cst(&intro);

    // K-rec intro = intro (normal iota)
    let rec_intro =
      app(app(app(cst(&rec), motive.clone()), h.clone()), cst(&intro));
    assert!(whnf_quote(&env, &prims, &rec_intro).is_ok());

    // K-rec on axiom — K-reduction should return the minor
    let ax_addr = mk_addr(123);
    let mut env2 = env.clone();
    add_axiom(&mut env2, &ax_addr, true_const);
    let rec_ax =
      app(app(app(cst(&rec), motive), h), cst(&ax_addr));
    assert_eq!(
      whnf_quote(&env2, &prims, &rec_ax).unwrap(),
      cst(&intro)
    );
  }

  // -- K-reduction extended --

  #[test]
  fn k_reduction_extended() {
    let prims = test_prims();
    let (env, true_ind, intro, rec) =
      build_my_true_env(empty_env());
    let true_const = cst(&true_ind);
    let motive = lam(true_const.clone(), prop());
    let h = cst(&intro);

    // K-rec intro = intro
    let rec_intro =
      app(app(app(cst(&rec), motive.clone()), h.clone()), cst(&intro));
    assert_eq!(
      whnf_quote(&env, &prims, &rec_intro).unwrap(),
      cst(&intro)
    );

    // K-rec on axiom = minor
    let ax_addr = mk_addr(123);
    let mut env2 = env.clone();
    add_axiom(&mut env2, &ax_addr, true_const.clone());
    let rec_ax = app(
      app(app(cst(&rec), motive.clone()), h.clone()),
      cst(&ax_addr),
    );
    assert_eq!(
      whnf_quote(&env2, &prims, &rec_ax).unwrap(),
      cst(&intro)
    );

    // Non-K recursor stays stuck on axiom
    let (nat_env, nat_ind, _zero, _succ, nat_rec) =
      build_my_nat_env(empty_env());
    let nat_motive = lam(cst(&nat_ind), ty());
    let nat_base = nat_lit(0);
    let nat_step = lam(
      cst(&nat_ind),
      lam(ty(), app(cst(prims.nat_succ.as_ref().unwrap()), bv(0))),
    );
    let nat_ax = mk_addr(125);
    let mut nat_env2 = nat_env.clone();
    add_axiom(&mut nat_env2, &nat_ax, cst(&nat_ind));
    let rec_nat_ax = app(
      app(
        app(
          app(cst(&nat_rec), nat_motive),
          nat_base,
        ),
        nat_step,
      ),
      cst(&nat_ax),
    );
    assert_eq!(
      whnf_head_addr(&nat_env2, &prims, &rec_nat_ax).unwrap(),
      Some(nat_rec)
    );
  }

  // -- proof irrelevance --

  #[test]
  fn proof_irrelevance() {
    let prims = test_prims();
    let ax1 = mk_addr(130);
    let ax2 = mk_addr(131);
    let mut env = empty_env();
    add_axiom(&mut env, &ax1, prop());
    add_axiom(&mut env, &ax2, prop());
    // Two Prop axioms are defEq (proof irrelevance for propositions)
    assert_eq!(
      is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap(),
      true
    );

    // Two Type axioms are NOT defEq
    let t1 = mk_addr(132);
    let t2 = mk_addr(133);
    let mut env2 = empty_env();
    add_axiom(&mut env2, &t1, ty());
    add_axiom(&mut env2, &t2, ty());
    assert_eq!(
      is_def_eq(&env2, &prims, &cst(&t1), &cst(&t2)).unwrap(),
      false
    );
  }

  // -- isDefEq --

  #[test]
  fn is_def_eq_basic() {
    let prims = test_prims();
    let env = empty_env();
    // Sort equality
    assert!(is_def_eq(&env, &prims, &prop(), &prop()).unwrap());
    assert!(is_def_eq(&env, &prims, &ty(), &ty()).unwrap());
    assert!(!is_def_eq(&env, &prims, &prop(), &ty()).unwrap());
    // Literal equality
    assert!(is_def_eq(&env, &prims, &nat_lit(42), &nat_lit(42)).unwrap());
    assert!(!is_def_eq(&env, &prims, &nat_lit(42), &nat_lit(43)).unwrap());
    // Lambda equality
    let id1 = lam(ty(), bv(0));
    let id2 = lam(ty(), bv(0));
    assert!(is_def_eq(&env, &prims, &id1, &id2).unwrap());
    let const_lam = lam(ty(), nat_lit(42));
    assert!(!is_def_eq(&env, &prims, &id1, &const_lam).unwrap());
    // Pi equality
    let p1 = pi(ty(), bv(0));
    let p2 = pi(ty(), bv(0));
    assert!(is_def_eq(&env, &prims, &p1, &p2).unwrap());
  }

  #[test]
  fn is_def_eq_delta() {
    let prims = test_prims();
    let d1 = mk_addr(60);
    let d2 = mk_addr(61);
    let mut env = empty_env();
    add_def(
      &mut env,
      &d1,
      ty(),
      nat_lit(5),
      0,
      ReducibilityHints::Abbrev,
    );
    add_def(
      &mut env,
      &d2,
      ty(),
      nat_lit(5),
      0,
      ReducibilityHints::Abbrev,
    );
    assert!(is_def_eq(&env, &prims, &cst(&d1), &cst(&d2)).unwrap());
  }

  #[test]
  fn is_def_eq_eta() {
    let prims = test_prims();
    let f_addr = mk_addr(62);
    let mut env = empty_env();
    add_def(
      &mut env,
      &f_addr,
      pi(ty(), ty()),
      lam(ty(), bv(0)),
      0,
      ReducibilityHints::Abbrev,
    );
    // λx. f x == f
    let eta_expanded = lam(ty(), app(cst(&f_addr), bv(0)));
    assert!(
      is_def_eq(&env, &prims, &eta_expanded, &cst(&f_addr)).unwrap()
    );
  }

  #[test]
  fn is_def_eq_nat_prims() {
    let prims = test_prims();
    let env = empty_env();
    let add_expr = app(
      app(cst(prims.nat_add.as_ref().unwrap()), nat_lit(2)),
      nat_lit(3),
    );
    assert!(is_def_eq(&env, &prims, &add_expr, &nat_lit(5)).unwrap());
    assert!(!is_def_eq(&env, &prims, &add_expr, &nat_lit(6)).unwrap());
  }

  // -- isDefEq offset --

  #[test]
  fn def_eq_offset() {
    let prims = test_prims();
    let env = empty_env();
    // Nat.succ 0 == 1
    let succ0 = app(cst(prims.nat_succ.as_ref().unwrap()), nat_lit(0));
    assert!(is_def_eq(&env, &prims, &succ0, &nat_lit(1)).unwrap());
    // Nat.zero == 0
    assert!(
      is_def_eq(
        &env,
        &prims,
        &cst(prims.nat_zero.as_ref().unwrap()),
        &nat_lit(0)
      )
      .unwrap()
    );
    // succ(succ(zero)) == 2
    let succ_succ_zero = app(
      cst(prims.nat_succ.as_ref().unwrap()),
      app(
        cst(prims.nat_succ.as_ref().unwrap()),
        cst(prims.nat_zero.as_ref().unwrap()),
      ),
    );
    assert!(
      is_def_eq(&env, &prims, &succ_succ_zero, &nat_lit(2)).unwrap()
    );
    // 3 != 4
    assert!(!is_def_eq(&env, &prims, &nat_lit(3), &nat_lit(4)).unwrap());
  }

  // -- isDefEq let --

  #[test]
  fn def_eq_let() {
    let prims = test_prims();
    let env = empty_env();
    // let x := 5 in x == 5
    assert!(
      is_def_eq(
        &env,
        &prims,
        &let_e(ty(), nat_lit(5), bv(0)),
        &nat_lit(5)
      )
      .unwrap()
    );
    // let x := 3 in let y := 4 in add x y == 7
    let add_xy = app(
      app(cst(prims.nat_add.as_ref().unwrap()), bv(1)),
      bv(0),
    );
    let let_expr = let_e(ty(), nat_lit(3), let_e(ty(), nat_lit(4), add_xy));
    assert!(is_def_eq(&env, &prims, &let_expr, &nat_lit(7)).unwrap());
    // let x := 5 in x != 6
    assert!(
      !is_def_eq(
        &env,
        &prims,
        &let_e(ty(), nat_lit(5), bv(0)),
        &nat_lit(6)
      )
      .unwrap()
    );
  }

  // -- Bool.true reflection --

  #[test]
  fn bool_true_reflection() {
    let prims = test_prims();
    let env = empty_env();
    let beq55 = app(
      app(cst(prims.nat_beq.as_ref().unwrap()), nat_lit(5)),
      nat_lit(5),
    );
    assert!(
      is_def_eq(
        &env,
        &prims,
        &cst(prims.bool_true.as_ref().unwrap()),
        &beq55
      )
      .unwrap()
    );
    let beq56 = app(
      app(cst(prims.nat_beq.as_ref().unwrap()), nat_lit(5)),
      nat_lit(6),
    );
    assert!(
      !is_def_eq(
        &env,
        &prims,
        &beq56,
        &cst(prims.bool_true.as_ref().unwrap())
      )
      .unwrap()
    );
  }

  // -- unit-like type equality --

  #[test]
  fn unit_like_def_eq() {
    let prims = test_prims();
    let unit_ind = mk_addr(140);
    let mk_addr2 = mk_addr(141);
    let mut env = empty_env();
    add_inductive(
      &mut env,
      &unit_ind,
      ty(),
      vec![mk_addr2.clone()],
      0,
      0,
      false,
      0,
      vec![unit_ind.clone()],
    );
    add_ctor(
      &mut env,
      &mk_addr2,
      &unit_ind,
      cst(&unit_ind),
      0,
      0,
      0,
      0,
    );
    // mk == mk
    assert!(
      is_def_eq(&env, &prims, &cst(&mk_addr2), &cst(&mk_addr2)).unwrap()
    );
    // mk == (λ_.mk) 0
    let mk_via_lam = app(lam(ty(), cst(&mk_addr2)), nat_lit(0));
    assert!(
      is_def_eq(&env, &prims, &mk_via_lam, &cst(&mk_addr2)).unwrap()
    );
  }

  // -- struct eta defEq --

  #[test]
  fn struct_eta_def_eq() {
    let prims = test_prims();
    let (env, pair_ind, pair_ctor) = build_pair_env(empty_env());
    // mk 3 7 == mk 3 7
    let mk37 = app(
      app(app(app(cst(&pair_ctor), ty()), ty()), nat_lit(3)),
      nat_lit(7),
    );
    assert!(is_def_eq(&env, &prims, &mk37, &mk37).unwrap());

    // proj 0 (mk 3 7) == 3
    let proj0 = proj_e(&pair_ind, 0, mk37.clone());
    assert!(is_def_eq(&env, &prims, &proj0, &nat_lit(3)).unwrap());

    // proj 1 (mk 3 7) == 7
    let proj1 = proj_e(&pair_ind, 1, mk37);
    assert!(is_def_eq(&env, &prims, &proj1, &nat_lit(7)).unwrap());
  }

  // -- struct eta with axioms --

  #[test]
  fn struct_eta_axiom() {
    let prims = test_prims();
    let (mut env, pair_ind, pair_ctor) = build_pair_env(empty_env());
    let ax_addr = mk_addr(290);
    let pair_type = app(app(cst(&pair_ind), ty()), ty());
    add_axiom(&mut env, &ax_addr, pair_type);

    // mk (proj 0 x) (proj 1 x) == x
    let proj0 = proj_e(&pair_ind, 0, cst(&ax_addr));
    let proj1 = proj_e(&pair_ind, 1, cst(&ax_addr));
    let rebuilt = app(
      app(app(app(cst(&pair_ctor), ty()), ty()), proj0),
      proj1,
    );
    assert!(
      is_def_eq(&env, &prims, &rebuilt, &cst(&ax_addr)).unwrap()
    );

    // Reversed: x == mk (proj0 x) (proj1 x)
    let proj0b = proj_e(&pair_ind, 0, cst(&ax_addr));
    let proj1b = proj_e(&pair_ind, 1, cst(&ax_addr));
    let rebuilt2 = app(
      app(app(app(cst(&pair_ctor), ty()), ty()), proj0b),
      proj1b,
    );
    assert!(
      is_def_eq(&env, &prims, &cst(&ax_addr), &rebuilt2).unwrap()
    );

    // Different axioms of same type: NOT defEq (Type, not Prop)
    let ax2 = mk_addr(291);
    add_axiom(&mut env, &ax2, app(app(cst(&pair_ind), ty()), ty()));
    assert!(
      !is_def_eq(&env, &prims, &cst(&ax_addr), &cst(&ax2)).unwrap()
    );
  }

  // -- struct eta iota --

  #[test]
  fn struct_eta_iota() {
    let prims = test_prims();
    let wrap_ind = mk_addr(170);
    let wrap_mk = mk_addr(171);
    let wrap_rec = mk_addr(172);
    let mut env = empty_env();

    add_inductive(
      &mut env,
      &wrap_ind,
      pi(ty(), ty()),
      vec![wrap_mk.clone()],
      1,
      0,
      false,
      0,
      vec![wrap_ind.clone()],
    );
    // Wrap.mk : (α : Type) → α → Wrap α
    let mk_type = pi(ty(), pi(bv(0), app(cst(&wrap_ind), bv(1))));
    add_ctor(&mut env, &wrap_mk, &wrap_ind, mk_type, 0, 1, 1, 0);

    // Wrap.rec : {α : Type} → (motive : Wrap α → Type) → ((a : α) → motive (mk a)) → (w : Wrap α) → motive w
    let rec_type = pi(
      ty(),
      pi(
        pi(app(cst(&wrap_ind), bv(0)), ty()),
        pi(
          pi(
            bv(1),
            app(bv(1), app(app(cst(&wrap_mk), bv(2)), bv(0))),
          ),
          pi(
            app(cst(&wrap_ind), bv(2)),
            app(bv(2), bv(0)),
          ),
        ),
      ),
    );
    // rhs: λ α motive f a => f a
    let rule_rhs =
      lam(ty(), lam(ty(), lam(ty(), lam(ty(), app(bv(1), bv(0))))));

    add_rec(
      &mut env,
      &wrap_rec,
      0,
      rec_type,
      vec![wrap_ind.clone()],
      1,
      0,
      1,
      1,
      vec![KRecursorRule {
        ctor: wrap_mk.clone(),
        nfields: 1,
        rhs: rule_rhs,
      }],
      false,
    );

    // rec (λ_. Nat) (λa. succ a) (mk Nat 5) = 6
    let motive = lam(app(cst(&wrap_ind), ty()), ty());
    let minor = lam(
      ty(),
      app(cst(prims.nat_succ.as_ref().unwrap()), bv(0)),
    );
    let mk_expr = app(app(cst(&wrap_mk), ty()), nat_lit(5));
    let rec_ctor = app(
      app(app(app(cst(&wrap_rec), ty()), motive.clone()), minor.clone()),
      mk_expr,
    );
    assert_eq!(
      whnf_quote(&env, &prims, &rec_ctor).unwrap(),
      nat_lit(6)
    );

    // Struct eta iota: rec on axiom of type Wrap Nat
    let ax_addr = mk_addr(173);
    let wrap_nat = app(cst(&wrap_ind), ty());
    add_axiom(&mut env, &ax_addr, wrap_nat);
    let rec_ax = app(
      app(app(app(cst(&wrap_rec), ty()), motive), minor),
      cst(&ax_addr),
    );
    assert!(whnf_quote(&env, &prims, &rec_ax).is_ok());
  }

  // -- quotient reduction --

  #[test]
  fn quotient_reduction() {
    let prims = test_prims();
    let quot_addr = mk_addr(150);
    let quot_mk_addr = mk_addr(151);
    let quot_lift_addr = mk_addr(152);
    let quot_ind_addr = mk_addr(153);

    let mut env = empty_env();

    // Quot.{u} : (α : Sort u) → (α → α → Prop) → Sort u
    let quot_type =
      pi(ty(), pi(pi(bv(0), pi(bv(1), prop())), bv(1)));
    add_quot(&mut env, &quot_addr, quot_type, QuotKind::Type, 1);

    // Quot.mk
    let mk_type = pi(
      ty(),
      pi(
        pi(bv(0), pi(bv(1), prop())),
        pi(
          bv(1),
          app(
            app(
              cst_l(&quot_addr, vec![KLevel::param(0, anon())]),
              bv(2),
            ),
            bv(1),
          ),
        ),
      ),
    );
    add_quot(&mut env, &quot_mk_addr, mk_type, QuotKind::Ctor, 1);

    // Quot.lift (simplified type)
    let lift_type = pi(
      ty(),
      pi(ty(), pi(ty(), pi(ty(), pi(ty(), pi(ty(), ty()))))),
    );
    add_quot(&mut env, &quot_lift_addr, lift_type, QuotKind::Lift, 2);

    // Quot.ind (simplified type)
    let ind_type = pi(
      ty(),
      pi(ty(), pi(ty(), pi(ty(), pi(ty(), prop())))),
    );
    add_quot(&mut env, &quot_ind_addr, ind_type, QuotKind::Ind, 1);

    let dummy_rel = lam(ty(), lam(ty(), prop()));
    let lvl1 = KLevel::succ(KLevel::zero());

    // Quot.mk applied
    let mk_expr = app(
      app(
        app(cst_l(&quot_mk_addr, vec![lvl1.clone()]), ty()),
        dummy_rel.clone(),
      ),
      nat_lit(42),
    );

    // f = λx. succ x
    let f_expr = lam(
      ty(),
      app(cst(prims.nat_succ.as_ref().unwrap()), bv(0)),
    );
    let h_expr = lam(ty(), lam(ty(), lam(prop(), nat_lit(0))));

    // Quot.lift α r β f h (Quot.mk α r 42) = f 42 = 43
    let lift_expr = app(
      app(
        app(
          app(
            app(
              app(
                cst_l(
                  &quot_lift_addr,
                  vec![lvl1.clone(), lvl1.clone()],
                ),
                ty(),
              ),
              dummy_rel,
            ),
            ty(),
          ),
          f_expr,
        ),
        h_expr,
      ),
      mk_expr,
    );
    assert_eq!(
      whnf_quote_qi(&env, &prims, &lift_expr, true).unwrap(),
      nat_lit(43)
    );
  }

  // -- type inference --

  #[test]
  fn infer_sorts() {
    let prims = test_prims();
    let env = empty_env();
    // Sort 0 : Sort 1
    assert_eq!(infer_quote(&env, &prims, &prop()).unwrap(), srt(1));
    // Sort 1 : Sort 2
    assert_eq!(infer_quote(&env, &prims, &ty()).unwrap(), srt(2));
  }

  #[test]
  fn infer_literals() {
    let prims = test_prims();
    let env = empty_env();
    // natLit 42 : Nat
    assert_eq!(
      infer_quote(&env, &prims, &nat_lit(42)).unwrap(),
      cst(prims.nat.as_ref().unwrap())
    );
    // strLit "hi" : String
    assert_eq!(
      infer_quote(&env, &prims, &str_lit("hi")).unwrap(),
      cst(prims.string.as_ref().unwrap())
    );
  }

  #[test]
  fn infer_lambda() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat_const = cst(&nat_addr);
    // λ(x : Nat). x : Nat → Nat
    let id_nat = lam(nat_const.clone(), bv(0));
    assert_eq!(
      infer_quote(&env, &prims, &id_nat).unwrap(),
      pi(nat_const.clone(), nat_const.clone())
    );
  }

  #[test]
  fn infer_pi() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat_const = cst(&nat_addr);
    // (Nat → Nat) : Sort 1
    assert_eq!(
      infer_quote(&env, &prims, &pi(nat_const.clone(), nat_const)).unwrap(),
      srt(1)
    );
    // ∀ (A : Type), A → A : Sort 2
    let poly_id = pi(ty(), pi(bv(0), bv(1)));
    assert_eq!(infer_quote(&env, &prims, &poly_id).unwrap(), srt(2));
  }

  #[test]
  fn infer_app() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat_const = cst(&nat_addr);
    // (λx:Nat. x) 5 : Nat
    let id_app = app(lam(nat_const.clone(), bv(0)), nat_lit(5));
    assert_eq!(
      infer_quote(&env, &prims, &id_app).unwrap(),
      nat_const
    );
  }

  #[test]
  fn infer_let() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat_const = cst(&nat_addr);
    // let x : Nat := 5 in x : Nat
    let let_expr = let_e(nat_const.clone(), nat_lit(5), bv(0));
    assert_eq!(
      infer_quote(&env, &prims, &let_expr).unwrap(),
      nat_const
    );
  }

  // -- errors --

  #[test]
  fn infer_errors() {
    let prims = test_prims();
    let env = empty_env();
    // bvar out of range
    assert!(infer_quote(&env, &prims, &bv(99)).is_err());
    // unknown const
    let bad_addr = mk_addr(255);
    assert!(infer_quote(&env, &prims, &cst(&bad_addr)).is_err());
    // app of non-function
    assert!(
      infer_quote(&env, &prims, &app(nat_lit(5), nat_lit(3))).is_err()
    );
  }

  // -- reducibility hints (lazyDelta) --

  #[test]
  fn reducibility_hints() {
    let prims = test_prims();
    let abbrev_addr = mk_addr(180);
    let reg_addr = mk_addr(181);
    let mut env = empty_env();
    add_def(
      &mut env,
      &abbrev_addr,
      ty(),
      nat_lit(5),
      0,
      ReducibilityHints::Abbrev,
    );
    add_def(
      &mut env,
      &reg_addr,
      ty(),
      nat_lit(5),
      0,
      ReducibilityHints::Regular(1),
    );
    // Both reduce to 5
    assert!(
      is_def_eq(&env, &prims, &cst(&abbrev_addr), &cst(&reg_addr)).unwrap()
    );

    // Different values: abbrev 5 != regular 6
    let reg2_addr = mk_addr(182);
    add_def(
      &mut env,
      &reg2_addr,
      ty(),
      nat_lit(6),
      0,
      ReducibilityHints::Regular(1),
    );
    assert!(
      !is_def_eq(&env, &prims, &cst(&abbrev_addr), &cst(&reg2_addr))
        .unwrap()
    );

    // Opaque != abbrev even with same value
    let opaq_addr = mk_addr(183);
    add_opaque(&mut env, &opaq_addr, ty(), nat_lit(5));
    assert!(
      !is_def_eq(&env, &prims, &cst(&opaq_addr), &cst(&abbrev_addr))
        .unwrap()
    );
  }

  // -- multi-universe params --

  #[test]
  fn multi_univ_params() {
    let prims = test_prims();
    let const_addr = mk_addr(190);
    let u = KLevel::param(0, anon());
    let v = KLevel::param(1, anon());
    let u_sort = KExpr::sort(u);
    let v_sort = KExpr::sort(v);
    let const_type = pi(u_sort.clone(), pi(v_sort.clone(), u_sort.clone()));
    let const_body = lam(u_sort, lam(v_sort, bv(1)));
    let mut env = empty_env();
    add_def(
      &mut env,
      &const_addr,
      const_type,
      const_body,
      2,
      ReducibilityHints::Abbrev,
    );

    // const.{1,0} Type Prop = Type
    let applied = app(
      app(
        cst_l(
          &const_addr,
          vec![KLevel::succ(KLevel::zero()), KLevel::zero()],
        ),
        ty(),
      ),
      prop(),
    );
    assert_eq!(whnf_quote(&env, &prims, &applied).unwrap(), ty());

    // const.{0,1} Prop Type = Prop
    let applied2 = app(
      app(
        cst_l(
          &const_addr,
          vec![KLevel::zero(), KLevel::succ(KLevel::zero())],
        ),
        prop(),
      ),
      ty(),
    );
    assert_eq!(whnf_quote(&env, &prims, &applied2).unwrap(), prop());
  }

  // -- string defEq --

  #[test]
  fn string_def_eq() {
    let prims = test_prims();
    let env = empty_env();
    // Same strings
    assert!(
      is_def_eq(&env, &prims, &str_lit("hello"), &str_lit("hello")).unwrap()
    );
    assert!(
      !is_def_eq(&env, &prims, &str_lit("hello"), &str_lit("world"))
        .unwrap()
    );
    // Empty strings
    assert!(
      is_def_eq(&env, &prims, &str_lit(""), &str_lit("")).unwrap()
    );

    // "" == String.mk (List.nil Char)
    let char_type = cst(prims.char_type.as_ref().unwrap());
    let nil_char = app(
      cst_l(prims.list_nil.as_ref().unwrap(), vec![KLevel::zero()]),
      char_type.clone(),
    );
    let empty_str =
      app(cst(prims.string_mk.as_ref().unwrap()), nil_char.clone());
    assert!(
      is_def_eq(&env, &prims, &str_lit(""), &empty_str).unwrap()
    );

    // "a" == String.mk (List.cons Char (Char.mk 97) nil)
    let char_a =
      app(cst(prims.char_mk.as_ref().unwrap()), nat_lit(97));
    let cons_a = app(
      app(
        app(
          cst_l(
            prims.list_cons.as_ref().unwrap(),
            vec![KLevel::zero()],
          ),
          char_type,
        ),
        char_a,
      ),
      nil_char,
    );
    let str_a = app(cst(prims.string_mk.as_ref().unwrap()), cons_a);
    assert!(is_def_eq(&env, &prims, &str_lit("a"), &str_a).unwrap());
  }

  // -- eta extension extended --

  #[test]
  fn eta_extended() {
    let prims = test_prims();
    let f_addr = mk_addr(220);
    let mut env = empty_env();
    add_def(
      &mut env,
      &f_addr,
      pi(ty(), ty()),
      lam(ty(), bv(0)),
      0,
      ReducibilityHints::Abbrev,
    );
    // f == λx. f x
    let eta = lam(ty(), app(cst(&f_addr), bv(0)));
    assert!(is_def_eq(&env, &prims, &cst(&f_addr), &eta).unwrap());

    // Double eta: f2 == λx.λy. f2 x y
    let f2_addr = mk_addr(221);
    let f2_type = pi(ty(), pi(ty(), ty()));
    add_def(
      &mut env,
      &f2_addr,
      f2_type,
      lam(ty(), lam(ty(), bv(1))),
      0,
      ReducibilityHints::Abbrev,
    );
    let double_eta =
      lam(ty(), lam(ty(), app(app(cst(&f2_addr), bv(1)), bv(0))));
    assert!(
      is_def_eq(&env, &prims, &cst(&f2_addr), &double_eta).unwrap()
    );

    // eta+beta: λx.(λy.y) x == λy.y
    let id_lam = lam(ty(), bv(0));
    let eta_id = lam(ty(), app(lam(ty(), bv(0)), bv(0)));
    assert!(is_def_eq(&env, &prims, &eta_id, &id_lam).unwrap());
  }

  // -- lazyDelta strategies --

  #[test]
  fn lazy_delta_strategies() {
    let prims = test_prims();
    let d1 = mk_addr(200);
    let d2 = mk_addr(201);
    let mut env = empty_env();
    add_def(
      &mut env,
      &d1,
      ty(),
      nat_lit(42),
      0,
      ReducibilityHints::Regular(1),
    );
    add_def(
      &mut env,
      &d2,
      ty(),
      nat_lit(42),
      0,
      ReducibilityHints::Regular(1),
    );
    assert!(is_def_eq(&env, &prims, &cst(&d1), &cst(&d2)).unwrap());

    // Different bodies
    let d3 = mk_addr(202);
    let d4 = mk_addr(203);
    add_def(
      &mut env,
      &d3,
      ty(),
      nat_lit(5),
      0,
      ReducibilityHints::Regular(1),
    );
    add_def(
      &mut env,
      &d4,
      ty(),
      nat_lit(6),
      0,
      ReducibilityHints::Regular(1),
    );
    assert!(!is_def_eq(&env, &prims, &cst(&d3), &cst(&d4)).unwrap());

    // Def chain: a := 5, b := a, c := b
    let a = mk_addr(204);
    let b = mk_addr(205);
    let c = mk_addr(206);
    add_def(
      &mut env,
      &a,
      ty(),
      nat_lit(5),
      0,
      ReducibilityHints::Regular(1),
    );
    add_def(
      &mut env,
      &b,
      ty(),
      cst(&a),
      0,
      ReducibilityHints::Regular(2),
    );
    add_def(
      &mut env,
      &c,
      ty(),
      cst(&b),
      0,
      ReducibilityHints::Regular(3),
    );
    assert!(is_def_eq(&env, &prims, &cst(&c), &nat_lit(5)).unwrap());
    assert!(is_def_eq(&env, &prims, &cst(&c), &cst(&a)).unwrap());
  }

  // -- isDefEq complex --

  #[test]
  fn def_eq_complex() {
    let prims = test_prims();
    let env = empty_env();
    // 2+3 == 3+2 (via reduction)
    let add23 = app(
      app(cst(prims.nat_add.as_ref().unwrap()), nat_lit(2)),
      nat_lit(3),
    );
    let add32 = app(
      app(cst(prims.nat_add.as_ref().unwrap()), nat_lit(3)),
      nat_lit(2),
    );
    assert!(is_def_eq(&env, &prims, &add23, &add32).unwrap());
    // 2*3 + 1 == 7
    let expr1 = app(
      app(
        cst(prims.nat_add.as_ref().unwrap()),
        app(
          app(cst(prims.nat_mul.as_ref().unwrap()), nat_lit(2)),
          nat_lit(3),
        ),
      ),
      nat_lit(1),
    );
    assert!(is_def_eq(&env, &prims, &expr1, &nat_lit(7)).unwrap());
  }

  // -- universe extended --

  #[test]
  fn universe_extended() {
    let prims = test_prims();
    let env = empty_env();
    // Sort (max 0 1) == Sort 1
    let max_sort = KExpr::sort(KLevel::max(KLevel::zero(), KLevel::succ(KLevel::zero())));
    assert!(is_def_eq(&env, &prims, &max_sort, &ty()).unwrap());
    // Sort (imax 1 0) == Sort 0 (imax u 0 = 0)
    let imax_sort = KExpr::sort(KLevel::imax(
      KLevel::succ(KLevel::zero()),
      KLevel::zero(),
    ));
    assert!(is_def_eq(&env, &prims, &imax_sort, &prop()).unwrap());
    // Sort (imax 0 1) == Sort 1
    let imax_sort2 = KExpr::sort(KLevel::imax(
      KLevel::zero(),
      KLevel::succ(KLevel::zero()),
    ));
    assert!(is_def_eq(&env, &prims, &imax_sort2, &ty()).unwrap());
  }

  // -- whnf caching and deep chains --

  #[test]
  fn whnf_deep_def_chain() {
    let prims = test_prims();
    let a = mk_addr(271);
    let b = mk_addr(272);
    let c = mk_addr(273);
    let d = mk_addr(274);
    let e = mk_addr(275);
    let mut env = empty_env();
    add_def(
      &mut env,
      &a,
      ty(),
      nat_lit(99),
      0,
      ReducibilityHints::Regular(1),
    );
    add_def(
      &mut env,
      &b,
      ty(),
      cst(&a),
      0,
      ReducibilityHints::Regular(2),
    );
    add_def(
      &mut env,
      &c,
      ty(),
      cst(&b),
      0,
      ReducibilityHints::Regular(3),
    );
    add_def(
      &mut env,
      &d,
      ty(),
      cst(&c),
      0,
      ReducibilityHints::Regular(4),
    );
    add_def(
      &mut env,
      &e,
      ty(),
      cst(&d),
      0,
      ReducibilityHints::Regular(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &cst(&e)).unwrap(), nat_lit(99));
  }

  // -- natLit ctor defEq --

  #[test]
  fn nat_lit_ctor_def_eq() {
    let prims = test_prims();
    let env = empty_env();
    // 0 == Nat.zero
    assert!(
      is_def_eq(
        &env,
        &prims,
        &nat_lit(0),
        &cst(prims.nat_zero.as_ref().unwrap())
      )
      .unwrap()
    );
    // Nat.zero == 0
    assert!(
      is_def_eq(
        &env,
        &prims,
        &cst(prims.nat_zero.as_ref().unwrap()),
        &nat_lit(0)
      )
      .unwrap()
    );
    // 1 == succ zero
    let succ_zero = app(
      cst(prims.nat_succ.as_ref().unwrap()),
      cst(prims.nat_zero.as_ref().unwrap()),
    );
    assert!(
      is_def_eq(&env, &prims, &nat_lit(1), &succ_zero).unwrap()
    );
    // 5 == succ^5 zero
    let succ5 = app(
      cst(prims.nat_succ.as_ref().unwrap()),
      app(
        cst(prims.nat_succ.as_ref().unwrap()),
        app(
          cst(prims.nat_succ.as_ref().unwrap()),
          app(
            cst(prims.nat_succ.as_ref().unwrap()),
            app(
              cst(prims.nat_succ.as_ref().unwrap()),
              cst(prims.nat_zero.as_ref().unwrap()),
            ),
          ),
        ),
      ),
    );
    assert!(is_def_eq(&env, &prims, &nat_lit(5), &succ5).unwrap());
    // 5 != succ^4 zero
    let succ4 = app(
      cst(prims.nat_succ.as_ref().unwrap()),
      app(
        cst(prims.nat_succ.as_ref().unwrap()),
        app(
          cst(prims.nat_succ.as_ref().unwrap()),
          app(
            cst(prims.nat_succ.as_ref().unwrap()),
            cst(prims.nat_zero.as_ref().unwrap()),
          ),
        ),
      ),
    );
    assert!(!is_def_eq(&env, &prims, &nat_lit(5), &succ4).unwrap());
  }

  // -- fvar comparison --

  #[test]
  fn fvar_comparison() {
    let prims = test_prims();
    let env = empty_env();
    // Identical lambdas
    assert!(
      is_def_eq(
        &env,
        &prims,
        &lam(ty(), lam(ty(), bv(1))),
        &lam(ty(), lam(ty(), bv(1)))
      )
      .unwrap()
    );
    // Different bvar refs
    assert!(
      !is_def_eq(
        &env,
        &prims,
        &lam(ty(), lam(ty(), bv(1))),
        &lam(ty(), lam(ty(), bv(0)))
      )
      .unwrap()
    );
    // Pi with bvar codomain
    assert!(
      is_def_eq(
        &env,
        &prims,
        &pi(ty(), bv(0)),
        &pi(ty(), bv(0))
      )
      .unwrap()
    );
    assert!(
      !is_def_eq(
        &env,
        &prims,
        &pi(ty(), bv(0)),
        &pi(ty(), ty())
      )
      .unwrap()
    );
  }

  // -- pi defEq --

  #[test]
  fn pi_def_eq() {
    let prims = test_prims();
    // Π A. A → A
    let dep_pi = pi(ty(), pi(bv(0), bv(1)));
    let env = empty_env();
    assert!(is_def_eq(&env, &prims, &dep_pi, &dep_pi).unwrap());

    // Reduced domains
    let d_ty = mk_addr(200); // different from other tests
    let mut env2 = empty_env();
    add_def(
      &mut env2,
      &d_ty,
      srt(2),
      ty(),
      0,
      ReducibilityHints::Abbrev,
    );
    assert!(
      is_def_eq(
        &env2,
        &prims,
        &pi(cst(&d_ty), ty()),
        &pi(ty(), ty())
      )
      .unwrap()
    );

    // Different codomains
    assert!(
      !is_def_eq(&env, &prims, &pi(ty(), ty()), &pi(ty(), prop())).unwrap()
    );
    // Different domains
    assert!(
      !is_def_eq(
        &env,
        &prims,
        &pi(ty(), bv(0)),
        &pi(prop(), bv(0))
      )
      .unwrap()
    );
  }

  // -- native reduction (reduceBool/reduceNat) --

  #[test]
  fn native_reduction() {
    let mut prims = test_prims();
    let rb_addr = mk_addr(44);
    let rn_addr = mk_addr(45);
    prims.reduce_bool = Some(rb_addr.clone());
    prims.reduce_nat = Some(rn_addr.clone());

    let true_def = mk_addr(46);
    let false_def = mk_addr(47);
    let nat_def = mk_addr(48);
    let mut env = empty_env();
    add_def(
      &mut env,
      &true_def,
      cst(prims.bool_type.as_ref().unwrap()),
      cst(prims.bool_true.as_ref().unwrap()),
      0,
      ReducibilityHints::Abbrev,
    );
    add_def(
      &mut env,
      &false_def,
      cst(prims.bool_type.as_ref().unwrap()),
      cst(prims.bool_false.as_ref().unwrap()),
      0,
      ReducibilityHints::Abbrev,
    );
    add_def(
      &mut env,
      &nat_def,
      ty(),
      nat_lit(42),
      0,
      ReducibilityHints::Abbrev,
    );

    // reduceBool trueDef → Bool.true
    let rb_true = app(cst(&rb_addr), cst(&true_def));
    assert_eq!(
      whnf_quote(&env, &prims, &rb_true).unwrap(),
      cst(prims.bool_true.as_ref().unwrap())
    );

    // reduceBool falseDef → Bool.false
    let rb_false = app(cst(&rb_addr), cst(&false_def));
    assert_eq!(
      whnf_quote(&env, &prims, &rb_false).unwrap(),
      cst(prims.bool_false.as_ref().unwrap())
    );

    // reduceNat natDef → 42
    let rn_expr = app(cst(&rn_addr), cst(&nat_def));
    assert_eq!(
      whnf_quote(&env, &prims, &rn_expr).unwrap(),
      nat_lit(42)
    );
  }

  // -- iota edge cases --

  #[test]
  fn iota_edge_cases() {
    let prims = test_prims();
    let (env, nat_ind, zero, succ, rec) =
      build_my_nat_env(empty_env());
    let nat_const = cst(&nat_ind);
    let motive = lam(nat_const.clone(), ty());
    let base = nat_lit(0);
    let step = lam(
      nat_const.clone(),
      lam(ty(), app(cst(prims.nat_succ.as_ref().unwrap()), bv(0))),
    );

    // natLit as major on non-Nat rec stays stuck
    let rec_lit0 = app(
      app(
        app(app(cst(&rec), motive.clone()), base.clone()),
        step.clone(),
      ),
      nat_lit(0),
    );
    assert_eq!(
      whnf_head_addr(&env, &prims, &rec_lit0).unwrap(),
      Some(rec.clone())
    );

    // rec on succ zero = 1
    let one = app(cst(&succ), cst(&zero));
    let rec_one = app(
      app(app(app(cst(&rec), motive.clone()), base.clone()), step.clone()),
      one,
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_one).unwrap(), nat_lit(1));

    // rec on succ^4 zero = 4
    let four = app(
      cst(&succ),
      app(
        cst(&succ),
        app(cst(&succ), app(cst(&succ), cst(&zero))),
      ),
    );
    let rec_four = app(
      app(app(app(cst(&rec), motive.clone()), base.clone()), step.clone()),
      four,
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_four).unwrap(), nat_lit(4));

    // rec stuck on axiom
    let ax_addr = mk_addr(54);
    let mut env2 = env.clone();
    add_axiom(&mut env2, &ax_addr, nat_const);
    let rec_ax = app(
      app(
        app(app(cst(&rec), motive.clone()), base.clone()),
        step.clone(),
      ),
      cst(&ax_addr),
    );
    assert_eq!(
      whnf_head_addr(&env2, &prims, &rec_ax).unwrap(),
      Some(rec.clone())
    );

    // succ^5 zero = 5
    let five = app(
      cst(&succ),
      app(
        cst(&succ),
        app(
          cst(&succ),
          app(cst(&succ), app(cst(&succ), cst(&zero))),
        ),
      ),
    );
    let rec_five = app(
      app(app(app(cst(&rec), motive), base), step),
      five,
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_five).unwrap(), nat_lit(5));
  }

  // -- deep spine comparison --

  #[test]
  fn deep_spine() {
    let prims = test_prims();
    let f_type = pi(ty(), pi(ty(), pi(ty(), pi(ty(), ty()))));
    let f_addr = mk_addr(99);
    let g_addr = mk_addr(98);
    let f_body = lam(ty(), lam(ty(), lam(ty(), lam(ty(), bv(3)))));
    let mut env = empty_env();
    add_def(
      &mut env,
      &f_addr,
      f_type.clone(),
      f_body.clone(),
      0,
      ReducibilityHints::Abbrev,
    );
    add_def(
      &mut env,
      &g_addr,
      f_type,
      f_body,
      0,
      ReducibilityHints::Abbrev,
    );

    // f 1 2 == g 1 2
    let fg12a = app(app(cst(&f_addr), nat_lit(1)), nat_lit(2));
    let fg12b = app(app(cst(&g_addr), nat_lit(1)), nat_lit(2));
    assert!(is_def_eq(&env, &prims, &fg12a, &fg12b).unwrap());

    // f 1 2 3 4 == g 1 2 3 5 (both reduce to 1)
    let f1234 = app(
      app(app(app(cst(&f_addr), nat_lit(1)), nat_lit(2)), nat_lit(3)),
      nat_lit(4),
    );
    let g1235 = app(
      app(app(app(cst(&g_addr), nat_lit(1)), nat_lit(2)), nat_lit(3)),
      nat_lit(5),
    );
    assert!(is_def_eq(&env, &prims, &f1234, &g1235).unwrap());

    // f 1 2 3 4 != g 2 2 3 4 (reduces to 1 vs 2)
    let g2234 = app(
      app(app(app(cst(&g_addr), nat_lit(2)), nat_lit(2)), nat_lit(3)),
      nat_lit(4),
    );
    assert!(!is_def_eq(&env, &prims, &f1234, &g2234).unwrap());
  }

  // -- proj defEq --

  #[test]
  fn proj_def_eq() {
    let prims = test_prims();
    let (mut env, pair_ind, pair_ctor) = build_pair_env(empty_env());
    let mk37 = app(
      app(app(app(cst(&pair_ctor), ty()), ty()), nat_lit(3)),
      nat_lit(7),
    );

    // proj 0 == proj 0
    let proj0a = proj_e(&pair_ind, 0, mk37.clone());
    let proj0b = proj_e(&pair_ind, 0, mk37.clone());
    assert!(is_def_eq(&env, &prims, &proj0a, &proj0b).unwrap());

    // proj 0 != proj 1
    let proj1 = proj_e(&pair_ind, 1, mk37.clone());
    assert!(!is_def_eq(&env, &prims, &proj0a, &proj1).unwrap());

    // proj 0 (mk 3 7) == 3
    assert!(
      is_def_eq(&env, &prims, &proj0a, &nat_lit(3)).unwrap()
    );

    // proj on axiom: proj 0 ax == proj 0 ax
    let ax_addr = mk_addr(33);
    let pair_type = app(app(cst(&pair_ind), ty()), ty());
    add_axiom(&mut env, &ax_addr, pair_type);
    let proj_ax0 = proj_e(&pair_ind, 0, cst(&ax_addr));
    assert!(
      is_def_eq(&env, &prims, &proj_ax0, &proj_ax0).unwrap()
    );

    // proj 0 ax != proj 1 ax
    let proj_ax1 = proj_e(&pair_ind, 1, cst(&ax_addr));
    assert!(
      !is_def_eq(&env, &prims, &proj_ax0, &proj_ax1).unwrap()
    );
  }

  // -- errors extended --

  #[test]
  fn errors_extended() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat_const = cst(&nat_addr);

    // App type mismatch: (λ(x:Nat). x) Prop
    let bad_app = app(lam(nat_const.clone(), bv(0)), prop());
    assert!(infer_quote(&env, &prims, &bad_app).is_err());

    // Let type mismatch: let x : Nat := Prop in x
    let bad_let = let_e(nat_const, prop(), bv(0));
    assert!(infer_quote(&env, &prims, &bad_let).is_err());

    // Wrong univ level count
    let id_addr = mk_addr(240);
    let lvl_param = KLevel::param(0, anon());
    let param_sort = KExpr::sort(lvl_param);
    add_def(
      &mut env,
      &id_addr,
      pi(param_sort.clone(), param_sort.clone()),
      lam(param_sort, bv(0)),
      1,
      ReducibilityHints::Abbrev,
    );
    // 0 levels provided, expects 1
    assert!(infer_quote(&env, &prims, &cst(&id_addr)).is_err());

    // Non-sort domain in lambda
    let bad_lam = lam(nat_lit(5), bv(0));
    assert!(infer_quote(&env, &prims, &bad_lam).is_err());

    // Non-sort domain in forallE
    let bad_pi = pi(nat_lit(5), bv(0));
    assert!(infer_quote(&env, &prims, &bad_pi).is_err());
  }

  // -- defn typecheck (myAdd) --

  #[test]
  fn defn_typecheck_add() {
    use crate::ix::kernel::check::typecheck_const;

    let prims = test_prims();
    let (mut env, nat_ind, zero, succ, rec) =
      build_my_nat_env(empty_env());
    let nat_const = cst(&nat_ind);

    // myAdd : MyNat → MyNat → MyNat
    let add_addr = mk_addr(55);
    let add_type = pi(nat_const.clone(), pi(nat_const.clone(), nat_const.clone()));
    let motive = lam(nat_const.clone(), nat_const.clone());
    let base = bv(1); // n
    let step = lam(
      nat_const.clone(),
      lam(nat_const.clone(), app(cst(&succ), bv(0))),
    );
    let target = bv(0); // m
    let rec_app = app(
      app(app(app(cst(&rec), motive), base), step),
      target,
    );
    let add_body = lam(nat_const.clone(), lam(nat_const.clone(), rec_app));
    add_def(
      &mut env,
      &add_addr,
      add_type,
      add_body,
      0,
      ReducibilityHints::Regular(1),
    );

    // whnf of myAdd applied to concrete values
    let two = app(cst(&succ), app(cst(&succ), cst(&zero)));
    let three = app(
      cst(&succ),
      app(cst(&succ), app(cst(&succ), cst(&zero))),
    );
    let add_app = app(app(cst(&add_addr), two), three);
    assert!(whnf_quote(&env, &prims, &add_app).is_ok());

    // typecheck the constant
    let result = typecheck_const(&env, &prims, &add_addr, false);
    assert!(
      result.is_ok(),
      "myAdd typecheck failed: {:?}",
      result.err()
    );
  }
}
