//! Unit tests for Kernel2 NbE type checker.
//!
//! These tests mirror the Lean tests in `Tests/Ix/Kernel2/Unit.lean`.
//! They use synthetic environments (no IO, no Ixon loading) to test
//! eval, quote, whnf, isDefEq, infer, and type-checking.

#[cfg(test)]
mod tests {
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
    KExpr::cnst(MetaId::from_addr(addr.clone()), vec![])
  }
  fn cst_l(addr: &Address, lvls: Vec<KLevel<Meta>>) -> KExpr<Meta> {
    KExpr::cnst(MetaId::from_addr(addr.clone()), lvls)
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
    KExpr::proj(MetaId::from_addr(type_addr.clone()), idx, strct)
  }

  /// Build Primitives with consistent test addresses.
  fn test_prims() -> Primitives<Meta> {
    let mid = |b: &[u8]| MetaId::from_addr(Address::hash(b));
    Primitives {
      nat: Some(mid(b"Nat")),
      nat_zero: Some(mid(b"Nat.zero")),
      nat_succ: Some(mid(b"Nat.succ")),
      nat_add: Some(mid(b"Nat.add")),
      nat_pred: Some(mid(b"Nat.pred")),
      nat_sub: Some(mid(b"Nat.sub")),
      nat_mul: Some(mid(b"Nat.mul")),
      nat_pow: Some(mid(b"Nat.pow")),
      nat_gcd: Some(mid(b"Nat.gcd")),
      nat_mod: Some(mid(b"Nat.mod")),
      nat_div: Some(mid(b"Nat.div")),
      nat_bitwise: Some(mid(b"Nat.bitwise")),
      nat_beq: Some(mid(b"Nat.beq")),
      nat_ble: Some(mid(b"Nat.ble")),
      nat_land: Some(mid(b"Nat.land")),
      nat_lor: Some(mid(b"Nat.lor")),
      nat_xor: Some(mid(b"Nat.xor")),
      nat_shift_left: Some(mid(b"Nat.shiftLeft")),
      nat_shift_right: Some(mid(b"Nat.shiftRight")),
      bool_type: Some(mid(b"Bool")),
      bool_true: Some(mid(b"Bool.true")),
      bool_false: Some(mid(b"Bool.false")),
      string: Some(mid(b"String")),
      string_mk: Some(mid(b"String.mk")),
      char_type: Some(mid(b"Char")),
      char_mk: Some(mid(b"Char.ofNat")),
      string_of_list: Some(mid(b"String.mk")),
      list: Some(mid(b"List")),
      list_nil: Some(mid(b"List.nil")),
      list_cons: Some(mid(b"List.cons")),
      eq: Some(mid(b"Eq")),
      eq_refl: Some(mid(b"Eq.refl")),
      quot_type: None,
      quot_ctor: None,
      quot_lift: None,
      quot_ind: None,
      reduce_bool: None,
      reduce_nat: None,
      eager_reduce: None,
      system_platform_num_bits: None,
    }
  }

  // -- Test runners --

  /// Evaluate an expression, then quote it back.
  fn eval_quote(
    env: &KEnv<Meta>,
    prims: &Primitives<Meta>,
    e: &KExpr<Meta>,
  ) -> Result<KExpr<Meta>, String> {
    let mut tc = TypeChecker::new(env, prims);
    let val = tc.eval(e, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    tc.quote(&val, 0).map_err(|e| format!("{e}"))
  }

  /// Evaluate, WHNF, then quote.
  fn whnf_quote(
    env: &KEnv<Meta>,
    prims: &Primitives<Meta>,
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
    prims: &Primitives<Meta>,
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
    prims: &Primitives<Meta>,
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
    prims: &Primitives<Meta>,
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
    prims: &Primitives<Meta>,
    e: &KExpr<Meta>,
  ) -> Result<Option<Address>, String> {
    let mut tc = TypeChecker::new(env, prims);
    let val = tc.eval(e, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    let w = tc.whnf_val(&val, 0).map_err(|e| format!("{e}"))?;
    match w.inner() {
      ValInner::Neutral {
        head: Head::Const { id, .. },
        ..
      } => Ok(Some(id.addr.clone())),
      ValInner::Ctor { id, .. } => Ok(Some(id.addr.clone())),
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
      MetaId::from_addr(addr.clone()),
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
        all: vec![MetaId::from_addr(addr.clone())],
      }),
    );
  }

  fn add_axiom(env: &mut KEnv<Meta>, addr: &Address, typ: KExpr<Meta>) {
    env.insert(
      MetaId::from_addr(addr.clone()),
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
      MetaId::from_addr(addr.clone()),
      KConstantInfo::Opaque(KOpaqueVal {
        cv: KConstantVal {
          num_levels: 0,
          typ,
          name: anon(),
          level_params: vec![],
        },
        value,
        is_unsafe: false,
        all: vec![MetaId::from_addr(addr.clone())],
      }),
    );
  }

  fn add_theorem(env: &mut KEnv<Meta>, addr: &Address, typ: KExpr<Meta>, value: KExpr<Meta>) {
    env.insert(
      MetaId::from_addr(addr.clone()),
      KConstantInfo::Theorem(KTheoremVal {
        cv: KConstantVal {
          num_levels: 0,
          typ,
          name: anon(),
          level_params: vec![],
        },
        value,
        all: vec![MetaId::from_addr(addr.clone())],
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
      MetaId::from_addr(addr.clone()),
      KConstantInfo::Inductive(KInductiveVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        num_params,
        num_indices,
        all: all.into_iter().map(MetaId::from_addr).collect(),
        ctors: ctors.into_iter().map(MetaId::from_addr).collect(),
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
      MetaId::from_addr(addr.clone()),
      KConstantInfo::Constructor(KConstructorVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        induct: MetaId::from_addr(induct.clone()),
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
      MetaId::from_addr(addr.clone()),
      KConstantInfo::Recursor(KRecursorVal {
        cv: KConstantVal {
          num_levels,
          typ,
          name: anon(),
          level_params: vec![],
        },
        all: all.into_iter().map(MetaId::from_addr).collect(),
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
      MetaId::from_addr(addr.clone()),
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

    // Lambda domain annotations must match the recType forall domains exactly:
    //   dom0 (motive) = MyNat → Type
    //   dom1 (base)   = motive zero
    //   dom2 (step)   = ∀ (n : MyNat), motive n → motive (succ n)
    let motive_dom = pi(nat_const.clone(), ty());
    let base_dom = app(bv(0), cst(&zero));
    let step_dom = pi(
      nat_const.clone(),
      pi(app(bv(2), bv(0)), app(bv(3), app(cst(&succ), bv(1)))),
    );
    // Rule for zero: nfields=0, rhs = λ motive base step => base
    let zero_rhs = lam(motive_dom.clone(), lam(base_dom.clone(), lam(step_dom.clone(), bv(1))));
    // Rule for succ: nfields=1, rhs = λ motive base step n => step n (rec motive base step n)
    let succ_rhs = lam(
      motive_dom,
      lam(
        base_dom,
        lam(
          step_dom,
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
          ctor: MetaId::from_addr(zero.clone()),
          nfields: 0,
          rhs: zero_rhs,
        },
        KRecursorRule {
          ctor: MetaId::from_addr(succ.clone()),
          nfields: 1,
          rhs: succ_rhs,
        },
      ],
      false,
    );

    (env, nat_ind, zero, succ, rec)
  }

  /// Build MyList inductive (universe-polymorphic).
  /// Returns (env, list_ind, nil, cons, rec).
  /// List.{u} : Type u → Type u
  /// nil.{u} : {α : Type u} → List α
  /// cons.{u} : {α : Type u} → α → List α → List α
  /// rec.{u,v} : {α : Type u} → {motive : List α → Sort v}
  ///   → motive nil → ((head : α) → (tail : List α) → motive tail → motive (head :: tail))
  ///   → (t : List α) → motive t
  fn build_my_list_env(
    mut env: KEnv<Meta>,
  ) -> (KEnv<Meta>, Address, Address, Address, Address) {
    let list_ind = mk_addr(200);
    let nil = mk_addr(201);
    let cons = mk_addr(202);
    let rec = mk_addr(203);

    // List.{u} : Type u → Type u
    // As an expr: ∀ (α : Sort (u+1)), Sort (u+1)
    // Simplified: we use num_levels=1 and represent as Type → Type
    let list_type = pi(ty(), ty()); // ∀ (α : Type), Type

    add_inductive(
      &mut env,
      &list_ind,
      list_type,
      vec![nil.clone(), cons.clone()],
      1,    // num_params = 1 (α)
      0,    // num_indices = 0
      true, // is_rec
      1,    // num_levels = 1 (u)
      vec![list_ind.clone()],
    );

    // nil : {α : Type} → List α
    // In our simplified env: ∀ (α : Type), List α
    let nil_type = pi(ty(), app(cst(&list_ind), bv(0)));
    add_ctor(&mut env, &nil, &list_ind, nil_type, 0, 1, 0, 1);

    // cons : {α : Type} → α → List α → List α
    let _list_alpha = app(cst(&list_ind), bv(0)); // List (bv 0) where bv 0 = α
    let cons_type = pi(
      ty(), // α : Type
      pi(
        bv(0), // head : α
        pi(
          app(cst(&list_ind), bv(1)), // tail : List α
          app(cst(&list_ind), bv(2)), // result : List α
        ),
      ),
    );
    add_ctor(&mut env, &cons, &list_ind, cons_type, 1, 1, 2, 1);

    // rec : {α : Type} → {motive : List α → Type}
    //   → motive (nil α) → ((head : α) → (tail : List α) → motive tail → motive (cons α head tail))
    //   → (t : List α) → motive t
    //
    // As de Bruijn (all binders implicit, outermost = highest index):
    //   ∀ (α : Type),                                              -- bv 4 (from inside)
    //     ∀ (motive : List α → Type),                              -- bv 3
    //       ∀ (nil_case : motive (nil α)),                         -- bv 2
    //         ∀ (cons_case : ∀ (head : α) (tail : List α), motive tail → motive (cons α head tail)),  -- bv 1
    //           ∀ (t : List α), motive t                           -- bv 0
    let _list_a = app(cst(&list_ind), bv(0)); // List α  (α = bv 0 in current scope)
    let rec_type = pi(
      ty(), // α : Type
      pi(
        pi(app(cst(&list_ind), bv(0)), ty()), // motive : List α → Type
        pi(
          app(bv(0), app(cst(&nil), bv(1))), // nil_case : motive (nil α)
          pi(
            pi(
              bv(2), // head : α
              pi(
                app(cst(&list_ind), bv(3)), // tail : List α
                pi(
                  app(bv(4), bv(0)), // motive tail
                  app(bv(5), app(app(app(cst(&cons), bv(5)), bv(2)), bv(1))), // motive (cons α head tail)
                ),
              ),
            ),
            pi(app(cst(&list_ind), bv(3)), app(bv(3), bv(0))), // (t : List α) → motive t
          ),
        ),
      ),
    );

    // Rule for nil: nfields=0, rhs = λ α motive nil_case cons_case => nil_case
    let nil_rhs = lam(
      ty(),
      lam(
        pi(app(cst(&list_ind), bv(0)), ty()),
        lam(
          app(bv(0), app(cst(&nil), bv(1))),
          lam(
            ty(), // cons_case domain placeholder
            bv(1), // nil_case
          ),
        ),
      ),
    );

    // Rule for cons: nfields=2, rhs = λ α motive nil_case cons_case head tail =>
    //   cons_case head tail (rec α motive nil_case cons_case tail)
    let cons_rhs = lam(
      ty(), // α
      lam(
        pi(app(cst(&list_ind), bv(0)), ty()), // motive
        lam(
          app(bv(0), app(cst(&nil), bv(1))), // nil_case
          lam(
            ty(), // cons_case domain placeholder
            lam(
              bv(3), // head : α
              lam(
                app(cst(&list_ind), bv(4)), // tail : List α
                app(
                  app(
                    app(bv(2), bv(1)), // cons_case head tail
                    bv(0),
                  ),
                  app(
                    app(app(app(app(cst(&rec), bv(5)), bv(4)), bv(3)), bv(2)),
                    bv(0), // rec α motive nil_case cons_case tail
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    );

    add_rec(
      &mut env,
      &rec,
      2,    // num_levels = 2 (u, v)
      rec_type,
      vec![list_ind.clone()],
      1,    // num_params = 1 (α)
      0,    // num_indices = 0
      1,    // num_motives = 1
      2,    // num_minors = 2 (nil, cons)
      vec![
        KRecursorRule {
          ctor: MetaId::from_addr(nil.clone()),
          nfields: 0,
          rhs: nil_rhs,
        },
        KRecursorRule {
          ctor: MetaId::from_addr(cons.clone()),
          nfields: 2,
          rhs: cons_rhs,
        },
      ],
      false,
    );

    (env, list_ind, nil, cons, rec)
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
    // Lambda domain annotations must match the recType forall domains exactly:
    //   dom0 (motive) = MyTrue → Prop
    //   dom1 (h)      = motive intro
    let motive_dom = pi(true_const.clone(), prop());
    let h_dom = app(bv(0), cst(&intro));
    let rule_rhs = lam(motive_dom, lam(h_dom, bv(0)));

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
        ctor: MetaId::from_addr(intro.clone()),
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
    KEnv::default()
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
      app(cst(&prims.nat_add.as_ref().unwrap().addr), nat_lit(2)),
      nat_lit(3),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(5));
  }

  #[test]
  fn nat_mul() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(&prims.nat_mul.as_ref().unwrap().addr), nat_lit(4)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(20));
  }

  #[test]
  fn nat_sub() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(&prims.nat_sub.as_ref().unwrap().addr), nat_lit(10)),
      nat_lit(3),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(7));
    // Truncated: 3 - 10 = 0
    let e2 = app(
      app(cst(&prims.nat_sub.as_ref().unwrap().addr), nat_lit(3)),
      nat_lit(10),
    );
    assert_eq!(whnf_quote(&env, &prims, &e2).unwrap(), nat_lit(0));
  }

  #[test]
  fn nat_pow() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(&prims.nat_pow.as_ref().unwrap().addr), nat_lit(2)),
      nat_lit(10),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(1024));
  }

  #[test]
  fn nat_succ() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(cst(&prims.nat_succ.as_ref().unwrap().addr), nat_lit(41));
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(42));
  }

  #[test]
  fn nat_mod_div() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(&prims.nat_mod.as_ref().unwrap().addr), nat_lit(17)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(2));
    let e2 = app(
      app(cst(&prims.nat_div.as_ref().unwrap().addr), nat_lit(17)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e2).unwrap(), nat_lit(3));
  }

  #[test]
  fn nat_beq_ble() {
    let env = empty_env();
    let prims = test_prims();
    let beq_true = app(
      app(cst(&prims.nat_beq.as_ref().unwrap().addr), nat_lit(5)),
      nat_lit(5),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &beq_true).unwrap(),
      cst(&prims.bool_true.as_ref().unwrap().addr)
    );
    let beq_false = app(
      app(cst(&prims.nat_beq.as_ref().unwrap().addr), nat_lit(5)),
      nat_lit(6),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &beq_false).unwrap(),
      cst(&prims.bool_false.as_ref().unwrap().addr)
    );
    let ble_true = app(
      app(cst(&prims.nat_ble.as_ref().unwrap().addr), nat_lit(3)),
      nat_lit(5),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &ble_true).unwrap(),
      cst(&prims.bool_true.as_ref().unwrap().addr)
    );
    let ble_false = app(
      app(cst(&prims.nat_ble.as_ref().unwrap().addr), nat_lit(5)),
      nat_lit(3),
    );
    assert_eq!(
      whnf_quote(&env, &prims, &ble_false).unwrap(),
      cst(&prims.bool_false.as_ref().unwrap().addr)
    );
  }

  // -- large nat --

  #[test]
  fn large_nat() {
    let env = empty_env();
    let prims = test_prims();
    let e = app(
      app(cst(&prims.nat_pow.as_ref().unwrap().addr), nat_lit(2)),
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
      app(cst(&prims.nat_gcd.as_ref().unwrap().addr), nat_lit(12)),
      nat_lit(8),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(4));
    // land 10 12 = 8
    let e = app(
      app(cst(&prims.nat_land.as_ref().unwrap().addr), nat_lit(10)),
      nat_lit(12),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(8));
    // lor 10 5 = 15
    let e = app(
      app(cst(&prims.nat_lor.as_ref().unwrap().addr), nat_lit(10)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(15));
    // xor 10 12 = 6
    let e = app(
      app(cst(&prims.nat_xor.as_ref().unwrap().addr), nat_lit(10)),
      nat_lit(12),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(6));
    // shiftLeft 1 10 = 1024
    let e = app(
      app(cst(&prims.nat_shift_left.as_ref().unwrap().addr), nat_lit(1)),
      nat_lit(10),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(1024));
    // shiftRight 1024 3 = 128
    let e = app(
      app(
        cst(&prims.nat_shift_right.as_ref().unwrap().addr),
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
      app(cst(&prims.nat_div.as_ref().unwrap().addr), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // mod 0 0 = 0
    let e = app(
      app(cst(&prims.nat_mod.as_ref().unwrap().addr), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // gcd 0 0 = 0
    let e = app(
      app(cst(&prims.nat_gcd.as_ref().unwrap().addr), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // sub 0 0 = 0
    let e = app(
      app(cst(&prims.nat_sub.as_ref().unwrap().addr), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // pow 0 0 = 1
    let e = app(
      app(cst(&prims.nat_pow.as_ref().unwrap().addr), nat_lit(0)),
      nat_lit(0),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(1));
    // mul 0 999 = 0
    let e = app(
      app(cst(&prims.nat_mul.as_ref().unwrap().addr), nat_lit(0)),
      nat_lit(999),
    );
    assert_eq!(whnf_quote(&env, &prims, &e).unwrap(), nat_lit(0));
    // chained: (3*4) + (10-3) = 19
    let inner1 = app(
      app(cst(&prims.nat_mul.as_ref().unwrap().addr), nat_lit(3)),
      nat_lit(4),
    );
    let inner2 = app(
      app(cst(&prims.nat_sub.as_ref().unwrap().addr), nat_lit(10)),
      nat_lit(3),
    );
    let chained =
      app(app(cst(&prims.nat_add.as_ref().unwrap().addr), inner1), inner2);
    assert_eq!(whnf_quote(&env, &prims, &chained).unwrap(), nat_lit(19));
  }

  // -- delta unfolding --

  #[test]
  fn delta_unfolding() {
    let prims = test_prims();
    let def_addr = mk_addr(1);
    let add_body = app(
      app(cst(&prims.nat_add.as_ref().unwrap().addr), nat_lit(2)),
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
      app(cst(&prims.nat_add.as_ref().unwrap().addr), cst(&def_addr)),
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
      app(cst(&prims.nat_add.as_ref().unwrap().addr), cst(&ax_addr)),
      nat_lit(5),
    );
    assert_eq!(
      whnf_head_addr(&env, &prims, &stuck_add).unwrap(),
      Some(prims.nat_add.as_ref().unwrap().addr.clone())
    );

    // Nat.add axiom (Nat.succ axiom): second arg IS structural succ,
    // so step-case fires: add x (succ y) → succ (add x y)
    let succ_axiom = app(cst(&prims.nat_succ.as_ref().unwrap().addr), cst(&ax_addr));
    let stuck_add_succ = app(
      app(cst(&prims.nat_add.as_ref().unwrap().addr), cst(&ax_addr)),
      succ_axiom,
    );
    assert_eq!(
      whnf_head_addr(&env, &prims, &stuck_add_succ).unwrap(),
      Some(prims.nat_succ.as_ref().unwrap().addr.clone())
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
        app(cst(&prims.nat_add.as_ref().unwrap().addr), bv(0)),
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
      lam(ty(), app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0)));
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
      lam(ty(), app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0))),
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
      lam(ty(), app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0))),
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

  // -- List.rec iota reduction --

  #[test]
  fn list_rec_nil() {
    let prims = test_prims();
    let (env, _list_ind, nil, _cons, rec) =
      build_my_list_env(empty_env());

    // List.rec α motive nil_case cons_case (nil α) = nil_case
    // We use Type as α, and a trivial motive
    let alpha = ty();
    let list_alpha = app(cst(&_list_ind), alpha.clone());
    let motive = lam(list_alpha.clone(), ty()); // motive : List α → Type
    let nil_case = nat_lit(42); // use a nat literal as the nil result
    let cons_case = lam(
      alpha.clone(),
      lam(list_alpha.clone(), lam(ty(), nat_lit(99))),
    );
    let nil_val = app(cst(&nil), alpha.clone());

    let rec_nil = app(
      app(app(app(app(cst(&rec), alpha.clone()), motive), nil_case.clone()), cons_case),
      nil_val,
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_nil).unwrap(), nat_lit(42));
  }

  #[test]
  fn list_rec_cons() {
    let prims = test_prims();
    let (env, _list_ind, nil, cons, rec) =
      build_my_list_env(empty_env());

    let alpha = ty();
    let list_alpha = app(cst(&_list_ind), alpha.clone());
    let motive = lam(list_alpha.clone(), ty());
    let nil_case = nat_lit(0);
    // cons_case : α → List α → motive tail → Nat
    // Just returns 1 + recursive result (using nat succ)
    let cons_case = lam(
      alpha.clone(),
      lam(list_alpha.clone(), lam(ty(), app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0)))),
    );

    // Build: cons α elem (nil α)  — a single-element list
    let elem = nat_lit(7);
    let one_list = app(app(app(cst(&cons), alpha.clone()), elem), app(cst(&nil), alpha.clone()));

    // rec α motive 0 cons_case (cons α 7 nil) should reduce:
    //   cons_case 7 nil (rec α motive 0 cons_case nil)
    //   = succ (rec α motive 0 cons_case nil)
    //   = succ 0
    //   = 1
    let rec_one = app(
      app(app(app(app(cst(&rec), alpha.clone()), motive), nil_case), cons_case),
      one_list,
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_one).unwrap(), nat_lit(1));
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
      lam(ty(), app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0))),
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

    // Create a proposition P : Prop, then two proofs p1 : P, p2 : P
    let p_addr = mk_addr(129);
    let ax1 = mk_addr(130);
    let ax2 = mk_addr(131);
    let mut env = empty_env();
    add_axiom(&mut env, &p_addr, prop()); // P : Prop
    add_axiom(&mut env, &ax1, cst(&p_addr)); // p1 : P
    add_axiom(&mut env, &ax2, cst(&p_addr)); // p2 : P
    // Two proofs of the same Prop are defEq (proof irrelevance)
    assert_eq!(
      is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap(),
      true
    );

    // Two distinct propositions (type Prop) are NOT defEq
    let q1 = mk_addr(132);
    let q2 = mk_addr(133);
    let mut env2 = empty_env();
    add_axiom(&mut env2, &q1, prop()); // Q1 : Prop
    add_axiom(&mut env2, &q2, prop()); // Q2 : Prop
    assert_eq!(
      is_def_eq(&env2, &prims, &cst(&q1), &cst(&q2)).unwrap(),
      false
    );

    // Two Type axioms are NOT defEq
    let t1 = mk_addr(134);
    let t2 = mk_addr(135);
    let mut env3 = empty_env();
    add_axiom(&mut env3, &t1, ty());
    add_axiom(&mut env3, &t2, ty());
    assert_eq!(
      is_def_eq(&env3, &prims, &cst(&t1), &cst(&t2)).unwrap(),
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
      app(cst(&prims.nat_add.as_ref().unwrap().addr), nat_lit(2)),
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
    let succ0 = app(cst(&prims.nat_succ.as_ref().unwrap().addr), nat_lit(0));
    assert!(is_def_eq(&env, &prims, &succ0, &nat_lit(1)).unwrap());
    // Nat.zero == 0
    assert!(
      is_def_eq(
        &env,
        &prims,
        &cst(&prims.nat_zero.as_ref().unwrap().addr),
        &nat_lit(0)
      )
      .unwrap()
    );
    // succ(succ(zero)) == 2
    let succ_succ_zero = app(
      cst(&prims.nat_succ.as_ref().unwrap().addr),
      app(
        cst(&prims.nat_succ.as_ref().unwrap().addr),
        cst(&prims.nat_zero.as_ref().unwrap().addr),
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
      app(cst(&prims.nat_add.as_ref().unwrap().addr), bv(1)),
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
      app(cst(&prims.nat_beq.as_ref().unwrap().addr), nat_lit(5)),
      nat_lit(5),
    );
    assert!(
      is_def_eq(
        &env,
        &prims,
        &cst(&prims.bool_true.as_ref().unwrap().addr),
        &beq55
      )
      .unwrap()
    );
    let beq56 = app(
      app(cst(&prims.nat_beq.as_ref().unwrap().addr), nat_lit(5)),
      nat_lit(6),
    );
    assert!(
      !is_def_eq(
        &env,
        &prims,
        &beq56,
        &cst(&prims.bool_true.as_ref().unwrap().addr)
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
        ctor: MetaId::from_addr(wrap_mk.clone()),
        nfields: 1,
        rhs: rule_rhs,
      }],
      false,
    );

    // rec (λ_. Nat) (λa. succ a) (mk Nat 5) = 6
    let motive = lam(app(cst(&wrap_ind), ty()), ty());
    let minor = lam(
      ty(),
      app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0)),
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
      app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0)),
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
      cst(&prims.nat.as_ref().unwrap().addr)
    );
    // strLit "hi" : String
    assert_eq!(
      infer_quote(&env, &prims, &str_lit("hi")).unwrap(),
      cst(&prims.string.as_ref().unwrap().addr)
    );
  }

  #[test]
  fn infer_lambda() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
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
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
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
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
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
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
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
    let char_type = cst(&prims.char_type.as_ref().unwrap().addr);
    let nil_char = app(
      cst_l(&prims.list_nil.as_ref().unwrap().addr, vec![KLevel::zero()]),
      char_type.clone(),
    );
    let empty_str =
      app(cst(&prims.string_mk.as_ref().unwrap().addr), nil_char.clone());
    assert!(
      is_def_eq(&env, &prims, &str_lit(""), &empty_str).unwrap()
    );

    // "a" == String.mk (List.cons Char (Char.mk 97) nil)
    let char_a =
      app(cst(&prims.char_mk.as_ref().unwrap().addr), nat_lit(97));
    let cons_a = app(
      app(
        app(
          cst_l(
            &prims.list_cons.as_ref().unwrap().addr,
            vec![KLevel::zero()],
          ),
          char_type,
        ),
        char_a,
      ),
      nil_char,
    );
    let str_a = app(cst(&prims.string_mk.as_ref().unwrap().addr), cons_a);
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
      app(cst(&prims.nat_add.as_ref().unwrap().addr), nat_lit(2)),
      nat_lit(3),
    );
    let add32 = app(
      app(cst(&prims.nat_add.as_ref().unwrap().addr), nat_lit(3)),
      nat_lit(2),
    );
    assert!(is_def_eq(&env, &prims, &add23, &add32).unwrap());
    // 2*3 + 1 == 7
    let expr1 = app(
      app(
        cst(&prims.nat_add.as_ref().unwrap().addr),
        app(
          app(cst(&prims.nat_mul.as_ref().unwrap().addr), nat_lit(2)),
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
        &cst(&prims.nat_zero.as_ref().unwrap().addr)
      )
      .unwrap()
    );
    // Nat.zero == 0
    assert!(
      is_def_eq(
        &env,
        &prims,
        &cst(&prims.nat_zero.as_ref().unwrap().addr),
        &nat_lit(0)
      )
      .unwrap()
    );
    // 1 == succ zero
    let succ_zero = app(
      cst(&prims.nat_succ.as_ref().unwrap().addr),
      cst(&prims.nat_zero.as_ref().unwrap().addr),
    );
    assert!(
      is_def_eq(&env, &prims, &nat_lit(1), &succ_zero).unwrap()
    );
    // 5 == succ^5 zero
    let succ5 = app(
      cst(&prims.nat_succ.as_ref().unwrap().addr),
      app(
        cst(&prims.nat_succ.as_ref().unwrap().addr),
        app(
          cst(&prims.nat_succ.as_ref().unwrap().addr),
          app(
            cst(&prims.nat_succ.as_ref().unwrap().addr),
            app(
              cst(&prims.nat_succ.as_ref().unwrap().addr),
              cst(&prims.nat_zero.as_ref().unwrap().addr),
            ),
          ),
        ),
      ),
    );
    assert!(is_def_eq(&env, &prims, &nat_lit(5), &succ5).unwrap());
    // 5 != succ^4 zero
    let succ4 = app(
      cst(&prims.nat_succ.as_ref().unwrap().addr),
      app(
        cst(&prims.nat_succ.as_ref().unwrap().addr),
        app(
          cst(&prims.nat_succ.as_ref().unwrap().addr),
          app(
            cst(&prims.nat_succ.as_ref().unwrap().addr),
            cst(&prims.nat_zero.as_ref().unwrap().addr),
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
    prims.reduce_bool = Some(MetaId::from_addr(rb_addr.clone()));
    prims.reduce_nat = Some(MetaId::from_addr(rn_addr.clone()));

    let true_def = mk_addr(46);
    let false_def = mk_addr(47);
    let nat_def = mk_addr(48);
    let mut env = empty_env();
    add_def(
      &mut env,
      &true_def,
      cst(&prims.bool_type.as_ref().unwrap().addr),
      cst(&prims.bool_true.as_ref().unwrap().addr),
      0,
      ReducibilityHints::Abbrev,
    );
    add_def(
      &mut env,
      &false_def,
      cst(&prims.bool_type.as_ref().unwrap().addr),
      cst(&prims.bool_false.as_ref().unwrap().addr),
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
      cst(&prims.bool_true.as_ref().unwrap().addr)
    );

    // reduceBool falseDef → Bool.false
    let rb_false = app(cst(&rb_addr), cst(&false_def));
    assert_eq!(
      whnf_quote(&env, &prims, &rb_false).unwrap(),
      cst(&prims.bool_false.as_ref().unwrap().addr)
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
      lam(ty(), app(cst(&prims.nat_succ.as_ref().unwrap().addr), bv(0))),
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
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
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
    let result = typecheck_const(&env, &prims, &MetaId::from_addr(add_addr.clone()), false);
    assert!(
      result.is_ok(),
      "myAdd typecheck failed: {:?}",
      result.err()
    );
  }

  // ==========================================================================
  // Group A: Proof Irrelevance
  // ==========================================================================

  #[test]
  fn proof_irrel_basic() {
    let prims = test_prims();
    let (mut env, true_ind, _intro, _rec) = build_my_true_env(empty_env());
    let p1 = mk_addr(300);
    let p2 = mk_addr(301);
    add_axiom(&mut env, &p1, cst(&true_ind));
    add_axiom(&mut env, &p2, cst(&true_ind));
    // Two proofs of a Prop are defeq
    assert!(is_def_eq(&env, &prims, &cst(&p1), &cst(&p2)).unwrap());
  }

  #[test]
  fn proof_irrel_different_prop_types() {
    let prims = test_prims();
    // Build MyTrue
    let (mut env, true_ind, _intro, _rec) = build_my_true_env(empty_env());
    // Build MyFalse : Prop (empty, no ctors)
    let false_ind = mk_addr(302);
    add_inductive(
      &mut env,
      &false_ind,
      prop(),
      vec![],
      0, 0, false, 0,
      vec![false_ind.clone()],
    );
    let p1 = mk_addr(303);
    let p2 = mk_addr(304);
    add_axiom(&mut env, &p1, cst(&true_ind));
    add_axiom(&mut env, &p2, cst(&false_ind));
    // Proofs of different types are NOT defeq
    assert!(!is_def_eq(&env, &prims, &cst(&p1), &cst(&p2)).unwrap());
  }

  #[test]
  fn proof_irrel_not_prop() {
    let prims = test_prims();
    let (mut env, nat_ind, _zero, _succ, _rec) = build_my_nat_env(empty_env());
    let n1 = mk_addr(305);
    let n2 = mk_addr(306);
    add_axiom(&mut env, &n1, cst(&nat_ind));
    add_axiom(&mut env, &n2, cst(&nat_ind));
    // Two axioms of Type (not Prop) are NOT defeq
    assert!(!is_def_eq(&env, &prims, &cst(&n1), &cst(&n2)).unwrap());
  }

  #[test]
  fn proof_irrel_under_lambda() {
    let prims = test_prims();
    let (mut env, true_ind, _intro, _rec) = build_my_true_env(empty_env());
    let p1 = mk_addr(307);
    let p2 = mk_addr(308);
    add_axiom(&mut env, &p1, cst(&true_ind));
    add_axiom(&mut env, &p2, cst(&true_ind));
    // λ(x:Type). p1 == λ(x:Type). p2
    let l1 = lam(ty(), cst(&p1));
    let l2 = lam(ty(), cst(&p2));
    assert!(is_def_eq(&env, &prims, &l1, &l2).unwrap());
  }

  #[test]
  fn proof_irrel_intro_vs_axiom() {
    let prims = test_prims();
    let (mut env, true_ind, intro, _rec) = build_my_true_env(empty_env());
    let p1 = mk_addr(309);
    add_axiom(&mut env, &p1, cst(&true_ind));
    // The constructor intro and an axiom p1 are both proofs of MyTrue → defeq
    assert!(is_def_eq(&env, &prims, &cst(&intro), &cst(&p1)).unwrap());
  }

  // ==========================================================================
  // Group B: Nat Literal / Constructor Equivalence (supplemental)
  // ==========================================================================

  #[test]
  fn nat_large_literal_eq() {
    let prims = test_prims();
    let env = empty_env();
    // O(1) literal comparison for large nats
    assert!(
      is_def_eq(&env, &prims, &nat_lit(1_000_000), &nat_lit(1_000_000)).unwrap()
    );
    assert!(
      !is_def_eq(&env, &prims, &nat_lit(1_000_000), &nat_lit(1_000_001)).unwrap()
    );
  }

  #[test]
  fn nat_succ_symbolic() {
    let prims = test_prims();
    let (mut env, nat_ind, _zero, _succ, _rec) = build_my_nat_env(empty_env());
    let x = mk_addr(310);
    let y = mk_addr(311);
    add_axiom(&mut env, &x, cst(&nat_ind));
    add_axiom(&mut env, &y, cst(&nat_ind));
    // Nat.succ(x) == Nat.succ(x)
    let sx = app(cst(&prims.nat_succ.as_ref().unwrap().addr), cst(&x));
    let sx2 = app(cst(&prims.nat_succ.as_ref().unwrap().addr), cst(&x));
    assert!(is_def_eq(&env, &prims, &sx, &sx2).unwrap());
    // Nat.succ(x) != Nat.succ(y)
    let sy = app(cst(&prims.nat_succ.as_ref().unwrap().addr), cst(&y));
    assert!(!is_def_eq(&env, &prims, &sx, &sy).unwrap());
  }

  #[test]
  fn nat_lit_zero_roundtrip() {
    let prims = test_prims();
    let env = empty_env();
    // nat_lit(0) whnf stays as nat_lit(0)
    assert_eq!(whnf_quote(&env, &prims, &nat_lit(0)).unwrap(), nat_lit(0));
  }

  // ==========================================================================
  // Group C: Lazy Delta / Hint Ordering (supplemental)
  // ==========================================================================

  #[test]
  fn lazy_delta_same_head_axiom_spine() {
    let prims = test_prims();
    let f = mk_addr(312);
    let mut env = empty_env();
    add_axiom(&mut env, &f, pi(ty(), pi(ty(), ty())));
    // f 1 2 == f 1 2 (same head, same spine → true)
    let fa = app(app(cst(&f), nat_lit(1)), nat_lit(2));
    let fb = app(app(cst(&f), nat_lit(1)), nat_lit(2));
    assert!(is_def_eq(&env, &prims, &fa, &fb).unwrap());
    // f 1 2 != f 1 3 (same head, different spine → false)
    let fc = app(app(cst(&f), nat_lit(1)), nat_lit(3));
    assert!(!is_def_eq(&env, &prims, &fa, &fc).unwrap());
  }

  #[test]
  fn lazy_delta_theorem_unfolded() {
    let prims = test_prims();
    let thm_addr = mk_addr(313);
    let mut env = empty_env();
    // Theorems ARE unfolded by delta in defEq
    add_theorem(&mut env, &thm_addr, ty(), nat_lit(5));
    assert!(
      is_def_eq(&env, &prims, &cst(&thm_addr), &nat_lit(5)).unwrap()
    );
    // But two different theorems with different bodies are not defeq by head
    let thm2 = mk_addr(337);
    add_theorem(&mut env, &thm2, ty(), nat_lit(6));
    assert!(
      !is_def_eq(&env, &prims, &cst(&thm_addr), &cst(&thm2)).unwrap()
    );
  }

  #[test]
  fn lazy_delta_chain_abbrev() {
    let prims = test_prims();
    let a = mk_addr(314);
    let b = mk_addr(315);
    let c = mk_addr(316);
    let mut env = empty_env();
    add_def(&mut env, &a, ty(), nat_lit(7), 0, ReducibilityHints::Abbrev);
    add_def(&mut env, &b, ty(), cst(&a), 0, ReducibilityHints::Abbrev);
    add_def(&mut env, &c, ty(), cst(&b), 0, ReducibilityHints::Abbrev);
    // Chain of abbrevs all reduce to 7
    assert!(is_def_eq(&env, &prims, &cst(&c), &nat_lit(7)).unwrap());
    assert!(is_def_eq(&env, &prims, &cst(&a), &cst(&c)).unwrap());
  }

  // ==========================================================================
  // Group D: K-Reduction
  // ==========================================================================

  #[test]
  fn k_reduction_direct_ctor() {
    let prims = test_prims();
    let (env, _true_ind, intro, rec) = build_my_true_env(empty_env());
    // rec (λ_. Nat) 42 intro → 42
    let rec_expr = app(
      app(
        app(cst(&rec), lam(cst(&_true_ind), ty())),
        nat_lit(42),
      ),
      cst(&intro),
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_expr).unwrap(), nat_lit(42));
  }

  #[test]
  fn k_reduction_axiom_major() {
    let prims = test_prims();
    let (mut env, true_ind, _intro, rec) = build_my_true_env(empty_env());
    let ax = mk_addr(317);
    add_axiom(&mut env, &ax, cst(&true_ind));
    // K-rec on axiom p : MyTrue still reduces (toCtorWhenK)
    let rec_expr = app(
      app(
        app(cst(&rec), lam(cst(&true_ind), ty())),
        nat_lit(99),
      ),
      cst(&ax),
    );
    assert_eq!(whnf_quote(&env, &prims, &rec_expr).unwrap(), nat_lit(99));
  }

  #[test]
  fn k_reduction_non_k_recursor_stays_stuck() {
    let prims = test_prims();
    let (mut env, nat_ind, _zero, _succ, rec) = build_my_nat_env(empty_env());
    let ax = mk_addr(318);
    add_axiom(&mut env, &ax, cst(&nat_ind));
    // MyNat.rec is NOT K (K=false). Applied to axiom of correct type stays stuck.
    let motive = lam(cst(&nat_ind), ty());
    let base = nat_lit(0);
    let step = lam(cst(&nat_ind), lam(ty(), bv(0)));
    let rec_expr = app(
      app(app(app(cst(&rec), motive), base), step),
      cst(&ax),
    );
    // rec on axiom (not a ctor) — iota fails, K not enabled → stuck
    assert_eq!(
      whnf_head_addr(&env, &prims, &rec_expr).unwrap(),
      Some(rec.clone())
    );
  }

  // ==========================================================================
  // Group E: Struct Eta (supplemental)
  // ==========================================================================

  #[test]
  fn struct_eta_not_recursive() {
    let prims = test_prims();
    // Build a recursive list-like type — struct eta should NOT fire
    let list_ind = mk_addr(319);
    let list_nil = mk_addr(320);
    let list_cons = mk_addr(321);
    let mut env = empty_env();
    add_inductive(
      &mut env,
      &list_ind,
      pi(ty(), ty()),
      vec![list_nil.clone(), list_cons.clone()],
      1, 0,
      true, // is_rec = true
      0,
      vec![list_ind.clone()],
    );
    add_ctor(
      &mut env, &list_nil, &list_ind,
      pi(ty(), app(cst(&list_ind), bv(0))),
      0, 1, 0, 0,
    );
    // cons : (α : Type) → α → List α → List α
    add_ctor(
      &mut env, &list_cons, &list_ind,
      pi(ty(), pi(bv(0), pi(app(cst(&list_ind), bv(1)), app(cst(&list_ind), bv(2))))),
      1, 1, 2, 0,
    );
    // Two axioms of list type should NOT be defeq (not unit-like, not proof irrel, not struct-eta)
    let ax1 = mk_addr(322);
    let ax2 = mk_addr(323);
    let list_nat = app(cst(&list_ind), ty());
    add_axiom(&mut env, &ax1, list_nat.clone());
    add_axiom(&mut env, &ax2, list_nat);
    assert!(!is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap());
  }

  // ==========================================================================
  // Group F: Unit-Like Types (supplemental)
  // ==========================================================================

  #[test]
  fn unit_like_prop_defeq() {
    let prims = test_prims();
    // Build a Prop type with 1 ctor, 0 fields (both unit-like and proof-irrel)
    let p_ind = mk_addr(324);
    let p_mk = mk_addr(325);
    let mut env = empty_env();
    add_inductive(
      &mut env, &p_ind, prop(),
      vec![p_mk.clone()],
      0, 0, false, 0,
      vec![p_ind.clone()],
    );
    add_ctor(&mut env, &p_mk, &p_ind, cst(&p_ind), 0, 0, 0, 0);
    let ax1 = mk_addr(326);
    let ax2 = mk_addr(327);
    add_axiom(&mut env, &ax1, cst(&p_ind));
    add_axiom(&mut env, &ax2, cst(&p_ind));
    // Both proof irrelevance and unit-like apply
    assert!(is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap());
  }

  #[test]
  fn unit_like_with_fields_not_defeq() {
    let prims = test_prims();
    let (mut env, pair_ind, _pair_ctor) = build_pair_env(empty_env());
    let ax1 = mk_addr(328);
    let ax2 = mk_addr(329);
    let pair_ty = app(app(cst(&pair_ind), ty()), ty());
    add_axiom(&mut env, &ax1, pair_ty.clone());
    add_axiom(&mut env, &ax2, pair_ty);
    // Pair has 2 fields → not unit-like → axioms not defeq
    assert!(!is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap());
  }

  // ==========================================================================
  // Group G: String Literal Expansion (supplemental)
  // ==========================================================================

  #[test]
  fn string_lit_multichar() {
    let prims = test_prims();
    let env = empty_env();
    let char_type = cst(&prims.char_type.as_ref().unwrap().addr);
    let mk_char = |n: u64| app(cst(&prims.char_mk.as_ref().unwrap().addr), nat_lit(n));
    let nil = app(
      cst_l(&prims.list_nil.as_ref().unwrap().addr, vec![KLevel::zero()]),
      char_type.clone(),
    );
    // Build "ab" as String.mk [Char.mk 97, Char.mk 98]
    let cons = |hd, tl| {
      app(
        app(
          app(
            cst_l(&prims.list_cons.as_ref().unwrap().addr, vec![KLevel::zero()]),
            char_type.clone(),
          ),
          hd,
        ),
        tl,
      )
    };
    let list_ab = cons(mk_char(97), cons(mk_char(98), nil));
    let str_ab = app(cst(&prims.string_mk.as_ref().unwrap().addr), list_ab);
    assert!(is_def_eq(&env, &prims, &str_lit("ab"), &str_ab).unwrap());
  }

  // ==========================================================================
  // Group H: Eta Expansion (supplemental)
  // ==========================================================================

  #[test]
  fn eta_axiom_fun() {
    let prims = test_prims();
    let f_addr = mk_addr(330);
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    add_axiom(&mut env, &f_addr, pi(cst(&nat_addr), cst(&nat_addr)));
    // f == λx. f x (eta)
    let eta_f = lam(cst(&nat_addr), app(cst(&f_addr), bv(0)));
    assert!(is_def_eq(&env, &prims, &cst(&f_addr), &eta_f).unwrap());
    assert!(is_def_eq(&env, &prims, &eta_f, &cst(&f_addr)).unwrap());
  }

  #[test]
  fn eta_nested_axiom() {
    let prims = test_prims();
    let f_addr = mk_addr(331);
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat = cst(&nat_addr);
    add_axiom(&mut env, &f_addr, pi(nat.clone(), pi(nat.clone(), nat.clone())));
    // f == λx.λy. f x y (double eta)
    let double_eta = lam(nat.clone(), lam(nat.clone(), app(app(cst(&f_addr), bv(1)), bv(0))));
    assert!(is_def_eq(&env, &prims, &cst(&f_addr), &double_eta).unwrap());
  }

  // ==========================================================================
  // Group I: Bidirectional Check
  // ==========================================================================

  /// Helper: run `check` on a term against an expected type.
  fn check_expr(
    env: &KEnv<Meta>,
    prims: &Primitives<Meta>,
    term: &KExpr<Meta>,
    expected_type: &KExpr<Meta>,
  ) -> Result<(), String> {
    let mut tc = TypeChecker::new(env, prims);
    let ty_val = tc.eval(expected_type, &std::rc::Rc::new(vec![])).map_err(|e| format!("{e}"))?;
    tc.check(term, &ty_val).map_err(|e| format!("{e}"))?;
    Ok(())
  }

  #[test]
  fn check_lam_against_pi() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat = cst(&nat_addr);
    // λ(x:Nat). x checked against (Nat → Nat) succeeds
    let id = lam(nat.clone(), bv(0));
    let pi_ty = pi(nat.clone(), nat.clone());
    assert!(check_expr(&env, &prims, &id, &pi_ty).is_ok());
  }

  #[test]
  fn check_domain_mismatch() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
    let bool_addr = prims.bool_type.as_ref().unwrap().addr.clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    add_axiom(&mut env, &bool_addr, ty());
    let nat = cst(&nat_addr);
    let bool_ty = cst(&bool_addr);
    // λ(x:Bool). x checked against (Nat → Nat) fails
    let lam_bool = lam(bool_ty, bv(0));
    let pi_nat = pi(nat.clone(), nat);
    assert!(check_expr(&env, &prims, &lam_bool, &pi_nat).is_err());
  }

  // ==========================================================================
  // Group J: Quotient Reduction (supplemental — already covered, add Quot.ind)
  // ==========================================================================

  #[test]
  fn quotient_ind_reduction() {
    let prims = test_prims();
    let quot_addr = mk_addr(150);
    let quot_mk_addr = mk_addr(151);
    let quot_lift_addr = mk_addr(152);
    let quot_ind_addr = mk_addr(153);
    let mut env = empty_env();

    let quot_type = pi(ty(), pi(pi(bv(0), pi(bv(1), prop())), bv(1)));
    add_quot(&mut env, &quot_addr, quot_type, QuotKind::Type, 1);

    let mk_type = pi(
      ty(),
      pi(
        pi(bv(0), pi(bv(1), prop())),
        pi(bv(1), app(app(cst_l(&quot_addr, vec![KLevel::param(0, anon())]), bv(2)), bv(1))),
      ),
    );
    add_quot(&mut env, &quot_mk_addr, mk_type, QuotKind::Ctor, 1);

    let lift_type = pi(ty(), pi(ty(), pi(ty(), pi(ty(), pi(ty(), pi(ty(), ty()))))));
    add_quot(&mut env, &quot_lift_addr, lift_type, QuotKind::Lift, 2);

    // Quot.ind : ... → Prop (simplified)
    let ind_type = pi(ty(), pi(ty(), pi(ty(), pi(ty(), pi(ty(), prop())))));
    add_quot(&mut env, &quot_ind_addr, ind_type, QuotKind::Ind, 1);

    let dummy_rel = lam(ty(), lam(ty(), prop()));
    let lvl1 = KLevel::succ(KLevel::zero());

    // Quot.mk applied
    let mk_expr = app(
      app(app(cst_l(&quot_mk_addr, vec![lvl1.clone()]), ty()), dummy_rel.clone()),
      nat_lit(10),
    );

    // h = λ(x:α). some_prop_value
    let h_expr = lam(ty(), prop());

    // Quot.ind α r motive h (Quot.mk α r 10) should reduce to h 10
    let ind_expr = app(
      app(
        app(
          app(
            app(cst_l(&quot_ind_addr, vec![lvl1]), ty()),
            dummy_rel,
          ),
          prop(), // motive (simplified)
        ),
        h_expr,
      ),
      mk_expr,
    );
    // Just check it reduces (doesn't error / doesn't stay stuck on quot_ind)
    let result = whnf_quote_qi(&env, &prims, &ind_expr, true);
    assert!(result.is_ok(), "Quot.ind reduction failed: {:?}", result.err());
  }

  // ==========================================================================
  // Group K: whnf Loop Ordering
  // ==========================================================================

  #[test]
  fn whnf_nat_prim_reduces_literals() {
    let prims = test_prims();
    let env = empty_env();
    // Nat.add 2 3 → 5 via primitive reduction
    let add_expr = app(
      app(cst(&prims.nat_add.as_ref().unwrap().addr), nat_lit(2)),
      nat_lit(3),
    );
    assert_eq!(whnf_quote(&env, &prims, &add_expr).unwrap(), nat_lit(5));
    // Nat.mul 4 5 → 20
    let mul_expr = app(
      app(cst(&prims.nat_mul.as_ref().unwrap().addr), nat_lit(4)),
      nat_lit(5),
    );
    assert_eq!(whnf_quote(&env, &prims, &mul_expr).unwrap(), nat_lit(20));
  }

  #[test]
  fn whnf_nat_prim_symbolic_stays_stuck() {
    let prims = test_prims();
    let x = mk_addr(332);
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    add_axiom(&mut env, &x, cst(&nat_addr));
    // Nat.add x 3 stays stuck (x is symbolic)
    let add_sym = app(
      app(cst(&prims.nat_add.as_ref().unwrap().addr), cst(&x)),
      nat_lit(3),
    );
    let result = whnf_quote(&env, &prims, &add_sym).unwrap();
    // Should NOT reduce to a literal — stays as application
    assert!(
      result != nat_lit(3),
      "Nat.add with symbolic arg should not reduce"
    );
  }

  // ==========================================================================
  // Group L: Level Equality (supplemental)
  // ==========================================================================

  #[test]
  fn level_max_commutative() {
    let prims = test_prims();
    let env = empty_env();
    let u = KLevel::param(0, anon());
    let v = KLevel::param(1, anon());
    // Sort (max u v) == Sort (max v u)
    let s1 = KExpr::sort(KLevel::max(u.clone(), v.clone()));
    let s2 = KExpr::sort(KLevel::max(v, u));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
  }

  #[test]
  fn level_imax_zero_rhs() {
    let prims = test_prims();
    let env = empty_env();
    let u = KLevel::param(0, anon());
    // imax(u, 0) should normalize to 0
    let imax_sort = KExpr::sort(KLevel::imax(u, KLevel::zero()));
    assert!(is_def_eq(&env, &prims, &imax_sort, &prop()).unwrap());
  }

  #[test]
  fn level_succ_not_zero() {
    let prims = test_prims();
    let env = empty_env();
    // Sort 1 != Sort 0
    assert!(!is_def_eq(&env, &prims, &ty(), &prop()).unwrap());
  }

  #[test]
  fn level_param_self_eq() {
    let prims = test_prims();
    let env = empty_env();
    let u = KLevel::param(0, anon());
    let s = KExpr::sort(u);
    assert!(is_def_eq(&env, &prims, &s, &s).unwrap());
  }

  // ==========================================================================
  // Group M: Projection Reduction (supplemental)
  // ==========================================================================

  #[test]
  fn proj_stuck_on_axiom() {
    let prims = test_prims();
    let (mut env, pair_ind, _pair_ctor) = build_pair_env(empty_env());
    let ax = mk_addr(333);
    let pair_ty = app(app(cst(&pair_ind), ty()), ty());
    add_axiom(&mut env, &ax, pair_ty);
    // proj 0 on axiom stays stuck (not a ctor)
    let proj = proj_e(&pair_ind, 0, cst(&ax));
    let result = whnf_quote(&env, &prims, &proj).unwrap();
    // Should still be a proj expression (not reduced)
    assert_eq!(result, proj_e(&pair_ind, 0, cst(&ax)));
  }

  #[test]
  fn proj_different_indices_not_defeq() {
    let prims = test_prims();
    let (mut env, pair_ind, _pair_ctor) = build_pair_env(empty_env());
    let ax = mk_addr(334);
    let pair_ty = app(app(cst(&pair_ind), ty()), ty());
    add_axiom(&mut env, &ax, pair_ty);
    // proj 0 ax != proj 1 ax
    let p0 = proj_e(&pair_ind, 0, cst(&ax));
    let p1 = proj_e(&pair_ind, 1, cst(&ax));
    assert!(!is_def_eq(&env, &prims, &p0, &p1).unwrap());
  }

  #[test]
  fn proj_nested_pair() {
    let prims = test_prims();
    let (env, pair_ind, pair_ctor) = build_pair_env(empty_env());
    // mk (mk 1 2) (mk 3 4)
    let inner1 = app(app(app(app(cst(&pair_ctor), ty()), ty()), nat_lit(1)), nat_lit(2));
    let inner2 = app(app(app(app(cst(&pair_ctor), ty()), ty()), nat_lit(3)), nat_lit(4));
    let pair_of_pair_ty = app(app(cst(&pair_ind), ty()), ty());
    let outer = app(
      app(
        app(app(cst(&pair_ctor), pair_of_pair_ty.clone()), pair_of_pair_ty),
        inner1,
      ),
      inner2,
    );
    // proj 0 outer == mk 1 2
    let p0 = proj_e(&pair_ind, 0, outer.clone());
    let expected = app(app(app(app(cst(&pair_ctor), ty()), ty()), nat_lit(1)), nat_lit(2));
    assert!(is_def_eq(&env, &prims, &p0, &expected).unwrap());
    // proj 0 (proj 0 outer) == 1
    let pp = proj_e(&pair_ind, 0, p0);
    assert!(is_def_eq(&env, &prims, &pp, &nat_lit(1)).unwrap());
  }

  // ==========================================================================
  // Group N: Opaque / Theorem separation
  // ==========================================================================

  #[test]
  fn opaque_self_eq() {
    let prims = test_prims();
    let o = mk_addr(335);
    let mut env = empty_env();
    add_opaque(&mut env, &o, ty(), nat_lit(5));
    // Opaque constant is defeq to itself (by pointer/const equality)
    assert!(is_def_eq(&env, &prims, &cst(&o), &cst(&o)).unwrap());
  }

  #[test]
  fn theorem_self_eq() {
    let prims = test_prims();
    let t = mk_addr(336);
    let mut env = empty_env();
    add_theorem(&mut env, &t, ty(), nat_lit(5));
    // Theorem constant is defeq to itself
    assert!(is_def_eq(&env, &prims, &cst(&t), &cst(&t)).unwrap());
    // Theorems are unfolded during defEq, so thm == 5
    assert!(is_def_eq(&env, &prims, &cst(&t), &nat_lit(5)).unwrap());
  }

  // ==========================================================================
  // Group O: Mixed reduction scenarios
  // ==========================================================================

  #[test]
  fn let_in_defeq() {
    let prims = test_prims();
    let env = empty_env();
    // (let x := 5 in x + x) == 10
    let add_xx = app(
      app(cst(&prims.nat_add.as_ref().unwrap().addr), bv(0)),
      bv(0),
    );
    let let_expr = let_e(ty(), nat_lit(5), add_xx);
    assert!(is_def_eq(&env, &prims, &let_expr, &nat_lit(10)).unwrap());
  }

  #[test]
  fn nested_let_defeq() {
    let prims = test_prims();
    let env = empty_env();
    // let x := 2 in let y := 3 in x + y == 5
    let inner = let_e(
      ty(),
      nat_lit(3),
      app(app(cst(&prims.nat_add.as_ref().unwrap().addr), bv(1)), bv(0)),
    );
    let outer = let_e(ty(), nat_lit(2), inner);
    assert!(is_def_eq(&env, &prims, &outer, &nat_lit(5)).unwrap());
  }

  #[test]
  fn beta_inside_defeq() {
    let prims = test_prims();
    let env = empty_env();
    // (λx.x) 5 == (λy.y) 5
    let a = app(lam(ty(), bv(0)), nat_lit(5));
    let b = app(lam(ty(), bv(0)), nat_lit(5));
    assert!(is_def_eq(&env, &prims, &a, &b).unwrap());
    // (λx.x) 5 == 5
    assert!(is_def_eq(&env, &prims, &a, &nat_lit(5)).unwrap());
  }

  #[test]
  fn sort_defeq_levels() {
    let prims = test_prims();
    let env = empty_env();
    // Sort 0 == Sort 0
    assert!(is_def_eq(&env, &prims, &prop(), &prop()).unwrap());
    // Sort 0 != Sort 1
    assert!(!is_def_eq(&env, &prims, &prop(), &ty()).unwrap());
    // Sort (succ (succ 0)) == Sort 2
    assert!(is_def_eq(&env, &prims, &srt(2), &srt(2)).unwrap());
    assert!(!is_def_eq(&env, &prims, &srt(2), &srt(3)).unwrap());
  }

  // ==========================================================================
  // Declaration-level checking, level arithmetic, and parity cleanup tests
  // ==========================================================================

  fn assert_typecheck_ok(env: &KEnv<Meta>, prims: &Primitives<Meta>, addr: &Address) {
    use crate::ix::kernel::check::typecheck_const;
    let result = typecheck_const(env, prims, &MetaId::from_addr(addr.clone()), false);
    assert!(result.is_ok(), "typecheck failed: {:?}", result.err());
  }

  fn assert_typecheck_err(env: &KEnv<Meta>, prims: &Primitives<Meta>, addr: &Address) {
    use crate::ix::kernel::check::typecheck_const;
    let result = typecheck_const(env, prims, &MetaId::from_addr(addr.clone()), false);
    assert!(result.is_err(), "expected typecheck error but got Ok");
  }

  // -- Phase 1B: Positive tests --

  #[test]
  fn check_mynat_ind_typechecks() {
    let prims = test_prims();
    let (env, nat_ind, zero, succ, rec) = build_my_nat_env(empty_env());
    assert_typecheck_ok(&env, &prims, &nat_ind);
    assert_typecheck_ok(&env, &prims, &zero);
    assert_typecheck_ok(&env, &prims, &succ);
    assert_typecheck_ok(&env, &prims, &rec);
  }

  #[test]
  fn check_mytrue_ind_typechecks() {
    let prims = test_prims();
    let (env, true_ind, intro, rec) = build_my_true_env(empty_env());
    assert_typecheck_ok(&env, &prims, &true_ind);
    assert_typecheck_ok(&env, &prims, &intro);
    assert_typecheck_ok(&env, &prims, &rec);
  }

  #[test]
  fn check_pair_ind_typechecks() {
    let prims = test_prims();
    let (env, pair_ind, pair_ctor) = build_pair_env(empty_env());
    assert_typecheck_ok(&env, &prims, &pair_ind);
    assert_typecheck_ok(&env, &prims, &pair_ctor);
  }

  #[test]
  fn check_axiom_typechecks() {
    let prims = test_prims();
    let mut env = empty_env();
    let ax_addr = mk_addr(500);
    add_axiom(&mut env, &ax_addr, ty());
    assert_typecheck_ok(&env, &prims, &ax_addr);
  }

  #[test]
  fn check_opaque_typechecks() {
    let prims = test_prims();
    let mut env = empty_env();
    let op_addr = mk_addr(501);
    add_opaque(&mut env, &op_addr, srt(2), ty());
    assert_typecheck_ok(&env, &prims, &op_addr);
  }

  #[test]
  fn check_theorem_typechecks() {
    let prims = test_prims();
    let (mut env, true_ind, intro, _rec) = build_my_true_env(empty_env());
    let thm_addr = mk_addr(502);
    add_theorem(&mut env, &thm_addr, cst(&true_ind), cst(&intro));
    assert_typecheck_ok(&env, &prims, &thm_addr);
  }

  #[test]
  fn check_definition_typechecks() {
    let prims = test_prims();
    let mut env = empty_env();
    let def_addr = mk_addr(503);
    add_def(&mut env, &def_addr, srt(2), ty(), 0, ReducibilityHints::Abbrev);
    assert_typecheck_ok(&env, &prims, &def_addr);
  }

  // -- Phase 1C: Constructor validation negatives --

  #[test]
  fn check_ctor_param_count_mismatch() {
    let prims = test_prims();
    let mut env = empty_env();
    let nat_ind = mk_addr(510);
    let zero_addr = mk_addr(511);
    // MyNat : Type
    add_inductive(
      &mut env, &nat_ind, ty(),
      vec![zero_addr.clone()], 0, 0, false, 0,
      vec![nat_ind.clone()],
    );
    // Constructor claims numParams=1 but inductive has numParams=0
    add_ctor(&mut env, &zero_addr, &nat_ind, cst(&nat_ind), 0, 1, 0, 0);
    assert_typecheck_err(&env, &prims, &nat_ind);
  }

  #[test]
  fn check_ctor_return_type_not_inductive() {
    let prims = test_prims();
    let mut env = empty_env();
    let my_ind = mk_addr(515);
    let my_ctor = mk_addr(516);
    let bogus = mk_addr(517);
    add_inductive(
      &mut env, &my_ind, ty(),
      vec![my_ctor.clone()], 0, 0, false, 0,
      vec![my_ind.clone()],
    );
    add_axiom(&mut env, &bogus, ty());
    // Constructor returns bogus instead of my_ind
    add_ctor(&mut env, &my_ctor, &my_ind, cst(&bogus), 0, 0, 0, 0);
    assert_typecheck_err(&env, &prims, &my_ind);
  }

  // -- Phase 1D: Strict positivity --

  #[test]
  fn positivity_ok_no_occurrence() {
    let prims = test_prims();
    let mut env = empty_env();
    let t_ind = mk_addr(520);
    let t_mk = mk_addr(521);
    let nat_addr = mk_addr(522);
    add_axiom(&mut env, &nat_addr, ty()); // Nat : Type
    add_inductive(
      &mut env, &t_ind, ty(),
      vec![t_mk.clone()], 0, 0, false, 0,
      vec![t_ind.clone()],
    );
    // mk : Nat → T
    add_ctor(&mut env, &t_mk, &t_ind, pi(cst(&nat_addr), cst(&t_ind)), 0, 0, 1, 0);
    assert_typecheck_ok(&env, &prims, &t_ind);
  }

  #[test]
  fn positivity_ok_direct() {
    let prims = test_prims();
    let mut env = empty_env();
    let t_ind = mk_addr(525);
    let t_mk = mk_addr(526);
    add_inductive(
      &mut env, &t_ind, ty(),
      vec![t_mk.clone()], 0, 0, true, 0,
      vec![t_ind.clone()],
    );
    // mk : T → T (direct positive)
    add_ctor(&mut env, &t_mk, &t_ind, pi(cst(&t_ind), cst(&t_ind)), 0, 0, 1, 0);
    assert_typecheck_ok(&env, &prims, &t_ind);
  }

  #[test]
  fn positivity_violation_negative() {
    let prims = test_prims();
    let mut env = empty_env();
    let t_ind = mk_addr(530);
    let t_mk = mk_addr(531);
    let nat_addr = mk_addr(532);
    add_axiom(&mut env, &nat_addr, ty());
    add_inductive(
      &mut env, &t_ind, ty(),
      vec![t_mk.clone()], 0, 0, true, 0,
      vec![t_ind.clone()],
    );
    // mk : (T → Nat) → T  -- T in negative position
    let field_type = pi(pi(cst(&t_ind), cst(&nat_addr)), cst(&t_ind));
    add_ctor(&mut env, &t_mk, &t_ind, field_type, 0, 0, 1, 0);
    assert_typecheck_err(&env, &prims, &t_ind);
  }

  #[test]
  fn positivity_ok_covariant() {
    let prims = test_prims();
    let mut env = empty_env();
    let t_ind = mk_addr(535);
    let t_mk = mk_addr(536);
    let nat_addr = mk_addr(537);
    add_axiom(&mut env, &nat_addr, ty());
    add_inductive(
      &mut env, &t_ind, ty(),
      vec![t_mk.clone()], 0, 0, true, 0,
      vec![t_ind.clone()],
    );
    // mk : (Nat → T) → T  -- T only in codomain (covariant)
    let field_type = pi(pi(cst(&nat_addr), cst(&t_ind)), cst(&t_ind));
    add_ctor(&mut env, &t_mk, &t_ind, field_type, 0, 0, 1, 0);
    assert_typecheck_ok(&env, &prims, &t_ind);
  }

  // -- Phase 1E: K-flag validation --

  #[test]
  fn k_flag_ok() {
    // Build a MyTrue-like inductive with properly annotated recursor RHS
    let prims = test_prims();
    let mut env = empty_env();
    let true_ind = mk_addr(538);
    let intro = mk_addr(539);
    let rec = mk_addr(5390);
    let true_const = cst(&true_ind);

    add_inductive(
      &mut env, &true_ind, prop(),
      vec![intro.clone()], 0, 0, false, 0,
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
    // RHS: λ (motive : MyTrue → Prop) (h : motive intro) => h
    let rule_rhs = lam(
      pi(true_const.clone(), prop()),
      lam(app(bv(0), cst(&intro)), bv(0)),
    );

    add_rec(
      &mut env, &rec, 0, rec_type,
      vec![true_ind.clone()], 0, 0, 1, 1,
      vec![KRecursorRule { ctor: MetaId::from_addr(intro.clone()), nfields: 0, rhs: rule_rhs }],
      true,
    );
    assert_typecheck_ok(&env, &prims, &rec);
  }

  #[test]
  fn k_flag_fail_not_prop() {
    let prims = test_prims();
    let mut env = empty_env();
    let t_ind = mk_addr(540);
    let t_mk = mk_addr(541);
    let t_rec = mk_addr(542);
    // T : Type (not Prop)
    add_inductive(
      &mut env, &t_ind, ty(),
      vec![t_mk.clone()], 0, 0, false, 0,
      vec![t_ind.clone()],
    );
    add_ctor(&mut env, &t_mk, &t_ind, cst(&t_ind), 0, 0, 0, 0);
    // Recursor with K=true on Type-level inductive
    let rec_type = pi(
      pi(cst(&t_ind), prop()),
      pi(
        app(bv(0), cst(&t_mk)),
        pi(cst(&t_ind), app(bv(2), bv(0))),
      ),
    );
    let rule_rhs = lam(pi(cst(&t_ind), prop()), lam(prop(), bv(0)));
    add_rec(
      &mut env, &t_rec, 0, rec_type,
      vec![t_ind.clone()], 0, 0, 1, 1,
      vec![KRecursorRule { ctor: MetaId::from_addr(t_mk.clone()), nfields: 0, rhs: rule_rhs }],
      true,
    );
    assert_typecheck_err(&env, &prims, &t_rec);
  }

  #[test]
  fn k_flag_fail_multiple_ctors() {
    let prims = test_prims();
    let mut env = empty_env();
    let p_ind = mk_addr(545);
    let p_mk1 = mk_addr(546);
    let p_mk2 = mk_addr(547);
    let p_rec = mk_addr(548);
    add_inductive(
      &mut env, &p_ind, prop(),
      vec![p_mk1.clone(), p_mk2.clone()], 0, 0, false, 0,
      vec![p_ind.clone()],
    );
    add_ctor(&mut env, &p_mk1, &p_ind, cst(&p_ind), 0, 0, 0, 0);
    add_ctor(&mut env, &p_mk2, &p_ind, cst(&p_ind), 1, 0, 0, 0);
    // Recursor with K=true but 2 ctors
    let rec_type = pi(
      pi(cst(&p_ind), prop()),
      pi(
        app(bv(0), cst(&p_mk1)),
        pi(
          app(bv(1), cst(&p_mk2)),
          pi(cst(&p_ind), app(bv(3), bv(0))),
        ),
      ),
    );
    let rhs1 = lam(pi(cst(&p_ind), prop()), lam(prop(), lam(prop(), bv(1))));
    let rhs2 = lam(pi(cst(&p_ind), prop()), lam(prop(), lam(prop(), bv(0))));
    add_rec(
      &mut env, &p_rec, 0, rec_type,
      vec![p_ind.clone()], 0, 0, 1, 2,
      vec![
        KRecursorRule { ctor: MetaId::from_addr(p_mk1.clone()), nfields: 0, rhs: rhs1 },
        KRecursorRule { ctor: MetaId::from_addr(p_mk2.clone()), nfields: 0, rhs: rhs2 },
      ],
      true,
    );
    assert_typecheck_err(&env, &prims, &p_rec);
  }

  #[test]
  fn k_flag_fail_has_fields() {
    let prims = test_prims();
    let mut env = empty_env();
    let p_ind = mk_addr(550);
    let p_mk = mk_addr(551);
    let p_rec = mk_addr(552);
    // P : Prop, mk : P → P (1 field)
    add_inductive(
      &mut env, &p_ind, prop(),
      vec![p_mk.clone()], 0, 0, true, 0,
      vec![p_ind.clone()],
    );
    add_ctor(&mut env, &p_mk, &p_ind, pi(cst(&p_ind), cst(&p_ind)), 0, 0, 1, 0);
    // Recursor with K=true but ctor has fields
    let rec_type = pi(
      pi(cst(&p_ind), prop()),
      pi(
        pi(cst(&p_ind), pi(app(bv(1), bv(0)), app(bv(2), app(cst(&p_mk), bv(1))))),
        pi(cst(&p_ind), app(bv(2), bv(0))),
      ),
    );
    let rule_rhs = lam(
      pi(cst(&p_ind), prop()),
      lam(
        pi(cst(&p_ind), pi(prop(), prop())),
        lam(cst(&p_ind), app(app(bv(1), bv(0)), app(bv(2), bv(0)))),
      ),
    );
    add_rec(
      &mut env, &p_rec, 0, rec_type,
      vec![p_ind.clone()], 0, 0, 1, 1,
      vec![KRecursorRule { ctor: MetaId::from_addr(p_mk.clone()), nfields: 1, rhs: rule_rhs }],
      true,
    );
    assert_typecheck_err(&env, &prims, &p_rec);
  }

  // -- Phase 1F: Recursor validation --

  #[test]
  fn rec_rules_count_mismatch() {
    let prims = test_prims();
    let (mut env, nat_ind, zero, _succ, _rec) = build_my_nat_env(empty_env());
    let bad_rec = mk_addr(560);
    // Recursor with 1 rule but MyNat has 2 ctors
    let rec_type = pi(
      pi(cst(&nat_ind), srt(1)),
      pi(
        app(bv(0), cst(&zero)),
        pi(cst(&nat_ind), app(bv(2), bv(0))),
      ),
    );
    let rule_rhs = lam(pi(cst(&nat_ind), srt(1)), lam(srt(1), bv(0)));
    add_rec(
      &mut env, &bad_rec, 0, rec_type,
      vec![nat_ind.clone()], 0, 0, 1, 1,
      vec![KRecursorRule { ctor: MetaId::from_addr(zero.clone()), nfields: 0, rhs: rule_rhs }],
      false,
    );
    assert_typecheck_err(&env, &prims, &bad_rec);
  }

  #[test]
  fn rec_rules_nfields_mismatch() {
    let prims = test_prims();
    let (mut env, nat_ind, zero, succ, _rec) = build_my_nat_env(empty_env());
    let bad_rec = mk_addr(565);
    let rec_type = pi(
      pi(cst(&nat_ind), srt(1)),
      pi(
        app(bv(0), cst(&zero)),
        pi(
          pi(
            cst(&nat_ind),
            pi(app(bv(2), bv(0)), app(bv(3), app(cst(&succ), bv(1)))),
          ),
          pi(cst(&nat_ind), app(bv(3), bv(0))),
        ),
      ),
    );
    let zero_rhs = lam(
      pi(cst(&nat_ind), srt(1)),
      lam(srt(1), lam(pi(cst(&nat_ind), pi(srt(1), srt(1))), bv(1))),
    );
    // succ rule claims nfields=0 instead of 1
    let succ_rhs = lam(
      pi(cst(&nat_ind), srt(1)),
      lam(srt(1), lam(pi(cst(&nat_ind), pi(srt(1), srt(1))), bv(0))),
    );
    add_rec(
      &mut env, &bad_rec, 0, rec_type,
      vec![nat_ind.clone()], 0, 0, 1, 2,
      vec![
        KRecursorRule { ctor: MetaId::from_addr(zero.clone()), nfields: 0, rhs: zero_rhs },
        KRecursorRule { ctor: MetaId::from_addr(succ.clone()), nfields: 0, rhs: succ_rhs },
      ],
      false,
    );
    assert_typecheck_err(&env, &prims, &bad_rec);
  }

  // -- Phase 1G: Elimination level --

  #[test]
  fn elim_level_type_large_ok() {
    // Build a MyNat-like inductive with properly annotated recursor RHS
    let prims = test_prims();
    let mut env = empty_env();
    let nat_ind = mk_addr(5600);
    let zero = mk_addr(5601);
    let succ = mk_addr(5602);
    let rec = mk_addr(5603);
    let nat_const = cst(&nat_ind);

    add_inductive(
      &mut env, &nat_ind, ty(),
      vec![zero.clone(), succ.clone()], 0, 0, false, 0,
      vec![nat_ind.clone()],
    );
    add_ctor(&mut env, &zero, &nat_ind, nat_const.clone(), 0, 0, 0, 0);
    add_ctor(&mut env, &succ, &nat_ind, pi(nat_const.clone(), nat_const.clone()), 1, 0, 1, 0);

    // rec : (motive : MyNat → Type) → motive zero → ((n:MyNat) → motive n → motive (succ n)) → (t:MyNat) → motive t
    let rec_type = pi(
      pi(nat_const.clone(), ty()),
      pi(
        app(bv(0), cst(&zero)),
        pi(
          pi(nat_const.clone(), pi(app(bv(2), bv(0)), app(bv(3), app(cst(&succ), bv(1))))),
          pi(nat_const.clone(), app(bv(3), bv(0))),
        ),
      ),
    );

    // Rule for zero: nfields=0
    // Expected type: (motive : MyNat → Type) → motive zero → ((n:MyNat) → motive n → motive (succ n)) → motive zero
    // RHS: λ (motive : MyNat → Type) (base : motive zero) (step : ...) => base
    let zero_rhs = lam(
      pi(nat_const.clone(), ty()),
      lam(
        app(bv(0), cst(&zero)),
        lam(
          pi(nat_const.clone(), pi(app(bv(2), bv(0)), app(bv(3), app(cst(&succ), bv(1))))),
          bv(1),
        ),
      ),
    );
    // Rule for succ: nfields=1
    // Expected type: (motive : MyNat → Type) → motive zero → ((n:MyNat) → motive n → motive (succ n)) → (n:MyNat) → motive (succ n)
    // RHS: λ (motive : ...) (base : ...) (step : ...) (n : MyNat) => step n (rec motive base step n)
    let succ_rhs = lam(
      pi(nat_const.clone(), ty()),
      lam(
        app(bv(0), cst(&zero)),
        lam(
          pi(nat_const.clone(), pi(app(bv(2), bv(0)), app(bv(3), app(cst(&succ), bv(1))))),
          lam(
            nat_const.clone(),
            app(
              app(bv(1), bv(0)),
              app(app(app(app(cst(&rec), bv(3)), bv(2)), bv(1)), bv(0)),
            ),
          ),
        ),
      ),
    );

    add_rec(
      &mut env, &rec, 0, rec_type,
      vec![nat_ind.clone()], 0, 0, 1, 2,
      vec![
        KRecursorRule { ctor: MetaId::from_addr(zero.clone()), nfields: 0, rhs: zero_rhs },
        KRecursorRule { ctor: MetaId::from_addr(succ.clone()), nfields: 1, rhs: succ_rhs },
      ],
      false,
    );
    assert_typecheck_ok(&env, &prims, &rec);
  }

  #[test]
  fn elim_level_prop_to_prop_ok() {
    let prims = test_prims();
    let mut env = empty_env();
    let p_ind = mk_addr(570);
    let p_mk1 = mk_addr(571);
    let p_mk2 = mk_addr(572);
    let p_rec = mk_addr(573);
    add_inductive(
      &mut env, &p_ind, prop(),
      vec![p_mk1.clone(), p_mk2.clone()], 0, 0, false, 0,
      vec![p_ind.clone()],
    );
    add_ctor(&mut env, &p_mk1, &p_ind, cst(&p_ind), 0, 0, 0, 0);
    add_ctor(&mut env, &p_mk2, &p_ind, cst(&p_ind), 1, 0, 0, 0);
    // Recursor to Prop only
    let rec_type = pi(
      pi(cst(&p_ind), prop()),
      pi(
        app(bv(0), cst(&p_mk1)),
        pi(
          app(bv(1), cst(&p_mk2)),
          pi(cst(&p_ind), app(bv(3), bv(0))),
        ),
      ),
    );
    // RHS with properly annotated lambda domains
    // rhs1: λ (motive : P → Prop) (h1 : motive mk1) (h2 : motive mk2) => h1
    let rhs1 = lam(
      pi(cst(&p_ind), prop()),
      lam(app(bv(0), cst(&p_mk1)),
        lam(app(bv(1), cst(&p_mk2)), bv(1))),
    );
    // rhs2: λ (motive : P → Prop) (h1 : motive mk1) (h2 : motive mk2) => h2
    let rhs2 = lam(
      pi(cst(&p_ind), prop()),
      lam(app(bv(0), cst(&p_mk1)),
        lam(app(bv(1), cst(&p_mk2)), bv(0))),
    );
    add_rec(
      &mut env, &p_rec, 0, rec_type,
      vec![p_ind.clone()], 0, 0, 1, 2,
      vec![
        KRecursorRule { ctor: MetaId::from_addr(p_mk1.clone()), nfields: 0, rhs: rhs1 },
        KRecursorRule { ctor: MetaId::from_addr(p_mk2.clone()), nfields: 0, rhs: rhs2 },
      ],
      false,
    );
    assert_typecheck_ok(&env, &prims, &p_rec);
  }

  #[test]
  fn elim_level_large_from_prop_multi_ctor_fail() {
    let prims = test_prims();
    let mut env = empty_env();
    let p_ind = mk_addr(575);
    let p_mk1 = mk_addr(576);
    let p_mk2 = mk_addr(577);
    let p_rec = mk_addr(578);
    add_inductive(
      &mut env, &p_ind, prop(),
      vec![p_mk1.clone(), p_mk2.clone()], 0, 0, false, 0,
      vec![p_ind.clone()],
    );
    add_ctor(&mut env, &p_mk1, &p_ind, cst(&p_ind), 0, 0, 0, 0);
    add_ctor(&mut env, &p_mk2, &p_ind, cst(&p_ind), 1, 0, 0, 0);
    // Recursor claims large elimination (motive : P → Type)
    let rec_type = pi(
      pi(cst(&p_ind), srt(1)),
      pi(
        app(bv(0), cst(&p_mk1)),
        pi(
          app(bv(1), cst(&p_mk2)),
          pi(cst(&p_ind), app(bv(3), bv(0))),
        ),
      ),
    );
    let rhs1 = lam(pi(cst(&p_ind), srt(1)), lam(srt(1), lam(srt(1), bv(1))));
    let rhs2 = lam(pi(cst(&p_ind), srt(1)), lam(srt(1), lam(srt(1), bv(0))));
    add_rec(
      &mut env, &p_rec, 0, rec_type,
      vec![p_ind.clone()], 0, 0, 1, 2,
      vec![
        KRecursorRule { ctor: MetaId::from_addr(p_mk1.clone()), nfields: 0, rhs: rhs1 },
        KRecursorRule { ctor: MetaId::from_addr(p_mk2.clone()), nfields: 0, rhs: rhs2 },
      ],
      false,
    );
    assert_typecheck_err(&env, &prims, &p_rec);
  }

  // -- Phase 1H: Theorem validation --

  #[test]
  fn check_theorem_not_in_prop() {
    let prims = test_prims();
    let mut env = empty_env();
    let thm_addr = mk_addr(580);
    add_theorem(&mut env, &thm_addr, ty(), srt(0));
    assert_typecheck_err(&env, &prims, &thm_addr);
  }

  #[test]
  fn check_theorem_value_mismatch() {
    let prims = test_prims();
    let (mut env, true_ind, _intro, _rec) = build_my_true_env(empty_env());
    let thm_addr = mk_addr(582);
    // theorem : MyTrue := Prop (wrong value)
    add_theorem(&mut env, &thm_addr, cst(&true_ind), prop());
    assert_typecheck_err(&env, &prims, &thm_addr);
  }

  // -- Phase 2: Level arithmetic --

  #[test]
  fn level_arithmetic_extended() {
    let prims = test_prims();
    let env = empty_env();
    let u = KLevel::param(0, anon());
    let v = KLevel::param(1, anon());
    // max(u, 0) = u
    let s1 = KExpr::sort(KLevel::max(u.clone(), KLevel::zero()));
    let s2 = KExpr::sort(u.clone());
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // max(0, u) = u
    let s1 = KExpr::sort(KLevel::max(KLevel::zero(), u.clone()));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // max(succ u, succ v) = succ(max(u,v))
    let s1 = KExpr::sort(KLevel::max(KLevel::succ(u.clone()), KLevel::succ(v.clone())));
    let s2 = KExpr::sort(KLevel::succ(KLevel::max(u.clone(), v.clone())));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // max(u, u) = u
    let s1 = KExpr::sort(KLevel::max(u.clone(), u.clone()));
    let s2 = KExpr::sort(u.clone());
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // imax(u, succ v) = max(u, succ v)
    let s1 = KExpr::sort(KLevel::imax(u.clone(), KLevel::succ(v.clone())));
    let s2 = KExpr::sort(KLevel::max(u.clone(), KLevel::succ(v.clone())));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // imax(u, 0) = 0
    let s1 = KExpr::sort(KLevel::imax(u.clone(), KLevel::zero()));
    let s2 = KExpr::sort(KLevel::zero());
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // param 0 != param 1
    let s1 = KExpr::sort(u.clone());
    let s2 = KExpr::sort(v.clone());
    assert!(!is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // succ(succ 0) == succ(succ 0)
    assert!(is_def_eq(&env, &prims, &srt(2), &srt(2)).unwrap());
  }

  // -- Phase 3: Parity cleanup --

  #[test]
  fn nat_pow_overflow() {
    let prims = test_prims();
    let env = empty_env();
    // 2^63 + 2^63 = 2^64
    let two = nat_lit(2);
    let pow63 = app(app(cst(&prims.nat_pow.as_ref().unwrap().addr), two.clone()), nat_lit(63));
    let pow64 = app(app(cst(&prims.nat_pow.as_ref().unwrap().addr), two.clone()), nat_lit(64));
    let sum = app(app(cst(&prims.nat_add.as_ref().unwrap().addr), pow63.clone()), pow63.clone());
    assert!(is_def_eq(&env, &prims, &sum, &pow64).unwrap());
  }

  #[test]
  fn unit_like_with_fields_not_defeq_parity() {
    let prims = test_prims();
    let (mut env, pair_ind, _pair_ctor) = build_pair_env(empty_env());
    let ax1 = mk_addr(595);
    let ax2 = mk_addr(596);
    let pair_nat_nat = app(app(cst(&pair_ind), ty()), ty());
    add_axiom(&mut env, &ax1, pair_nat_nat.clone());
    add_axiom(&mut env, &ax2, pair_nat_nat);
    // Pair has 2 fields, so NOT unit-like
    assert!(!is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap());
  }

  // ==========================================================================
  // Phase 4: Lean parity — remaining gaps
  // ==========================================================================

  #[test]
  fn nat_pow_boundary_guard() {
    let prims = test_prims();
    let env = empty_env();
    // Nat.pow 2 16777216 should compute (boundary, exponent = 2^24)
    let pow_boundary = app(
      app(cst(&prims.nat_pow.as_ref().unwrap().addr), nat_lit(2)),
      nat_lit(16777216),
    );
    // Should reduce to a nat lit (not stay stuck)
    let result = whnf_quote(&env, &prims, &pow_boundary).unwrap();
    match result.0.as_ref() {
      KExprData::Lit(Literal::NatVal(_)) => {} // ok
      other => panic!("expected NatLit, got {other:?}"),
    }
    // Nat.pow 2 16777217 should stay stuck (exponent > 2^24)
    let pow_over = app(
      app(cst(&prims.nat_pow.as_ref().unwrap().addr), nat_lit(2)),
      nat_lit(16777217),
    );
    assert_eq!(
      whnf_head_addr(&env, &prims, &pow_over).unwrap(),
      Some(prims.nat_pow.as_ref().unwrap().addr.clone())
    );
  }

  #[test]
  fn string_lit_3char() {
    let prims = test_prims();
    let env = empty_env();
    let char_type = cst(&prims.char_type.as_ref().unwrap().addr);
    let mk_char = |n: u64| app(cst(&prims.char_mk.as_ref().unwrap().addr), nat_lit(n));
    let nil = app(
      cst_l(&prims.list_nil.as_ref().unwrap().addr, vec![KLevel::zero()]),
      char_type.clone(),
    );
    let cons = |hd, tl| {
      app(
        app(
          app(
            cst_l(&prims.list_cons.as_ref().unwrap().addr, vec![KLevel::zero()]),
            char_type.clone(),
          ),
          hd,
        ),
        tl,
      )
    };
    // Build "abc" as String.mk [Char.mk 97, Char.mk 98, Char.mk 99]
    let list_abc = cons(mk_char(97), cons(mk_char(98), cons(mk_char(99), nil)));
    let str_abc = app(cst(&prims.string_mk.as_ref().unwrap().addr), list_abc);
    assert!(is_def_eq(&env, &prims, &str_lit("abc"), &str_abc).unwrap());
  }

  #[test]
  fn struct_eta_cross_type_negative() {
    let prims = test_prims();
    let (mut env, _pair_ind, pair_ctor) = build_pair_env(empty_env());
    // Build a second struct Pair2 with same shape but different address
    let pair2_ind = mk_addr(600);
    let pair2_ctor = mk_addr(601);
    add_inductive(
      &mut env, &pair2_ind,
      pi(ty(), pi(ty(), ty())),
      vec![pair2_ctor.clone()],
      2, 0, false, 0,
      vec![pair2_ind.clone()],
    );
    let ctor2_type = pi(
      ty(),
      pi(ty(), pi(bv(1), pi(bv(1), app(app(cst(&pair2_ind), bv(3)), bv(2))))),
    );
    add_ctor(&mut env, &pair2_ctor, &pair2_ind, ctor2_type, 0, 2, 2, 0);
    // mk1 Nat Nat 3 7 vs mk2 Nat Nat 3 7 — different struct types
    let mk1 = app(app(app(app(cst(&pair_ctor), ty()), ty()), nat_lit(3)), nat_lit(7));
    let mk2 = app(app(app(app(cst(&pair2_ctor), ty()), ty()), nat_lit(3)), nat_lit(7));
    assert!(!is_def_eq(&env, &prims, &mk1, &mk2).unwrap());
  }

  #[test]
  fn unit_like_multi_ctor_not_unit() {
    let prims = test_prims();
    let mut env = empty_env();
    // Bool-like type with 2 ctors, 0 fields each — NOT unit-like
    let bool_ind = mk_addr(602);
    let b1 = mk_addr(603);
    let b2 = mk_addr(604);
    add_inductive(
      &mut env, &bool_ind, ty(),
      vec![b1.clone(), b2.clone()],
      0, 0, false, 0,
      vec![bool_ind.clone()],
    );
    add_ctor(&mut env, &b1, &bool_ind, cst(&bool_ind), 0, 0, 0, 0);
    add_ctor(&mut env, &b2, &bool_ind, cst(&bool_ind), 1, 0, 0, 0);
    let ax1 = mk_addr(605);
    let ax2 = mk_addr(606);
    add_axiom(&mut env, &ax1, cst(&bool_ind));
    add_axiom(&mut env, &ax2, cst(&bool_ind));
    assert!(!is_def_eq(&env, &prims, &cst(&ax1), &cst(&ax2)).unwrap());
  }

  #[test]
  fn deep_spine_axiom_heads() {
    let prims = test_prims();
    let mut env = empty_env();
    // Two different axioms with same function type, applied to same arg
    let ax1 = mk_addr(607);
    let ax2 = mk_addr(608);
    add_axiom(&mut env, &ax1, pi(ty(), ty()));
    add_axiom(&mut env, &ax2, pi(ty(), ty()));
    assert!(!is_def_eq(&env, &prims, &app(cst(&ax1), nat_lit(1)), &app(cst(&ax2), nat_lit(1))).unwrap());
  }

  #[test]
  fn infer_extended() {
    let prims = test_prims();
    let nat_addr = prims.nat.as_ref().unwrap().addr.clone();
    let mut env = empty_env();
    add_axiom(&mut env, &nat_addr, ty());
    let nat_const = cst(&nat_addr);
    // Nested lambda: λ(x:Nat). λ(y:Nat). x : Nat → Nat → Nat
    let nested_lam = lam(nat_const.clone(), lam(nat_const.clone(), bv(1)));
    let inferred = infer_quote(&env, &prims, &nested_lam).unwrap();
    assert_eq!(inferred, pi(nat_const.clone(), pi(nat_const.clone(), nat_const.clone())));
    // Prop → Type = Sort 2 (imax 0 1 = 1, result is Sort(imax(Sort1_level, 1)) = Sort 2)
    let inferred = infer_quote(&env, &prims, &pi(prop(), ty())).unwrap();
    assert_eq!(inferred, srt(2));
    // Type → Prop = Sort 2
    let inferred = infer_quote(&env, &prims, &pi(ty(), prop())).unwrap();
    assert_eq!(inferred, srt(2));
    // Nested let inference: let x : Nat := 5 in let y : Nat := x in y : Nat
    let let_nested = let_e(nat_const.clone(), nat_lit(5), let_e(nat_const.clone(), bv(0), bv(0)));
    let inferred = infer_quote(&env, &prims, &let_nested).unwrap();
    assert_eq!(inferred, nat_const.clone());
    // Inference of applied def
    let id_addr = mk_addr(609);
    add_def(&mut env, &id_addr, pi(nat_const.clone(), nat_const.clone()),
      lam(nat_const.clone(), bv(0)), 0, ReducibilityHints::Abbrev);
    let inferred = infer_quote(&env, &prims, &app(cst(&id_addr), nat_lit(5))).unwrap();
    assert_eq!(inferred, nat_const);
  }

  #[test]
  fn opaque_applied_stuck() {
    let prims = test_prims();
    let opaq_fn = mk_addr(610);
    let mut env = empty_env();
    add_opaque(&mut env, &opaq_fn, pi(ty(), ty()), lam(ty(), bv(0)));
    // Opaque function applied stays stuck (head = opaque addr)
    assert_eq!(
      whnf_head_addr(&env, &prims, &app(cst(&opaq_fn), nat_lit(5))).unwrap(),
      Some(opaq_fn)
    );
  }

  #[test]
  fn iota_trailing_args() {
    let prims = test_prims();
    let (env, nat_ind, zero, _succ, rec) = build_my_nat_env(empty_env());
    let nat_const = cst(&nat_ind);
    // Function-valued motive: MyNat → (Nat → Nat)
    let fn_motive = lam(nat_const.clone(), pi(ty(), ty()));
    // base: λx. Nat.add x (partial app)
    let fn_base = lam(ty(), app(cst(&prims.nat_add.as_ref().unwrap().addr), bv(0)));
    // step: λ_ acc. acc
    let fn_step = lam(nat_const, lam(pi(ty(), ty()), bv(0)));
    // rec fnMotive fnBase fnStep zero 10 — extra arg applied after major
    let rec_fn_zero = app(
      app(
        app(app(app(cst(&rec), fn_motive), fn_base), fn_step),
        cst(&zero),
      ),
      nat_lit(10),
    );
    // Should reduce (iota fires on zero, then extra arg is applied)
    assert!(whnf_quote(&env, &prims, &rec_fn_zero).is_ok());
  }

  #[test]
  fn level_arithmetic_associativity() {
    let prims = test_prims();
    let env = empty_env();
    let u = KLevel::param(0, anon());
    let v = KLevel::param(1, anon());
    let w = KLevel::param(2, anon());
    // max(max(u, v), w) == max(u, max(v, w)) (associativity)
    let s1 = KExpr::sort(KLevel::max(KLevel::max(u.clone(), v.clone()), w.clone()));
    let s2 = KExpr::sort(KLevel::max(u.clone(), KLevel::max(v.clone(), w.clone())));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // imax(succ u, succ v) == max(succ u, succ v)
    let s1 = KExpr::sort(KLevel::imax(KLevel::succ(u.clone()), KLevel::succ(v.clone())));
    let s2 = KExpr::sort(KLevel::max(KLevel::succ(u.clone()), KLevel::succ(v.clone())));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
    // succ(max(u, v)) == max(succ u, succ v)
    let s1 = KExpr::sort(KLevel::succ(KLevel::max(u.clone(), v.clone())));
    let s2 = KExpr::sort(KLevel::max(KLevel::succ(u), KLevel::succ(v)));
    assert!(is_def_eq(&env, &prims, &s1, &s2).unwrap());
  }
}
