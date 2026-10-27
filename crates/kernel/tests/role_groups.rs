//! Group admission of bound roles, on the compiler's own basis blocks.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, Name};
use ix_kernel::artifact_checker::ArtifactChecker;
use ix_kernel::mode::Anon;
use ix_kernel::role_admission::ArtifactSource;
use ixon::constant::{Axiom, Constant, ConstantInfo, DefKind, Definition};
use ixon::contract::{BinderContract, ValueContract};
use ixon::env::{Env, RoleBinding};
use ixon::expr::Expr;
use ixon::role_table::{Evidence, Role, RoleTable};
use ixon::univ::Univ;

const BASIS: &[u8] = include_bytes!("fixtures/role_admission/basis.ixe");

fn loaded() -> Env {
  let mut input = BASIS;
  let env = Env::get(&mut input).unwrap();
  assert!(input.is_empty());
  env
}

fn name(dotted: &str) -> Name {
  dotted
    .split('.')
    .fold(Name::anon(), |prefix, part| Name::str(prefix, part.into()))
}

fn address_of(env: &Env, dotted: &str) -> Address {
  env
    .lookup_name(&name(dotted))
    .unwrap_or_else(|| panic!("{dotted} missing"))
    .addr
}

fn bind(env: &mut Env, bound: Vec<(Role, Address)>) {
  bind_with_evidence(env, bound, vec![]);
}

fn bind_with_evidence(
  env: &mut Env,
  mut bound: Vec<(Role, Address)>,
  mut evidence: Vec<(Role, Vec<Evidence>)>,
) {
  bound.sort_by_key(|(role, _)| role.index());
  evidence.sort_by_key(|(role, _)| role.index());
  let raw = RoleTable { version: 2, bound, evidence }.to_bytes().unwrap();
  env.role_binding =
    Some(RoleBinding { address: Address::hash(&raw), bytes: raw.into() });
}

fn nat_roles(env: &Env) -> Vec<(Role, Address)> {
  vec![
    (Role::Nat, address_of(env, "Nat")),
    (Role::NatZero, address_of(env, "Nat.zero")),
    (Role::NatSucc, address_of(env, "Nat.succ")),
    (Role::NatRec, address_of(env, "Nat.rec")),
  ]
}

/// A definition `n : Nat := 5`, stored in `env`.
fn literal_definition(env: &Env, nat: &Address) -> Address {
  let literal = env.store_blob(vec![5]);
  let mut constant = Constant::new(ConstantInfo::Defn(Definition {
    kind: DefKind::Definition,
    safety: DefinitionSafety::Safe,
    lvls: 0,
    typ: Arc::new(Expr::Ref(0, vec![])),
    value: Arc::new(Expr::Nat(1)),
  }));
  constant.refs = vec![nat.clone(), literal];
  let address = constant.commit().0;
  env.store_const(address.clone(), constant);
  address
}

#[test]
fn the_compiled_nat_block_is_admitted_with_its_literals() {
  let mut env = loaded();
  let roles = nat_roles(&env);
  let nat = roles[0].1.clone();
  let definition = literal_definition(&env, &nat);
  bind(&mut env, roles.clone());
  let source = ArtifactSource::snapshot(&env).unwrap();
  let admission = source.admission();
  assert!(admission.refused().is_empty(), "{:?}", admission.refused());
  for (role, address) in &roles {
    assert_eq!(admission.address(*role), Some(address), "{role:?}");
    assert!(source.capability(*role).is_some());
  }
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
  checker.check_const(&nat).unwrap();
  checker.check_const(&definition).unwrap();
}

#[test]
fn unbound_or_refused_nat_leaves_literals_refused() {
  // Without any Nat role, and with Nat roles that fail their
  // specification, a literal's type is not available.
  for misbind in [false, true] {
    let mut env = loaded();
    let nat = address_of(&env, "Nat");
    let definition = literal_definition(&env, &nat);
    if misbind {
      // `Bool` has `Nat`'s shape of unit (two constructors and a
      // recursor), but not its declarations.
      let as_nat = vec![
        (Role::Nat, address_of(&env, "Bool")),
        (Role::NatZero, address_of(&env, "Bool.false")),
        (Role::NatSucc, address_of(&env, "Bool.true")),
        (Role::NatRec, address_of(&env, "Bool.rec")),
      ];
      bind(&mut env, as_nat);
    } else {
      bind(&mut env, vec![]);
    }
    let source = ArtifactSource::snapshot(&env).unwrap();
    assert!(!source.is_admitted(Role::Nat));
    assert!(source.capability(Role::Nat).is_none());
    if misbind {
      let refused = source.admission().refused();
      assert_eq!(refused.len(), 1, "{refused:?}");
      assert_eq!(refused[0].0, Role::Nat);
      assert!(refused[0].1.contains("differs from the specification"));
    }
    let error = ArtifactChecker::<Anon>::from_source(Ok(source))
      .check_const(&definition)
      .unwrap_err();
    assert!(format!("{error}").contains("Nat support is not admitted"));
  }
}

#[test]
fn swapped_constructor_roles_are_refused() {
  let mut env = loaded();
  let mut roles = nat_roles(&env);
  let zero = roles[1].1.clone();
  roles[1].1 = roles[2].1.clone();
  roles[2].1 = zero;
  bind(&mut env, roles);
  let source = ArtifactSource::snapshot(&env).unwrap();
  assert!(!source.is_admitted(Role::Nat));
  let refused = source.admission().refused();
  assert!(refused[0].1.contains("not at its position"), "{refused:?}");
}

fn basis_roles(env: &Env) -> Vec<(Role, Address)> {
  let mut roles = nat_roles(env);
  for (role, name) in [
    (Role::Eq, "Eq"),
    (Role::EqRefl, "Eq.refl"),
    (Role::EqRec, "Eq.rec"),
    (Role::PUnit, "PUnit"),
    (Role::PUnitUnit, "PUnit.unit"),
    (Role::PUnitRec, "PUnit.rec"),
    (Role::Empty, "Empty"),
    (Role::EmptyRec, "Empty.rec"),
    (Role::False, "False"),
    (Role::FalseRec, "False.rec"),
    (Role::Quot, "Quot"),
    (Role::QuotMk, "Quot.mk"),
    (Role::QuotLift, "Quot.lift"),
    (Role::QuotInd, "Quot.ind"),
    (Role::QuotSound, "Quot.sound"),
  ] {
    roles.push((role, address_of(env, name)));
  }
  roles
}

#[test]
fn the_compiled_basis_blocks_are_admitted() {
  let mut env = loaded();
  let roles = basis_roles(&env);
  bind(&mut env, roles.clone());
  let source = ArtifactSource::snapshot(&env).unwrap();
  let admission = source.admission();
  assert!(admission.refused().is_empty(), "{:?}", admission.refused());
  assert_eq!(admission.admitted_count(), roles.len());
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
  for (role, address) in &roles {
    checker.check_const(address).unwrap_or_else(|e| panic!("{role:?}: {e}"));
  }
}

#[test]
fn a_misbound_block_is_refused_with_the_groups_that_need_it() {
  let mut env = loaded();
  let mut roles = basis_roles(&env);
  // Bind `Eq`'s roles to `PUnit`'s block and `PUnit`'s to `Eq`'s.
  let position = |roles: &[(Role, Address)], role| {
    roles.iter().position(|(r, _)| *r == role).unwrap()
  };
  for (a, b) in [
    (Role::Eq, Role::PUnit),
    (Role::EqRefl, Role::PUnitUnit),
    (Role::EqRec, Role::PUnitRec),
  ] {
    let (i, j) = (position(&roles, a), position(&roles, b));
    let address = roles[i].1.clone();
    roles[i].1 = roles[j].1.clone();
    roles[j].1 = address;
  }
  bind(&mut env, roles);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let refused: Vec<Role> =
    source.admission().refused().iter().map(|(role, _)| *role).collect();
  assert_eq!(refused, [Role::Eq, Role::PUnit, Role::Quot]);
  assert!(source.is_admitted(Role::Nat) && source.is_admitted(Role::False));
  let reason = &source.admission().refused()[2].1;
  assert!(reason.contains("needs the unadmitted"), "{reason}");
}

#[test]
fn quotient_records_need_the_quot_group() {
  let mut env = loaded();
  let quot = address_of(&env, "Quot");
  let nat = address_of(&env, "Nat");
  // `def : (Nat → Nat → Prop) → Type := @Quot.{1} Nat`.
  let type1 = Arc::new(Univ::Succ(Arc::new(Univ::Zero)));
  let relation =
    pi(reference(1, vec![]), pi(reference(1, vec![]), arc(Expr::Sort(1))));
  let definition = store(
    &env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: pi(relation, arc(Expr::Sort(0))),
      value: app(reference(0, vec![0]), reference(1, vec![])),
    }),
    vec![quot, nat],
    vec![type1, Arc::new(Univ::Zero)],
  );
  let roles = nat_roles(&env);
  bind(&mut env, roles);
  let error = ArtifactChecker::<Anon>::from_source(Ok(
    ArtifactSource::snapshot(&env).unwrap(),
  ))
  .check_const(&definition)
  .unwrap_err();
  assert!(
    format!("{error}").contains("not an admitted quotient primitive"),
    "{error}"
  );
}

// Anchors are specified by type alone, so any safe declarations of the
// specified types serve.

fn arc(expr: Expr) -> Arc<Expr> {
  Arc::new(expr)
}
fn pi(domain: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
  arc(Expr::All(
    BinderContract::default(),
    ValueContract::shared(),
    domain,
    body,
  ))
}
fn app(f: Arc<Expr>, a: Arc<Expr>) -> Arc<Expr> {
  arc(Expr::App(f, a))
}
fn reference(index: u64, levels: Vec<u64>) -> Arc<Expr> {
  arc(Expr::Ref(index, levels))
}

fn store(
  env: &Env,
  info: ConstantInfo,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Address {
  let mut constant = Constant::new(info);
  constant.refs = refs;
  constant.univs = univs;
  let address = constant.commit().0;
  env.store_const(address.clone(), constant);
  address
}

fn axiom(
  env: &Env,
  lvls: u64,
  typ: Arc<Expr>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Address {
  store(
    env,
    ConstantInfo::Axio(Axiom { is_unsafe: false, lvls, typ }),
    refs,
    univs,
  )
}

fn lambda(domain: Arc<Expr>, body: Arc<Expr>) -> Arc<Expr> {
  arc(Expr::Lam(BinderContract::default(), domain, body))
}

fn definition(
  env: &Env,
  lvls: u64,
  typ: Arc<Expr>,
  value: Arc<Expr>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Address {
  store(
    env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls,
      typ,
      value,
    }),
    refs,
    univs,
  )
}

/// The literal-support anchors as definitions of the specified types, over
/// `Nat` and `PUnit`: `Char := Nat`, `String := PUnit`, `List α := PUnit`.
/// With `of_list_is_wrong`, `String.ofList : List Char → List Char`.
fn literal_anchors(env: &Env, of_list_is_wrong: bool) -> Vec<(Role, Address)> {
  let nat = address_of(env, "Nat");
  let punit = address_of(env, "PUnit");
  let unit = address_of(env, "PUnit.unit");
  let zero = Arc::new(Univ::Zero);
  let one = Arc::new(Univ::Succ(zero.clone()));
  let succ_param = Arc::new(Univ::Succ(Arc::new(Univ::Var(0))));
  let char_t = definition(
    env,
    0,
    arc(Expr::Sort(0)),
    reference(0, vec![]),
    vec![nat.clone()],
    vec![one.clone()],
  );
  let string = definition(
    env,
    0,
    arc(Expr::Sort(0)),
    reference(0, vec![0]),
    vec![punit.clone()],
    vec![one.clone()],
  );
  // `Type u → Type u`; universe 0 is `u + 1`, universe 1 is `u`.
  let list = definition(
    env,
    1,
    pi(arc(Expr::Sort(0)), arc(Expr::Sort(0))),
    lambda(arc(Expr::Sort(0)), reference(0, vec![0])),
    vec![punit],
    vec![succ_param.clone()],
  );
  let list_u = |arg| app(reference(0, vec![1]), arg);
  let univs = vec![succ_param, Arc::new(Univ::Var(0))];
  let nil = definition(
    env,
    1,
    pi(arc(Expr::Sort(0)), list_u(arc(Expr::Var(0)))),
    lambda(arc(Expr::Sort(0)), reference(1, vec![0])),
    vec![list.clone(), unit.clone()],
    univs.clone(),
  );
  let cons = definition(
    env,
    1,
    pi(
      arc(Expr::Sort(0)),
      pi(
        arc(Expr::Var(0)),
        pi(list_u(arc(Expr::Var(1))), list_u(arc(Expr::Var(2)))),
      ),
    ),
    lambda(
      arc(Expr::Sort(0)),
      lambda(
        arc(Expr::Var(0)),
        lambda(list_u(arc(Expr::Var(1))), reference(1, vec![0])),
      ),
    ),
    vec![list.clone(), unit.clone()],
    univs,
  );
  let of_nat = definition(
    env,
    0,
    pi(reference(0, vec![]), reference(1, vec![])),
    lambda(reference(0, vec![]), arc(Expr::Var(0))),
    vec![nat, char_t.clone()],
    vec![],
  );
  // `List.{0} Char → String := fun _ => PUnit.unit.{1}`.
  let list_char = || app(reference(0, vec![0]), reference(1, vec![]));
  let of_list = if of_list_is_wrong {
    definition(
      env,
      0,
      pi(list_char(), list_char()),
      lambda(list_char(), arc(Expr::Var(0))),
      vec![list.clone(), char_t.clone()],
      vec![zero],
    )
  } else {
    definition(
      env,
      0,
      pi(list_char(), reference(2, vec![])),
      lambda(list_char(), reference(3, vec![1])),
      vec![list.clone(), char_t.clone(), string.clone(), unit],
      vec![zero, one],
    )
  };
  vec![
    (Role::Char, char_t),
    (Role::String, string),
    (Role::List, list),
    (Role::ListNil, nil),
    (Role::ListCons, cons),
    (Role::CharOfNat, of_nat),
    (Role::StringOfList, of_list),
  ]
}

/// `theorem : @Eq.{1} String "a" (String.ofList [Char.ofNat 97]) :=
/// @Eq.refl.{1} String "a"`.
fn string_literal_theorem(env: &Env, anchors: &[(Role, Address)]) -> Address {
  let anchor = |role| {
    anchors.iter().find(|(r, _)| *r == role).map(|(_, a)| a.clone()).unwrap()
  };
  let text = env.store_blob(b"a".to_vec());
  let code = env.store_blob(vec![97]);
  let refs = vec![
    address_of(env, "Eq"),
    address_of(env, "Eq.refl"),
    anchor(Role::String),
    anchor(Role::StringOfList),
    anchor(Role::ListCons),
    anchor(Role::ListNil),
    anchor(Role::Char),
    anchor(Role::CharOfNat),
    text,
    code,
  ];
  // Universe 0 is `1`, universe 1 is `0`.
  let univs =
    vec![Arc::new(Univ::Succ(Arc::new(Univ::Zero))), Arc::new(Univ::Zero)];
  let string = || reference(2, vec![]);
  let char_t = || reference(6, vec![]);
  let literal = || arc(Expr::Str(8));
  let list = app(
    app(
      app(reference(4, vec![1]), char_t()),
      app(reference(7, vec![]), arc(Expr::Nat(9))),
    ),
    app(reference(5, vec![1]), char_t()),
  );
  let typ = app(
    app(app(reference(0, vec![0]), string()), literal()),
    app(reference(3, vec![]), list),
  );
  let value = app(app(reference(1, vec![0]), string()), literal());
  store(
    env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ,
      value,
    }),
    refs,
    univs,
  )
}

#[test]
fn string_literals_use_the_admitted_anchors() {
  let checked = |of_list_is_wrong: bool, bind_of_list: bool| {
    let mut env = loaded();
    let anchors = literal_anchors(&env, of_list_is_wrong);
    let theorem = string_literal_theorem(&env, &anchors);
    let mut roles = basis_roles(&env);
    roles.extend(
      anchors
        .into_iter()
        .filter(|(role, _)| bind_of_list || *role != Role::StringOfList),
    );
    bind(&mut env, roles);
    let source = ArtifactSource::snapshot(&env).unwrap();
    let refused = source.admission().refused().to_vec();
    let result =
      ArtifactChecker::<Anon>::from_source(Ok(source)).check_const(&theorem);
    (refused, result)
  };

  // Every anchor admitted: the literal expands to its `String.ofList` form.
  let (refused, result) = checked(false, true);
  assert!(refused.is_empty(), "{refused:?}");
  result.unwrap();

  // `String.ofList` declared but not bound: the expansion refuses.
  let (refused, result) = checked(false, false);
  assert!(refused.is_empty(), "{refused:?}");
  let error = result.unwrap_err();
  assert!(
    format!("{error}").contains("String.ofList support is not admitted"),
    "{error}"
  );

  // `String.ofList : List Char → List Char` is refused.
  let (refused, _) = checked(true, true);
  assert_eq!(refused.len(), 1, "{refused:?}");
  assert_eq!(refused[0].0, Role::StringOfList);
  assert!(refused[0].1.contains("differs from the specification: type"));
}

/// The structural operations with the number of their recurrence equations.
const STRUCTURAL: [(Role, &str, usize); 7] = [
  (Role::NatPred, "Nat.pred", 2),
  (Role::NatAdd, "Nat.add", 2),
  (Role::NatSub, "Nat.sub", 2),
  (Role::NatMul, "Nat.mul", 2),
  (Role::NatPow, "Nat.pow", 2),
  (Role::NatBeq, "Nat.beq", 4),
  (Role::NatBle, "Nat.ble", 3),
];

fn bool_roles(env: &Env) -> Vec<(Role, Address)> {
  vec![
    (Role::Bool, address_of(env, "Bool")),
    (Role::BoolFalse, address_of(env, "Bool.false")),
    (Role::BoolTrue, address_of(env, "Bool.true")),
    (Role::BoolRec, address_of(env, "Bool.rec")),
  ]
}

/// The basis, `Bool` and the structural operations, with their evidence.
fn bind_structural(env: &mut Env, swap_add_and_mul: bool) {
  let mut roles = basis_roles(env);
  roles.extend(bool_roles(env));
  let mut evidence = vec![];
  for (role, name, equations) in STRUCTURAL {
    let name = match (swap_add_and_mul, name) {
      (true, "Nat.add") => "Nat.mul",
      (true, "Nat.mul") => "Nat.add",
      _ => name,
    };
    roles.push((role, address_of(env, name)));
    evidence.push((role, vec![Evidence::DefEq; equations]));
  }
  bind_with_evidence(env, roles, evidence);
}

/// `theorem : @Eq.{1} Nat (Nat.pow 2 64) 18446744073709551616 := Eq.refl _`,
/// which only the admitted `Nat.pow` fast path checks in reasonable time.
fn power_theorem(env: &Env) -> Address {
  let two = env.store_blob(vec![2]);
  let sixty_four = env.store_blob(vec![64]);
  let mut big = vec![0; 8];
  big.push(1);
  let big = env.store_blob(big);
  let refs = vec![
    address_of(env, "Eq"),
    address_of(env, "Eq.refl"),
    address_of(env, "Nat"),
    address_of(env, "Nat.pow"),
    two,
    sixty_four,
    big,
  ];
  let univs = vec![Arc::new(Univ::Succ(Arc::new(Univ::Zero)))];
  let power =
    app(app(reference(3, vec![]), arc(Expr::Nat(4))), arc(Expr::Nat(5)));
  let typ = app(
    app(app(reference(0, vec![0]), reference(2, vec![])), power.clone()),
    arc(Expr::Nat(6)),
  );
  let value = app(app(reference(1, vec![0]), reference(2, vec![])), power);
  store(
    env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ,
      value,
    }),
    refs,
    univs,
  )
}

#[test]
fn the_structural_operations_are_admitted_by_their_equations() {
  let mut env = loaded();
  let theorem = power_theorem(&env);
  bind_structural(&mut env, false);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let admission = source.admission();
  assert!(admission.refused().is_empty(), "{:?}", admission.refused());
  for (role, _, _) in STRUCTURAL {
    assert!(source.is_admitted(role), "{role:?}");
  }
  ArtifactChecker::<Anon>::from_source(Ok(source))
    .check_const(&theorem)
    .unwrap();
}

#[test]
fn an_operation_whose_equations_fail_is_refused_with_its_dependents() {
  let mut env = loaded();
  bind_structural(&mut env, true);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let refused = source.admission().refused();
  let roles: Vec<Role> = refused.iter().map(|(role, _)| *role).collect();
  assert_eq!(roles, [Role::NatAdd, Role::NatMul, Role::NatPow], "{refused:?}");
  assert!(refused[0].1.contains("does not hold"), "{refused:?}");
  assert!(refused[1].1.contains("needs the unadmitted"), "{refused:?}");
  for role in [Role::NatPred, Role::NatSub, Role::NatBeq, Role::NatBle] {
    assert!(source.is_admitted(role), "{role:?}");
  }
}

/// The `True`, `And`, `Iff` and `Nonempty` anchors at their specified
/// types, the type formers and introductions as impredicative encodings and
/// the recursors as axioms (never used here), and the axioms `propext`,
/// `Classical.choice` and `sorryAx`.
fn axiom_roles(env: &Env) -> Vec<(Role, Address)> {
  let eq = address_of(env, "Eq");
  let zero = Arc::new(Univ::Zero);
  let one = Arc::new(Univ::Succ(zero.clone()));
  let param = Arc::new(Univ::Var(0));
  let v = |i: u64| arc(Expr::Var(i));
  // Universe 0 is always `Prop`; universe 1, where present, is `u`.
  let prop = || arc(Expr::Sort(0));
  let sort_u = || arc(Expr::Sort(1));
  let props = vec![zero.clone(), param.clone()];
  let both =
    |r: u64, a: u64, b: u64| app(app(reference(r, vec![]), v(a)), v(b));
  let four = |r: u64, args: [u64; 4]| {
    args.iter().fold(reference(r, vec![]), |f, a| app(f, v(*a)))
  };

  // `True := ∀ p : Prop, p → p`, `True.intro := fun _ h => h`.
  let true_t = definition(
    env,
    0,
    prop(),
    pi(prop(), pi(v(0), v(1))),
    vec![],
    vec![zero.clone()],
  );
  let true_intro = definition(
    env,
    0,
    reference(0, vec![]),
    lambda(prop(), lambda(v(0), v(0))),
    vec![true_t.clone()],
    vec![zero.clone()],
  );

  // `And a b := ∀ c : Prop, (a → b → c) → c`.
  let binary = || pi(prop(), pi(prop(), prop()));
  let and = definition(
    env,
    0,
    binary(),
    lambda(
      prop(),
      lambda(prop(), pi(prop(), pi(pi(v(2), pi(v(2), v(2))), v(1)))),
    ),
    vec![],
    vec![zero.clone()],
  );
  let and_intro = definition(
    env,
    0,
    pi(prop(), pi(prop(), pi(v(1), pi(v(1), both(0, 3, 2))))),
    lambda(
      prop(),
      lambda(
        prop(),
        lambda(
          v(1),
          lambda(
            v(1),
            lambda(
              prop(),
              lambda(pi(v(4), pi(v(4), v(2))), app(app(v(0), v(3)), v(2))),
            ),
          ),
        ),
      ),
    ),
    vec![and.clone()],
    vec![zero.clone()],
  );
  let and_rec = axiom(
    env,
    1,
    pi(
      prop(),
      pi(
        prop(),
        pi(
          pi(both(0, 1, 0), sort_u()),
          pi(
            pi(v(2), pi(v(2), app(v(2), four(1, [4, 3, 1, 0])))),
            pi(both(0, 3, 2), app(v(2), v(0))),
          ),
        ),
      ),
    ),
    vec![and.clone(), and_intro.clone()],
    props.clone(),
  );

  // `Iff a b := ∀ c : Prop, ((a → b) → (b → a) → c) → c`.
  let iff = definition(
    env,
    0,
    binary(),
    lambda(
      prop(),
      lambda(
        prop(),
        pi(prop(), pi(pi(pi(v(2), v(2)), pi(pi(v(2), v(4)), v(2))), v(1))),
      ),
    ),
    vec![],
    vec![zero.clone()],
  );
  let iff_intro = definition(
    env,
    0,
    pi(
      prop(),
      pi(prop(), pi(pi(v(1), v(1)), pi(pi(v(1), v(3)), both(0, 3, 2)))),
    ),
    lambda(
      prop(),
      lambda(
        prop(),
        lambda(
          pi(v(1), v(1)),
          lambda(
            pi(v(1), v(3)),
            lambda(
              prop(),
              lambda(
                pi(pi(v(4), v(4)), pi(pi(v(4), v(6)), v(2))),
                app(app(v(0), v(3)), v(2)),
              ),
            ),
          ),
        ),
      ),
    ),
    vec![iff.clone()],
    vec![zero.clone()],
  );
  let iff_rec = axiom(
    env,
    1,
    pi(
      prop(),
      pi(
        prop(),
        pi(
          pi(both(0, 1, 0), sort_u()),
          pi(
            pi(
              pi(v(2), v(2)),
              pi(pi(v(2), v(4)), app(v(2), four(1, [4, 3, 1, 0]))),
            ),
            pi(both(0, 3, 2), app(v(2), v(0))),
          ),
        ),
      ),
    ),
    vec![iff.clone(), iff_intro.clone()],
    props.clone(),
  );

  // `Nonempty.{u} α := ∀ p : Prop, (α → p) → p`.
  let nonempty = definition(
    env,
    1,
    pi(sort_u(), prop()),
    lambda(sort_u(), pi(prop(), pi(pi(v(1), v(1)), v(1)))),
    vec![],
    props.clone(),
  );
  let nonempty_u = |e| app(reference(0, vec![1]), e);
  let nonempty_intro = definition(
    env,
    1,
    pi(sort_u(), pi(v(0), nonempty_u(v(1)))),
    lambda(
      sort_u(),
      lambda(v(0), lambda(prop(), lambda(pi(v(2), v(1)), app(v(0), v(2))))),
    ),
    vec![nonempty.clone()],
    props.clone(),
  );
  let nonempty_rec = axiom(
    env,
    1,
    pi(
      sort_u(),
      pi(
        pi(nonempty_u(v(0)), prop()),
        pi(
          pi(v(1), app(v(1), app(app(reference(1, vec![1]), v(2)), v(0)))),
          pi(nonempty_u(v(2)), app(v(2), v(0))),
        ),
      ),
    ),
    vec![nonempty.clone(), nonempty_intro.clone()],
    props.clone(),
  );

  // `propext {a b : Prop} : Iff a b → @Eq.{1} Prop a b`; universe 1 is `1`.
  let propext = axiom(
    env,
    0,
    pi(
      prop(),
      pi(
        prop(),
        pi(
          both(0, 1, 0),
          app(app(app(reference(1, vec![1]), prop()), v(2)), v(1)),
        ),
      ),
    ),
    vec![iff.clone(), eq],
    vec![zero.clone(), one],
  );
  let choice = axiom(
    env,
    1,
    pi(sort_u(), pi(nonempty_u(v(0)), v(1))),
    vec![nonempty.clone()],
    props.clone(),
  );
  let sorry = axiom(env, 1, pi(sort_u(), v(0)), vec![], props);
  vec![
    (Role::True, true_t),
    (Role::TrueIntro, true_intro),
    (Role::And, and),
    (Role::AndIntro, and_intro),
    (Role::AndRec, and_rec),
    (Role::Iff, iff),
    (Role::IffIntro, iff_intro),
    (Role::IffRec, iff_rec),
    (Role::Nonempty, nonempty),
    (Role::NonemptyIntro, nonempty_intro),
    (Role::NonemptyRec, nonempty_rec),
    (Role::Propext, propext),
    (Role::Choice, choice),
    (Role::SorryAx, sorry),
  ]
}

/// `theorem : True := e`, with `refs` for `e`'s references.
fn proof_of_true(
  env: &Env,
  true_t: &Address,
  value: Arc<Expr>,
  mut refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Address {
  refs.insert(0, true_t.clone());
  store(
    env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: reference(0, vec![]),
      value,
    }),
    refs,
    univs,
  )
}

#[test]
fn only_the_standard_axioms_may_be_used() {
  let mut env = loaded();
  let roles = axiom_roles(&env);
  let role = |r: Role| roles.iter().find(|(x, _)| *x == r).unwrap().1.clone();
  let true_t = role(Role::True);
  // `sorryAx.{0} True`, and a nonstandard `axiom : True`.
  let zero = Arc::new(Univ::Zero);
  let uses_sorry = proof_of_true(
    &env,
    &true_t,
    app(reference(1, vec![0]), reference(0, vec![])),
    vec![role(Role::SorryAx)],
    vec![zero.clone()],
  );
  let nonstandard =
    axiom(&env, 0, reference(0, vec![]), vec![true_t.clone()], vec![]);
  let uses_nonstandard = proof_of_true(
    &env,
    &true_t,
    reference(1, vec![]),
    vec![nonstandard.clone()],
    vec![],
  );
  // `def : ∀ {a b : Prop}, Iff a b → a = b := @propext`, and an unsafe
  // axiom, which is outside the safe theory's policy.
  let prop = || arc(Expr::Sort(0));
  let uses_propext = store(
    &env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: pi(
        prop(),
        pi(
          prop(),
          pi(
            app(
              app(reference(0, vec![]), arc(Expr::Var(1))),
              arc(Expr::Var(0)),
            ),
            app(
              app(app(reference(1, vec![1]), prop()), arc(Expr::Var(2))),
              arc(Expr::Var(1)),
            ),
          ),
        ),
      ),
      value: reference(2, vec![]),
    }),
    vec![role(Role::Iff), address_of(&env, "Eq"), role(Role::Propext)],
    vec![zero, Arc::new(Univ::Succ(Arc::new(Univ::Zero)))],
  );
  let unsafe_axiom = store(
    &env,
    ConstantInfo::Axio(Axiom {
      is_unsafe: true,
      lvls: 0,
      typ: reference(0, vec![]),
    }),
    vec![true_t.clone()],
    vec![],
  );
  let mut bound = basis_roles(&env);
  bound.extend(roles.iter().cloned());
  bind(&mut env, bound);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let refused = source.admission().refused();
  assert!(refused.is_empty(), "{refused:?}");
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
  for declared in [Role::Propext, Role::Choice, Role::SorryAx] {
    checker
      .check_const(&role(declared))
      .unwrap_or_else(|e| panic!("{declared:?}: {e}"));
  }
  checker.check_const(&uses_propext).unwrap();
  checker.check_const(&unsafe_axiom).unwrap();
  for (address, reason) in [
    (&uses_sorry, "is not an admitted standard axiom"),
    (&nonstandard, "is not a standard axiom of the checked theory"),
    (&uses_nonstandard, "is not an admitted standard axiom"),
  ] {
    let error = checker.check_const(address).unwrap_err();
    assert!(format!("{error}").contains(reason), "{error}");
  }
}
