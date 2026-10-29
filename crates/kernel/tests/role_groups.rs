//! Group admission of bound roles, on the compiler's own basis blocks.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, Name};
use ix_kernel::anon_work::{build_artifact_work, verdict_work};
use ix_kernel::artifact_checker::ArtifactChecker;
use ix_kernel::mode::Anon;
use ix_kernel::role_admission::{ArtifactSource, PRELUDE, SPEC_VERSION};
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
  let raw =
    RoleTable { version: SPEC_VERSION, bound, evidence }.to_bytes().unwrap();
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
  let bound = with_prelude(&env, roles.clone());
  bind(&mut env, bound);
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
    // Nat is in the prelude: without it no unit is checked at all.
    assert!(format!("{error}").contains("prelude is not admitted"), "{error}");
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
  let bound = with_prelude(&env, roles.clone());
  bind(&mut env, bound.clone());
  let source = ArtifactSource::snapshot(&env).unwrap();
  let admission = source.admission();
  assert!(admission.refused().is_empty(), "{:?}", admission.refused());
  assert_eq!(admission.admitted_count(), bound.len());
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
  // The whole prelude but the quotient package.
  let roles: Vec<_> = with_prelude(&env, nat_roles(&env))
    .into_iter()
    .filter(|(role, _)| {
      !matches!(
        role,
        Role::Quot
          | Role::QuotMk
          | Role::QuotLift
          | Role::QuotInd
          | Role::QuotSound
      )
    })
    .collect();
  bind(&mut env, roles);
  let error = ArtifactChecker::<Anon>::from_source(Ok(
    ArtifactSource::snapshot(&env).unwrap(),
  ))
  .check_const(&definition)
  .unwrap_err();
  assert!(
    format!("{error}").contains("does not bind the prelude role Quot"),
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
    let roles = with_prelude(&env, roles);
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
  let roles = with_prelude(env, roles);
  bind_with_evidence(env, roles, evidence);
}

#[derive(Clone, Copy, Debug)]
enum DefinitionMutation {
  None,
  AnchorAxiom,
  WrongValue,
  WrongType,
  ExtraUniverse,
  Opaque,
  Unsafe,
}

/// A small alternate representation: Int is Nat, ofNat is identity, and
/// negSucc is successor. A beta-expanded identity satisfies negOfNat's
/// actual generated equations; the mutants remain separately addressed.
fn equation_candidate(
  env: &Env,
  mutation: DefinitionMutation,
) -> Vec<(Role, Address)> {
  let nat = address_of(env, "Nat");
  let zero = address_of(env, "Nat.zero");
  let succ = address_of(env, "Nat.succ");
  let one = Arc::new(Univ::Succ(Arc::new(Univ::Zero)));
  let integer = if matches!(mutation, DefinitionMutation::AnchorAxiom) {
    axiom(env, 0, arc(Expr::Sort(0)), vec![], vec![one])
  } else {
    definition(
      env,
      0,
      arc(Expr::Sort(0)),
      app(lambda(arc(Expr::Sort(0)), arc(Expr::Var(0))), reference(0, vec![])),
      vec![nat.clone()],
      vec![one],
    )
  };
  let typ = pi(reference(0, vec![]), reference(1, vec![]));
  let of_nat = definition(
    env,
    0,
    typ.clone(),
    lambda(reference(0, vec![]), arc(Expr::Var(0))),
    vec![nat.clone(), integer.clone()],
    vec![],
  );
  let negative = definition(
    env,
    0,
    typ.clone(),
    reference(2, vec![]),
    vec![nat.clone(), integer.clone(), succ],
    vec![],
  );
  let body = match mutation {
    DefinitionMutation::WrongValue => reference(2, vec![]),
    _ => {
      app(lambda(reference(0, vec![]), arc(Expr::Var(0))), arc(Expr::Var(0)))
    },
  };
  let (typ, value) = match mutation {
    DefinitionMutation::WrongType => {
      (reference(0, vec![]), reference(2, vec![]))
    },
    _ => (typ, lambda(reference(0, vec![]), body)),
  };
  let operation = store(
    env,
    ConstantInfo::Defn(Definition {
      kind: if matches!(mutation, DefinitionMutation::Opaque) {
        DefKind::Opaque
      } else {
        DefKind::Definition
      },
      safety: if matches!(mutation, DefinitionMutation::Unsafe) {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      },
      lvls: u64::from(matches!(mutation, DefinitionMutation::ExtraUniverse)),
      typ,
      value,
    }),
    vec![nat, integer.clone(), zero],
    vec![],
  );
  vec![
    (Role::Int, integer),
    (Role::IntOfNat, of_nat),
    (Role::IntNegSucc, negative),
    (Role::IntNegOfNat, operation),
  ]
}

fn bind_equation_candidate(
  env: &mut Env,
  extra: &[(Role, Address)],
  evidence: Vec<Evidence>,
) {
  let mut roles = basis_roles(env);
  roles.extend(extra.iter().cloned());
  let roles = with_prelude(env, roles);
  bind_with_evidence(env, roles, vec![(Role::IntNegOfNat, evidence)]);
}

#[test]
fn generated_equations_admit_actual_definitions_and_refuse_semantic_mutants() {
  for (mutation, expected) in [
    (DefinitionMutation::None, None),
    (
      DefinitionMutation::WrongValue,
      Some("definitional equation does not hold"),
    ),
    (DefinitionMutation::WrongType, Some("definition type")),
    (DefinitionMutation::ExtraUniverse, Some("universe parameter count")),
    (DefinitionMutation::Opaque, Some("not a safe definition")),
    (DefinitionMutation::Unsafe, Some("not a safe definition")),
  ] {
    let mut env = loaded();
    let roles = equation_candidate(&env, mutation);
    bind_equation_candidate(&mut env, &roles, vec![Evidence::DefEq; 2]);
    let source = ArtifactSource::snapshot(&env).unwrap();
    for role in
      [Role::Nat, Role::Eq, Role::Int, Role::IntOfNat, Role::IntNegSucc]
    {
      assert!(
        source.is_admitted(role),
        "{mutation:?}: {:?}",
        source.admission().refused()
      );
    }
    let refused = source.admission().refused();
    if let Some(expected) = expected {
      assert_eq!(refused.len(), 1, "{mutation:?}: {refused:?}");
      assert_eq!(refused[0].0, Role::IntNegOfNat);
      assert!(refused[0].1.contains(expected), "{mutation:?}: {refused:?}");
      assert!(!source.is_admitted(Role::IntNegOfNat));
      ArtifactChecker::<Anon>::from_source(Ok(source))
        .check_const(&roles[3].1)
        .unwrap_err();
    } else {
      assert!(refused.is_empty(), "{refused:?}");
      assert!(source.is_admitted(Role::IntNegOfNat));
      ArtifactChecker::<Anon>::from_source(Ok(source))
        .check_const(&roles[3].1)
        .unwrap();
    }
  }
}

#[test]
fn generated_support_anchors_cannot_admit_a_new_axiom() {
  let mut env = loaded();
  let roles = equation_candidate(&env, DefinitionMutation::AnchorAxiom);
  bind_equation_candidate(&mut env, &roles, vec![Evidence::DefEq; 2]);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let refused = source.admission().refused();
  assert_eq!(refused.len(), 2, "{refused:?}");
  assert_eq!(refused[0].0, Role::Int);
  assert!(
    refused[0].1.contains("not an admitted standard axiom"),
    "{refused:?}"
  );
  assert_eq!(refused[1].0, Role::IntNegOfNat);
  assert!(!source.is_admitted(Role::Int));
  assert!(!source.is_admitted(Role::IntNegOfNat));
}

#[test]
fn equation_rhs_anchors_require_their_helpers_to_be_well_typed() {
  for ill_typed in [false, true] {
    let mut env = loaded();
    let mut roles = equation_candidate(&env, DefinitionMutation::None);
    let nat = address_of(&env, "Nat");
    let integer = roles[0].1.clone();
    let discarded =
      address_of(&env, if ill_typed { "True.intro" } else { "Nat.zero" });
    // Both helpers reduce to successor. In the negative case the erased
    // argument is a proof of True where the lambda requires a Nat.
    let helper = definition(
      &env,
      0,
      pi(reference(0, vec![]), reference(1, vec![])),
      lambda(
        reference(0, vec![]),
        app(
          lambda(
            reference(0, vec![]),
            app(reference(2, vec![]), arc(Expr::Var(1))),
          ),
          reference(3, vec![]),
        ),
      ),
      vec![
        nat.clone(),
        integer.clone(),
        address_of(&env, "Nat.succ"),
        discarded,
      ],
      vec![],
    );
    let rhs_anchor = definition(
      &env,
      0,
      pi(reference(0, vec![]), reference(1, vec![])),
      reference(2, vec![]),
      vec![nat, integer, helper.clone()],
      vec![],
    );
    assert_eq!(roles[2].0, Role::IntNegSucc);
    roles[2].1 = rhs_anchor.clone();
    bind_equation_candidate(&mut env, &roles, vec![Evidence::DefEq; 2]);
    let source = ArtifactSource::snapshot(&env).unwrap();
    let actual_closure = source.closure(&[roles[3].1.clone()]).unwrap();
    assert!(!actual_closure.contains(&rhs_anchor));
    assert!(!actual_closure.contains(&helper));
    let admitted = source.admission();
    if ill_typed {
      assert!(
        !source.is_admitted(Role::IntNegSucc),
        "{:?}",
        admitted.refused()
      );
      assert!(
        !source.is_admitted(Role::IntNegOfNat),
        "{:?}",
        admitted.refused()
      );
      ArtifactChecker::<Anon>::from_source(Ok(source))
        .check_const(&helper)
        .unwrap_err();
    } else {
      assert!(admitted.refused().is_empty(), "{:?}", admitted.refused());
      assert!(source.is_admitted(Role::IntNegSucc));
      assert!(source.is_admitted(Role::IntNegOfNat));
      ArtifactChecker::<Anon>::from_source(Ok(source))
        .check_const(&helper)
        .unwrap();
    }
  }
}

#[derive(Clone, Copy, Debug)]
enum ProofMutation {
  None,
  ValidHelper,
  WrongStatement,
  WrongBody,
  BadHelper,
  ExtraUniverse,
}

/// Ordinary reflexivity witnesses for the alternate representation above.
/// A wrong-statement mutant is itself a valid theorem; it must fail the
/// generated equation check, independently of ordinary declaration checking.
fn equation_proofs(
  env: &Env,
  roles: &[(Role, Address)],
  mutation: ProofMutation,
) -> Vec<Evidence> {
  let integer = roles[0].1.clone();
  let of_nat = roles[1].1.clone();
  let negative = roles[2].1.clone();
  let operation = roles[3].1.clone();
  let mut refs = vec![
    address_of(env, "Eq"),
    address_of(env, "Eq.refl"),
    integer,
    operation,
    address_of(env, "Nat.zero"),
    of_nat,
    address_of(env, "Nat"),
    address_of(env, "Nat.succ"),
    negative,
  ];
  let r = |i| reference(i, vec![]);
  let equality =
    |lhs, rhs| app(app(app(reference(0, vec![0]), r(2)), lhs), rhs);
  let refl = |term| app(app(reference(1, vec![0]), r(2)), term);
  let first = app(r(5), r(4));
  let mut statements = [
    equality(app(r(3), r(4)), first.clone()),
    pi(
      r(6),
      equality(
        app(r(3), app(r(7), arc(Expr::Var(0)))),
        app(r(8), arc(Expr::Var(0))),
      ),
    ),
  ];
  let mut values =
    [refl(first), lambda(r(6), refl(app(r(8), arc(Expr::Var(0)))))];
  if matches!(mutation, ProofMutation::WrongStatement) {
    let one = app(r(7), r(4));
    statements[0] = equality(one.clone(), one.clone());
    values[0] = refl(one);
  }
  if matches!(mutation, ProofMutation::WrongBody) {
    values[0] = arc(Expr::Var(0));
  }
  if matches!(mutation, ProofMutation::ValidHelper | ProofMutation::BadHelper) {
    let helper = store(
      env,
      ConstantInfo::Defn(Definition {
        kind: DefKind::Theorem,
        safety: DefinitionSafety::Safe,
        lvls: 0,
        typ: statements[0].clone(),
        value: if matches!(mutation, ProofMutation::ValidHelper) {
          values[0].clone()
        } else {
          arc(Expr::Var(0))
        },
      }),
      refs.clone(),
      vec![Arc::new(Univ::Succ(Arc::new(Univ::Zero)))],
    );
    values[0] = reference(u64::try_from(refs.len()).unwrap(), vec![]);
    refs.push(helper);
  }
  statements
    .into_iter()
    .zip(values)
    .map(|(typ, value)| {
      Evidence::Proof(store(
        env,
        ConstantInfo::Defn(Definition {
          kind: DefKind::Theorem,
          safety: DefinitionSafety::Safe,
          lvls: u64::from(matches!(mutation, ProofMutation::ExtraUniverse)),
          typ,
          value,
        }),
        refs.clone(),
        vec![Arc::new(Univ::Succ(Arc::new(Univ::Zero)))],
      ))
    })
    .collect()
}

#[test]
fn generated_equations_check_proof_bodies_statements_and_universes() {
  for mutation in [
    ProofMutation::None,
    ProofMutation::ValidHelper,
    ProofMutation::WrongStatement,
    ProofMutation::WrongBody,
    ProofMutation::BadHelper,
    ProofMutation::ExtraUniverse,
  ] {
    let mut env = loaded();
    let roles = equation_candidate(&env, DefinitionMutation::None);
    let evidence = equation_proofs(&env, &roles, mutation);
    bind_equation_candidate(&mut env, &roles, evidence);
    let source = ArtifactSource::snapshot(&env).unwrap();
    assert!(
      source.is_admitted(Role::Int),
      "{:?}",
      source.admission().refused()
    );
    let refused = source.admission().refused();
    if matches!(mutation, ProofMutation::None | ProofMutation::ValidHelper) {
      assert!(refused.is_empty(), "{refused:?}");
      assert!(source.is_admitted(Role::IntNegOfNat));
    } else {
      assert_eq!(refused.len(), 1, "{mutation:?}: {refused:?}");
      assert_eq!(refused[0].0, Role::IntNegOfNat);
      assert!(!source.is_admitted(Role::IntNegOfNat));
      if matches!(mutation, ProofMutation::WrongStatement) {
        assert!(refused[0].1.contains("different statement"), "{refused:?}");
      }
    }
  }
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

/// `True`, `And`, `Iff` and `Nonempty` declared at their specified types,
/// the type formers and introductions as impredicative encodings and the
/// recursors as axioms (never used here), with the axioms `propext` and
/// `Classical.choice` of their specified types over them and a `sorryAx` of
/// type `∀ α, α`. The `True` and `And` anchors are specified by type alone,
/// so these serve; `Iff` and `Nonempty` are blocks, and `sorryAx` has its
/// type, so those are refused.
fn definitional_axiom_roles(env: &Env) -> Vec<(Role, Address)> {
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

/// The `True` and `And` anchors as in [`definitional_axiom_roles`], with
/// the compiled `Iff` and `Nonempty` families, `propext`,
/// `Classical.choice` and `sorryAx`.
fn axiom_roles(env: &Env) -> Vec<(Role, Address)> {
  let mut roles: Vec<(Role, Address)> = definitional_axiom_roles(env)
    .into_iter()
    .filter(|(role, _)| {
      matches!(
        role,
        Role::True
          | Role::TrueIntro
          | Role::And
          | Role::AndIntro
          | Role::AndRec
      )
    })
    .collect();
  for role in [
    Role::Iff,
    Role::IffIntro,
    Role::IffRec,
    Role::Nonempty,
    Role::NonemptyIntro,
    Role::NonemptyRec,
    Role::Propext,
    Role::Choice,
    Role::SorryAx,
  ] {
    roles.push((role, address_of(env, role.lean_name())));
  }
  roles
}

/// Bind the basis, the prelude and `roles`, and return the snapshot.
fn bound_with_basis(
  env: &mut Env,
  roles: &[(Role, Address)],
) -> ArtifactSource {
  let mut bound = basis_roles(env);
  bound.extend(roles.iter().cloned());
  let bound = with_prelude(env, bound);
  bind(env, bound);
  ArtifactSource::snapshot(env).unwrap()
}

fn refused_roles(source: &ArtifactSource) -> Vec<Role> {
  source.admission().refused().iter().map(|(role, _)| *role).collect()
}

#[test]
fn families_specified_by_type_alone_are_refused() {
  // `Iff` and `Nonempty` must be the inductives the standard axioms
  // quantify over, and `sorryAx` must have its type: definitions of the
  // families' types, and an axiom `∀ α, α`, are refused, and so are the
  // axioms over those families.
  let mut env = loaded();
  let roles = definitional_axiom_roles(&env);
  let source = bound_with_basis(&mut env, &roles);
  assert_eq!(
    refused_roles(&source),
    [Role::Iff, Role::Nonempty, Role::Propext, Role::Choice, Role::SorryAx]
  );
  let refused = source.admission().refused();
  for (_, reason) in &refused[..2] {
    assert!(reason.contains("not a member of a carried unit"), "{reason}");
  }
  for (_, reason) in &refused[2..4] {
    assert!(reason.contains("needs the unadmitted"), "{reason}");
  }
  assert!(refused[4].1.contains("differs from the specification: type"));
  for role in [Role::True, Role::And] {
    assert!(source.is_admitted(role), "{role:?}");
  }
}

/// `Nonempty.{u} := fun _ => True`, `Nonempty.intro := fun _ _ =>
/// True.intro`, an axiom `choice'.{u} (α : Sort u) : Nonempty α → α` (the
/// specified type of `Classical.choice` over that `Nonempty`), and
/// `Nonempty.rec := fun α motive h t => h (choice' α t)`, well typed by
/// proof irrelevance since `Nonempty α` is `True`; with `theorem bad : False
/// := choice'.{0} False True.intro`. Returns the roles and `bad`.
fn nonempty_as_true(env: &Env) -> (Vec<(Role, Address)>, Address) {
  let true_t = address_of(env, "True");
  let true_intro = address_of(env, "True.intro");
  let v = |i: u64| arc(Expr::Var(i));
  // Universe 0 is `Prop`, universe 1 is `u`.
  let prop = || arc(Expr::Sort(0));
  let sort_u = || arc(Expr::Sort(1));
  let props = || vec![Arc::new(Univ::Zero), Arc::new(Univ::Var(0))];
  let nonempty_u = |e| app(reference(0, vec![1]), e);
  let nonempty = definition(
    env,
    1,
    pi(sort_u(), prop()),
    lambda(sort_u(), reference(0, vec![])),
    vec![true_t.clone()],
    props(),
  );
  let intro = definition(
    env,
    1,
    pi(sort_u(), pi(v(0), nonempty_u(v(1)))),
    lambda(sort_u(), lambda(v(0), reference(1, vec![]))),
    vec![nonempty.clone(), true_intro.clone()],
    props(),
  );
  let choice = axiom(
    env,
    1,
    pi(sort_u(), pi(nonempty_u(v(0)), v(1))),
    vec![nonempty.clone()],
    props(),
  );
  let motive = || pi(nonempty_u(v(0)), prop());
  let minor =
    || pi(v(1), app(v(1), app(app(reference(1, vec![1]), v(2)), v(0))));
  let major = || nonempty_u(v(2));
  let rec = definition(
    env,
    1,
    pi(sort_u(), pi(motive(), pi(minor(), pi(major(), app(v(2), v(0)))))),
    lambda(
      sort_u(),
      lambda(
        motive(),
        lambda(
          minor(),
          lambda(
            major(),
            app(v(1), app(app(reference(2, vec![1]), v(3)), v(0))),
          ),
        ),
      ),
    ),
    vec![nonempty.clone(), intro.clone(), choice.clone()],
    props(),
  );
  let bad = store(
    env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: reference(0, vec![]),
      value: app(
        app(reference(1, vec![0]), reference(0, vec![])),
        reference(2, vec![]),
      ),
    }),
    vec![address_of(env, "False"), choice.clone(), true_intro.clone()],
    vec![Arc::new(Univ::Zero)],
  );
  let roles = vec![
    (Role::True, true_t),
    (Role::TrueIntro, true_intro),
    (Role::Nonempty, nonempty),
    (Role::NonemptyIntro, intro),
    (Role::NonemptyRec, rec),
    (Role::Choice, choice),
  ];
  (roles, bad)
}

#[test]
fn nonempty_as_true_does_not_admit_choice() {
  // With `Nonempty` specified by its type alone, every group here was
  // admitted, every unit checked, and `bad : False` with them.
  let mut env = loaded();
  let (roles, bad) = nonempty_as_true(&env);
  let source = bound_with_basis(&mut env, &roles);
  assert_eq!(refused_roles(&source), [Role::Nonempty, Role::Choice]);
  let role = |r: Role| roles.iter().find(|(x, _)| *x == r).unwrap().1.clone();
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
  for r in
    [Role::Nonempty, Role::NonemptyIntro, Role::NonemptyRec, Role::Choice]
  {
    let error = checker.check_const(&role(r)).unwrap_err();
    assert!(
      format!("{error}").contains("requires unadmitted role"),
      "{r:?}: {error}"
    );
  }
  let error = checker.check_const(&bad).unwrap_err();
  assert!(
    format!("{error}").contains("is not an admitted standard axiom"),
    "{error}"
  );
}

#[test]
fn sorry_bound_to_another_axiom_is_refused() {
  // `sorryAx` is inert, but it has its type: a binding cannot make
  // `axiom evil.{u} : False` the one tolerated axiom.
  let mut env = loaded();
  let evil = axiom(
    &env,
    1,
    reference(0, vec![]),
    vec![address_of(&env, "False")],
    vec![],
  );
  let bound = with_prelude(&env, vec![(Role::SorryAx, evil.clone())]);
  bind(&mut env, bound);
  let source = ArtifactSource::snapshot(&env).unwrap();
  assert_eq!(refused_roles(&source), [Role::SorryAx]);
  let reason = &source.admission().refused()[0].1;
  assert!(reason.contains("differs from the specification: type"), "{reason}");
  let error = ArtifactChecker::<Anon>::from_source(Ok(source))
    .check_const(&evil)
    .unwrap_err();
  assert!(
    format!("{error}").contains("requires unadmitted role SorryAx"),
    "{error}"
  );
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
  // `sorryAx.{0} True false`, and a nonstandard `axiom : True`.
  let zero = Arc::new(Univ::Zero);
  let uses_sorry = proof_of_true(
    &env,
    &true_t,
    app(app(reference(1, vec![0]), reference(0, vec![])), reference(2, vec![])),
    vec![role(Role::SorryAx), address_of(&env, "Bool.false")],
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
  let bound = with_prelude(&env, bound);
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

/// Bind the basis, `Bool`, the structural operations and a `Nat.div` of
/// `fun x _ => x` whose three evidence entries are the theorem `proof`;
/// return why `Nat.div` was refused.
fn refused_division(mut env: Env, proof: Address) -> String {
  let nat = address_of(&env, "Nat");
  let div = definition(
    &env,
    0,
    pi(reference(0, vec![]), pi(reference(0, vec![]), reference(0, vec![]))),
    lambda(
      reference(0, vec![]),
      lambda(reference(0, vec![]), arc(Expr::Var(1))),
    ),
    vec![nat],
    vec![],
  );
  let mut roles = basis_roles(&env);
  roles.extend(bool_roles(&env));
  let mut evidence = vec![];
  for (role, name, equations) in STRUCTURAL {
    roles.push((role, address_of(&env, name)));
    evidence.push((role, vec![Evidence::DefEq; equations]));
  }
  roles.push((Role::NatDiv, div));
  evidence.push((Role::NatDiv, vec![Evidence::Proof(proof); 3]));
  bind_with_evidence(&mut env, roles, evidence);
  let source = ArtifactSource::snapshot(&env).unwrap();
  assert!(!source.is_admitted(Role::NatDiv));
  let refused = source.admission().refused();
  assert_eq!(refused.len(), 1, "{refused:?}");
  assert_eq!(refused[0].0, Role::NatDiv);
  refused[0].1.clone()
}

#[test]
fn a_well_founded_operation_needs_local_proofs_of_its_statements() {
  // A proof that mentions records outside the operation's closure.
  let env = loaded();
  let roles = axiom_roles(&env);
  let proof = proof_of_true(
    &env,
    &roles[0].1,
    reference(1, vec![]),
    vec![roles[1].1.clone()],
    vec![],
  );
  let reason = refused_division(env, proof);
  assert!(reason.contains("outside the operation's closure"), "{reason}");

  // A local term that proves nothing.
  let env = loaded();
  let proof = store(
    &env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: reference(0, vec![]),
      value: reference(1, vec![]),
    }),
    vec![address_of(&env, "Nat"), address_of(&env, "Nat.zero")],
    vec![],
  );
  let reason = refused_division(env, proof);
  assert!(reason.contains("certificate 0"), "{reason}");
}

fn theorem(
  env: &Env,
  typ: Arc<Expr>,
  value: Arc<Expr>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Address {
  declare(
    env,
    DefKind::Theorem,
    DefinitionSafety::Safe,
    typ,
    value,
    refs,
    univs,
  )
}

fn apps(head: Arc<Expr>, arguments: Vec<Arc<Expr>>) -> Arc<Expr> {
  arguments.into_iter().fold(head, app)
}

/// A `Nat.div` admitted on a lemma that does not check: the lemma is local
/// to the division's certificates only through a dead reference in the
/// bound `Nat.sub`'s value, so the closure of a constant that uses the
/// division does not reach it. A verdict on that constant must still check
/// the lemma, because admission assumed it.
#[test]
fn a_closure_verdict_checks_what_role_admission_assumed() {
  let mut env = loaded();
  let a = |name: &str| address_of(&env, name);
  let (nat, zero, succ, eq) = (a("Nat"), a("Nat.zero"), a("Nat.succ"), a("Eq"));
  let (eq_refl, eq_rec) = (a("Eq.refl"), a("Eq.rec"));
  let (boolean, true_c, false_c) = (a("Bool"), a("Bool.true"), a("Bool.false"));
  let ble = a("Nat.ble");
  let one = || Arc::new(Univ::Succ(Arc::new(Univ::Zero)));
  let v = |i: u64| arc(Expr::Var(i));
  let r = |i: u64| reference(i, vec![]);
  let eq_at = |i: u64, t: Arc<Expr>, lhs: Arc<Expr>, rhs: Arc<Expr>| {
    apps(reference(i, vec![0]), vec![t, lhs, rhs])
  };

  // `theorem zero_is_one : @Eq Nat Nat.zero (Nat.succ Nat.zero)
  //   := @Eq.refl Nat Nat.zero`, which does not check.
  // refs: Eq, Nat, Nat.zero, Nat.succ, Eq.refl
  let zero_is_one = theorem(
    &env,
    eq_at(0, r(1), r(2), app(r(3), r(2))),
    apps(reference(4, vec![0]), vec![r(1), r(2)]),
    vec![eq.clone(), nat.clone(), zero.clone(), succ.clone(), eq_refl.clone()],
    vec![one()],
  );
  // `def sub (x y : Nat) : Nat := (fun _ : 0 = 1 => Nat.sub x y) zero_is_one`
  // refs: Nat, Nat.sub, Eq, Nat.zero, Nat.succ, zero_is_one
  let sub = definition(
    &env,
    0,
    pi(r(0), pi(r(0), r(0))),
    lambda(
      r(0),
      lambda(
        r(0),
        app(
          lambda(
            eq_at(2, r(0), r(3), app(r(4), r(3))),
            apps(r(1), vec![v(2), v(1)]),
          ),
          r(5),
        ),
      ),
    ),
    vec![
      nat.clone(),
      a("Nat.sub"),
      eq.clone(),
      zero.clone(),
      succ.clone(),
      zero_is_one.clone(),
    ],
    vec![one()],
  );
  // `def div (_ _ : Nat) : Nat := Nat.zero`
  let div = definition(
    &env,
    0,
    pi(r(0), pi(r(0), r(0))),
    lambda(r(0), lambda(r(0), r(1))),
    vec![nat.clone(), zero.clone()],
    vec![],
  );
  // The certificates, over refs Nat, Eq, Bool, Nat.ble, Bool.true,
  // Bool.false, Nat.succ, Nat.zero, div, sub, zero_is_one, Eq.refl.
  let refs = vec![
    nat.clone(),
    eq.clone(),
    boolean,
    ble,
    true_c,
    false_c,
    succ.clone(),
    zero.clone(),
    div.clone(),
    sub.clone(),
    zero_is_one.clone(),
    eq_refl.clone(),
  ];
  let guard = |a: Arc<Expr>, b: Arc<Expr>, holds: bool| {
    eq_at(1, r(2), apps(r(3), vec![a, b]), r(if holds { 4 } else { 5 }))
  };
  let one_n = || app(r(6), r(7));
  let div_of = |x: Arc<Expr>, y: Arc<Expr>| apps(r(8), vec![x, y]);
  // `∀ x y, ble y x = true → ble 1 y = true → div x y = succ (div (sub x y)
  // y) := fun _ _ _ _ => zero_is_one`
  let recursive = theorem(
    &env,
    pi(
      r(0),
      pi(
        r(0),
        pi(
          guard(v(0), v(1), true),
          pi(
            guard(one_n(), v(1), true),
            eq_at(
              1,
              r(0),
              div_of(v(3), v(2)),
              app(r(6), div_of(apps(r(9), vec![v(3), v(2)]), v(2))),
            ),
          ),
        ),
      ),
    ),
    lambda(
      r(0),
      lambda(
        r(0),
        lambda(
          guard(v(0), v(1), true),
          lambda(guard(one_n(), v(1), true), r(10)),
        ),
      ),
    ),
    refs.clone(),
    vec![one()],
  );
  // `∀ x y, g = false → div x y = 0 := fun _ _ _ => rfl`, for the guards
  // `ble y x` and `ble 1 y`.
  let base = |guard_of: &dyn Fn() -> Arc<Expr>| {
    theorem(
      &env,
      pi(
        r(0),
        pi(r(0), pi(guard_of(), eq_at(1, r(0), div_of(v(2), v(1)), r(7)))),
      ),
      lambda(
        r(0),
        lambda(
          r(0),
          lambda(guard_of(), apps(reference(11, vec![0]), vec![r(0), r(7)])),
        ),
      ),
      refs.clone(),
      vec![one()],
    )
  };
  let below = base(&|| guard(v(0), v(1), false));
  let by_zero = base(&|| guard(one_n(), v(0), false));

  // `theorem vanishes : ∀ n, div n 2 = 0 := fun _ => rfl`, by unfolding.
  // refs: Nat, Eq, div, 2, Nat.zero, Eq.refl
  let two = env.store_blob(vec![2]);
  let four = env.store_blob(vec![4]);
  let vanishes = theorem(
    &env,
    pi(r(0), eq_at(1, r(0), apps(r(2), vec![v(0), arc(Expr::Nat(3))]), r(4))),
    lambda(r(0), apps(reference(5, vec![0]), vec![r(0), r(4)])),
    vec![
      nat.clone(),
      eq.clone(),
      div.clone(),
      two.clone(),
      zero.clone(),
      eq_refl.clone(),
    ],
    vec![one()],
  );
  // `theorem bad : 2 = 0 := @Eq.rec (motive := fun b _ => 2 = b)
  //   (rfl : 2 = div 4 2) (vanishes 4)`: `div 4 2` is `2` natively.
  // refs: Eq, Nat, 2, Nat.zero, Eq.rec, div, 4, Eq.refl, vanishes
  let eq1 = |lhs, rhs| apps(reference(0, vec![1]), vec![r(1), lhs, rhs]);
  let lit = |i: u64| arc(Expr::Nat(i));
  let quotient = apps(r(5), vec![lit(6), lit(2)]);
  let bad = theorem(
    &env,
    eq1(lit(2), r(3)),
    apps(
      reference(4, vec![0, 1]),
      vec![
        r(1),
        quotient.clone(),
        lambda(r(1), lambda(eq1(quotient, v(0)), eq1(lit(2), v(1)))),
        apps(reference(7, vec![1]), vec![r(1), lit(2)]),
        r(3),
        app(r(8), lit(6)),
      ],
    ),
    vec![eq, nat, two, zero, eq_rec, div.clone(), four, eq_refl, vanishes],
    vec![Arc::new(Univ::Zero), one()],
  );

  let mut roles = basis_roles(&env);
  roles.extend(bool_roles(&env));
  let mut evidence = vec![];
  for (role, name, equations) in STRUCTURAL {
    let bound = if role == Role::NatSub { sub.clone() } else { a(name) };
    roles.push((role, bound));
    evidence.push((role, vec![Evidence::DefEq; equations]));
  }
  roles.push((Role::NatDiv, div));
  evidence.push((
    Role::NatDiv,
    [recursive, below, by_zero].into_iter().map(Evidence::Proof).collect(),
  ));
  let roles = with_prelude(&env, roles);
  bind_with_evidence(&mut env, roles, evidence);
  let source = ArtifactSource::snapshot(&env).unwrap();
  let refused = source.admission().refused();
  assert!(refused.is_empty(), "{refused:?}");
  assert!(source.is_admitted(Role::NatDiv));

  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source.clone()));
  checker.check_const(&bad).unwrap();
  assert!(checker.check_const(&zero_is_one).is_err());

  let work = build_artifact_work(&source).unwrap();
  for dependencies in [true, false] {
    let selected =
      verdict_work(&source, &work, std::slice::from_ref(&bad), dependencies)
        .unwrap();
    assert!(selected.iter().any(|item| item.primary() == &bad));
    let failed: Vec<&Address> = selected
      .iter()
      .map(|item| item.primary())
      .filter(|primary| checker.check_const(primary).is_err())
      .collect();
    assert_eq!(failed, [&zero_is_one], "dependencies: {dependencies}");
  }
}

/// `roles` with every prelude role it lacks bound to the compiled records.
fn with_prelude(
  env: &Env,
  mut roles: Vec<(Role, Address)>,
) -> Vec<(Role, Address)> {
  for role in PRELUDE {
    if !roles.iter().any(|(bound, _)| *bound == role) {
      roles.push((role, address_of(env, role.lean_name())));
    }
  }
  roles
}

fn declare(
  env: &Env,
  kind: DefKind,
  safety: DefinitionSafety,
  typ: Arc<Expr>,
  value: Arc<Expr>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Address {
  store(
    env,
    ConstantInfo::Defn(Definition { kind, safety, lvls: 0, typ, value }),
    refs,
    univs,
  )
}

#[test]
fn a_bound_artifact_follows_the_safety_tier() {
  let mut env = loaded();
  let nat = address_of(&env, "Nat");
  let zero_blob = env.store_blob(vec![]);
  let nat_t = || reference(0, vec![]);
  let zero_of = |safety| {
    declare(
      &env,
      DefKind::Definition,
      safety,
      nat_t(),
      arc(Expr::Nat(1)),
      vec![nat.clone(), zero_blob.clone()],
      vec![],
    )
  };
  // `partial def p : Nat := 0` and `unsafe def u : Nat := 0`.
  let p = zero_of(DefinitionSafety::Partial);
  let u = zero_of(DefinitionSafety::Unsafe);
  // `def v : @Eq.{1} Nat c 0 := @Eq.refl.{1} Nat 0` at `v`'s safety, which
  // needs `c` unfolded.
  let one = Arc::new(Univ::Succ(Arc::new(Univ::Zero)));
  let needs_unfolded = |c: &Address, safety| {
    declare(
      &env,
      DefKind::Definition,
      safety,
      app(
        app(
          app(reference(0, vec![0]), reference(2, vec![])),
          reference(3, vec![]),
        ),
        arc(Expr::Nat(4)),
      ),
      app(app(reference(1, vec![0]), reference(2, vec![])), arc(Expr::Nat(4))),
      vec![
        address_of(&env, "Eq"),
        address_of(&env, "Eq.refl"),
        nat.clone(),
        c.clone(),
        zero_blob.clone(),
      ],
      vec![one.clone()],
    )
  };
  let unfolds_p = needs_unfolded(&p, DefinitionSafety::Partial);
  let unfolds_u = needs_unfolded(&u, DefinitionSafety::Unsafe);
  // `unsafe opaque o : Nat := u`: an opaque is checked as safe.
  let opaque = declare(
    &env,
    DefKind::Opaque,
    DefinitionSafety::Unsafe,
    nat_t(),
    reference(1, vec![]),
    vec![nat.clone(), u.clone()],
    vec![],
  );
  // A safe axiom whose type mentions `u`.
  let mentions_u = axiom(
    &env,
    0,
    pi(nat_t(), app(reference(2, vec![]), reference(1, vec![]))),
    vec![nat.clone(), u.clone(), opaque.clone()],
    vec![],
  );

  // Unbound, the kernel follows Lean's: partial and unsafe definitions
  // unfold, and the fence covers definitions only.
  let unbound = ArtifactSource::snapshot(&env).unwrap();
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(unbound));
  checker.check_const(&unfolds_p).unwrap();
  checker.check_const(&unfolds_u).unwrap();
  checker.check_const(&opaque).unwrap();

  let roles = with_prelude(&env, vec![]);
  bind(&mut env, roles);
  let source = ArtifactSource::snapshot(&env).unwrap();
  assert!(source.in_safety_tier(&p) && source.in_safety_tier(&u));
  assert!(!source.in_safety_tier(&address_of(&env, "Nat.add")));
  let mut checker = ArtifactChecker::<Anon>::from_source(Ok(source));
  checker.check_const(&p).unwrap();
  // Partial definitions stay opaque; unsafe ones unfold, as in Lean.
  assert!(checker.check_const(&unfolds_p).is_err());
  checker.check_const(&unfolds_u).unwrap();
  let error = checker.check_const(&opaque).unwrap_err();
  assert!(
    format!("{error}").contains("references unsafe definition"),
    "{error}"
  );
  let error = checker.check_const(&mentions_u).unwrap_err();
  assert!(
    format!("{error}").contains("references unsafe definition"),
    "{error}"
  );
}
