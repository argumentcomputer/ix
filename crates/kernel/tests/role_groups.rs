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
use ixon::role_table::{Role, RoleTable};
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

fn bind(env: &mut Env, mut bound: Vec<(Role, Address)>) {
  bound.sort_by_key(|(role, _)| role.index());
  let raw =
    RoleTable { version: 2, bound, evidence: vec![] }.to_bytes().unwrap();
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
  let sound = address_of(&env, "Quot.sound");
  let roles = nat_roles(&env);
  bind(&mut env, roles);
  let error = ArtifactChecker::<Anon>::from_source(Ok(
    ArtifactSource::snapshot(&env).unwrap(),
  ))
  .check_const(&sound)
  .unwrap_err();
  assert!(
    format!("{error}").contains("not an admitted quotient primitive"),
    "{error}"
  );
}

// Anchors are specified by type alone, so declarations of the specified
// types serve: `Char : Type := Nat` and axioms for the rest.

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

/// The literal-support anchors; `String.ofList` returns `Char` when
/// `of_list_is_wrong`.
fn literal_anchors(env: &Env, of_list_is_wrong: bool) -> Vec<(Role, Address)> {
  let nat = address_of(env, "Nat");
  let zero = Arc::new(Univ::Zero);
  let one = Arc::new(Univ::Succ(zero.clone()));
  let succ_param = Arc::new(Univ::Succ(Arc::new(Univ::Var(0))));
  let char_t = store(
    env,
    ConstantInfo::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: arc(Expr::Sort(0)),
      value: reference(0, vec![]),
    }),
    vec![nat.clone()],
    vec![one.clone()],
  );
  let string = axiom(env, 0, arc(Expr::Sort(0)), vec![], vec![one.clone()]);
  // `Type u → Type u`; universe 0 is `u + 1`, universe 1 is `u`.
  let list = axiom(
    env,
    1,
    pi(arc(Expr::Sort(0)), arc(Expr::Sort(0))),
    vec![],
    vec![succ_param.clone()],
  );
  let list_u = |arg| app(reference(0, vec![1]), arg);
  let univs = vec![succ_param, Arc::new(Univ::Var(0))];
  let nil = axiom(
    env,
    1,
    pi(arc(Expr::Sort(0)), list_u(arc(Expr::Var(0)))),
    vec![list.clone()],
    univs.clone(),
  );
  let cons = axiom(
    env,
    1,
    pi(
      arc(Expr::Sort(0)),
      pi(
        arc(Expr::Var(0)),
        pi(list_u(arc(Expr::Var(1))), list_u(arc(Expr::Var(2)))),
      ),
    ),
    vec![list.clone()],
    univs,
  );
  let of_nat = axiom(
    env,
    0,
    pi(reference(0, vec![]), reference(1, vec![])),
    vec![nat, char_t.clone()],
    vec![],
  );
  // `List.{0} Char → String` (or `→ Char`).
  let target = if of_list_is_wrong { 1 } else { 2 };
  let of_list = axiom(
    env,
    0,
    pi(
      app(reference(0, vec![0]), reference(1, vec![])),
      reference(target, vec![]),
    ),
    vec![list.clone(), char_t.clone(), string.clone()],
    vec![zero],
  );
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

  // `String.ofList : List Char → Char` is refused.
  let (refused, _) = checked(true, true);
  assert_eq!(refused.len(), 1, "{refused:?}");
  assert_eq!(refused[0].0, Role::StringOfList);
  assert!(refused[0].1.contains("differs from the specification: type"));
}
