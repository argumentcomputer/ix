//! Group admission of bound roles, on the compiler's own basis blocks.

use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, Name};
use ix_kernel::artifact_checker::ArtifactChecker;
use ix_kernel::mode::Anon;
use ix_kernel::role_admission::ArtifactSource;
use ixon::constant::{Constant, ConstantInfo, DefKind, Definition};
use ixon::env::{Env, RoleBinding};
use ixon::expr::Expr;
use ixon::role_table::{Role, RoleTable};

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
