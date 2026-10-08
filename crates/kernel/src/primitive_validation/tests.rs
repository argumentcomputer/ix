use super::*;
use crate::constant::RecRule;
use crate::expr::ExprData;
use crate::mode::Anon;
use crate::primitive::{PrimAddrs, Primitives};
use ix_common::env::ReducibilityHints;

type E = KExpr<Anon>;
fn var(n: u64) -> E {
  E::var(n, ())
}
fn lam(ty: E, body: E) -> E {
  E::lam((), (), ty, body)
}
fn apps(mut f: E, args: &[E]) -> E {
  for a in args {
    f = E::app(f, a.clone());
  }
  f
}
fn lit(n: u64) -> E {
  let n = bignat::Nat::from(n);
  let a = Address::hash(&n.to_le_bytes());
  E::nat(n, a)
}
fn str_lit(s: &str) -> E {
  E::str(s.to_string(), Address::hash(s.as_bytes()))
}
fn id(name: &str) -> KId<Anon> {
  KId::new(Address::hash(name.as_bytes()), ())
}
fn definition(env: &mut KEnv<Anon>, id: &KId<Anon>, ty: E, val: E) {
  env.insert(
    id.clone(),
    KConst::Defn {
      name: (),
      level_params: (),
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Regular(1),
      lvls: 0,
      ty,
      val,
      lean_all: (),
      block: id.clone(),
    },
  );
}
fn axiom(env: &mut KEnv<Anon>, id: &KId<Anon>, lvls: u64, ty: E) {
  env.insert(
    id.clone(),
    KConst::Axio { name: (), level_params: (), is_unsafe: false, lvls, ty },
  );
}

fn fixture() -> (KEnv<Anon>, PrimAddrs) {
  let mut a = PrimAddrs::new();
  a.nat = id("test Nat").addr;
  a.nat_zero = id("test Nat.zero").addr;
  a.nat_succ = id("test Nat.succ").addr;
  a.nat_rec = id("test Nat.rec").addr;
  a.nat_add = id("test addition").addr;
  a.nat_mul = id("test multiplication").addr;
  let mut env = KEnv::new();
  let p = Primitives::from_env_with(&env, &a);
  let nat = cnst(&p.nat);
  let zero = cnst(&p.nat_zero);
  let succ = cnst(&p.nat_succ);
  env.insert(
    p.nat.clone(),
    KConst::Indc {
      name: (),
      level_params: (),
      lvls: 0,
      params: 0,
      indices: 0,
      is_unsafe: false,
      block: p.nat.clone(),
      member_idx: 0,
      ty: E::sort(KUniv::succ(KUniv::zero())),
      ctors: vec![p.nat_zero.clone(), p.nat_succ.clone()],
      lean_all: (),
    },
  );
  for (id, cidx, fields, ty) in [
    (p.nat_zero.clone(), 0, 0, nat.clone()),
    (p.nat_succ.clone(), 1, 1, arrow(nat.clone(), nat.clone())),
  ] {
    env.insert(
      id,
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: p.nat.clone(),
        cidx,
        params: 0,
        fields,
        ty,
      },
    );
  }
  let u = KUniv::param(0, ());
  let motive = arrow(nat.clone(), E::sort(u.clone()));
  let minor0 = E::app(var(0), zero.clone());
  let minor1 = arrow(
    nat.clone(),
    arrow(E::app(var(2), var(0)), E::app(var(3), E::app(succ.clone(), var(1)))),
  );
  let rec_ty = arrow(
    motive.clone(),
    arrow(
      minor0.clone(),
      arrow(minor1.clone(), arrow(nat.clone(), E::app(var(3), var(0)))),
    ),
  );
  let rec = E::cnst(p.nat_rec.clone(), Box::new([u]));
  let ih = apps(rec, &[var(3), var(2), var(1), var(0)]);
  env.insert(
    p.nat_rec.clone(),
    KConst::Recr {
      name: (),
      level_params: (),
      k: false,
      is_unsafe: false,
      lvls: 1,
      params: 0,
      indices: 0,
      motives: 1,
      minors: 2,
      block: p.nat.clone(),
      member_idx: 0,
      ty: rec_ty,
      rules: vec![
        RecRule {
          ctor: (),
          fields: 0,
          rhs: lam(
            motive.clone(),
            lam(minor0.clone(), lam(minor1.clone(), var(1))),
          ),
        },
        RecRule {
          ctor: (),
          fields: 1,
          rhs: lam(
            motive,
            lam(
              minor0,
              lam(minor1, lam(nat.clone(), apps(var(1), &[var(0), ih]))),
            ),
          ),
        },
      ],
      lean_all: (),
    },
  );
  let rec = E::cnst(p.nat_rec.clone(), Box::new([KUniv::succ(KUniv::zero())]));
  let step_add = lam(nat.clone(), lam(nat.clone(), E::app(succ, var(0))));
  let add = lam(
    nat.clone(),
    lam(
      nat.clone(),
      apps(
        rec.clone(),
        &[lam(nat.clone(), nat.clone()), var(1), step_add, var(0)],
      ),
    ),
  );
  let binary = arrow(nat.clone(), arrow(nat.clone(), nat.clone()));
  definition(&mut env, &p.nat_add, binary.clone(), add);
  let step_mul = lam(
    nat.clone(),
    lam(nat.clone(), apps(cnst(&p.nat_add), &[var(0), var(3)])),
  );
  let mul = lam(
    nat.clone(),
    lam(
      nat.clone(),
      apps(rec, &[lam(nat.clone(), nat), zero, step_mul, var(0)]),
    ),
  );
  definition(&mut env, &p.nat_mul, binary, mul);
  (env, a)
}
fn bind(env: &mut KEnv<Anon>, a: &PrimAddrs) {
  let p = Primitives::from_env_with(env, a);
  assert!(!p.trusted);
  assert!(env.set_prims(p).is_ok());
}

#[test]
fn admits_new_addresses_by_equations_and_caches_evidence() {
  let (mut env, a) = fixture();
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert!(tc.admit_nat_operation(&a.nat_add));
  assert!(tc.admit_nat_operation(&a.nat_mul));
  let expr = apps(cnst(&tc.prims.nat_mul), &[lit(200), lit(300)]);
  assert!(tc.is_def_eq(&expr, &lit(60_000)).unwrap());
  let cached = tc.env.primitive_admission.len();
  tc.rec_fuel = 0;
  assert!(tc.admit_nat_operation(&a.nat_mul));
  assert_eq!(tc.env.primitive_admission.len(), cached);
}

#[test]
fn swapped_add_mul_cannot_certify_themselves_or_change_arithmetic() {
  let (mut env, mut a) = fixture();
  let actual_mul = a.nat_mul.clone();
  std::mem::swap(&mut a.nat_add, &mut a.nat_mul);
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert!(!tc.admit_nat_operation(&a.nat_add));
  assert!(!tc.admit_nat_operation(&a.nat_mul));
  let expr = apps(cnst(&KId::new(actual_mul, ())), &[lit(2), lit(3)]);
  assert!(tc.is_def_eq(&expr, &lit(6)).unwrap());
  assert!(!tc.is_def_eq(&expr, &lit(5)).unwrap());
}

#[test]
fn matching_signature_is_insufficient_and_offsets_use_ordinary_reduction() {
  let (mut env, a) = fixture();
  let p = Primitives::from_env_with(&env, &a);
  let nat = cnst(&p.nat);
  definition(
    &mut env,
    &p.nat_add,
    arrow(nat.clone(), arrow(nat.clone(), nat.clone())),
    lam(nat.clone(), lam(nat.clone(), var(1))),
  );
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert!(!tc.admit_nat_operation(&a.nat_add));
  tc.push_local(nat);
  let expr = apps(cnst(&p.nat_add), &[var(0), lit(7)]);
  assert!(tc.is_def_eq(&expr, &var(0)).unwrap());
  assert!(!tc.is_def_eq(&expr, &E::app(cnst(&p.nat_succ), var(0))).unwrap());
}

#[test]
fn invalid_nat_basis_cannot_create_literal_inhabitants() {
  let (mut env, mut a) = fixture();
  a.nat = id("empty type").addr;
  axiom(
    &mut env,
    &KId::new(a.nat.clone(), ()),
    0,
    E::sort(KUniv::succ(KUniv::zero())),
  );
  bind(&mut env, &a);
  assert!(TypeChecker::new(&mut env).infer(&lit(0)).is_err());
}

fn string_fixture(env: &mut KEnv<Anon>, a: &mut PrimAddrs) {
  // Distinct interfaces can implement the expansion without sharing Lean's
  // String, Char, or List representations. Their declarations are assumptions
  // here, as they are for an individual environment work item.
  a.string = id("string interface").addr;
  a.char_type = id("character interface").addr;
  a.char_of_nat = id("character construction").addr;
  a.list = id("list interface").addr;
  a.list_nil = id("empty list interface").addr;
  a.list_cons = id("cons interface").addr;
  a.string_of_list = id("string construction").addr;
  let p = Primitives::from_env_with(env, a);
  let sort1 = E::sort(KUniv::succ(KUniv::zero()));
  axiom(env, &p.string, 0, sort1.clone());
  axiom(env, &p.char_type, 0, sort1);
  let sort_u1 = E::sort(KUniv::succ(KUniv::param(0, ())));
  axiom(env, &p.list, 1, arrow(sort_u1.clone(), sort_u1.clone()));
  let list =
    |x| E::app(E::cnst(p.list.clone(), Box::new([KUniv::param(0, ())])), x);
  axiom(env, &p.list_nil, 1, arrow(sort_u1.clone(), list(var(0))));
  axiom(
    env,
    &p.list_cons,
    1,
    arrow(sort_u1, arrow(var(0), arrow(list(var(1)), list(var(2))))),
  );
  axiom(env, &p.char_of_nat, 0, arrow(cnst(&p.nat), cnst(&p.char_type)));
  let list_char = E::app(
    E::cnst(p.list.clone(), Box::new([KUniv::zero()])),
    cnst(&p.char_type),
  );
  axiom(env, &p.string_of_list, 0, arrow(list_char, cnst(&p.string)));
}

#[test]
fn string_literal_uses_a_typed_expansion_under_unseen_bindings() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert_eq!(tc.infer(&str_lit("hé🙂")).unwrap(), cnst(&tc.prims.string));
  let expansion = tc.str_lit_to_constructor("hé🙂");
  assert!(tc.is_def_eq(&str_lit("hé🙂"), &expansion).unwrap());
}

#[test]
fn string_type_substitution_without_compatible_construction_is_rejected() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  a.string = id("another empty type").addr;
  axiom(
    &mut env,
    &KId::new(a.string.clone(), ()),
    0,
    E::sort(KUniv::succ(KUniv::zero())),
  );
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert!(tc.infer(&str_lit("")).is_err());
  assert!(
    tc.infer(&lit(3)).is_ok(),
    "unused invalid String binding cannot invalidate Nat"
  );
}

#[test]
fn wrong_string_append_and_decidable_bindings_do_not_enable_native_rules() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  a.string_append = id("left projection append").addr;
  a.decidable_decide = a.nat_mul.clone();
  let p = Primitives::from_env_with(&env, &a);
  let s = cnst(&p.string);
  definition(
    &mut env,
    &p.string_append,
    arrow(s.clone(), arrow(s.clone(), s.clone())),
    lam(s.clone(), lam(s, var(1))),
  );
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  let expr = apps(cnst(&p.string_append), &[str_lit("a"), str_lit("b")]);
  assert!(tc.is_def_eq(&expr, &str_lit("a")).unwrap());
  assert!(!tc.is_def_eq(&expr, &str_lit("ab")).unwrap());
}

#[test]
fn conflicting_operation_roles_fall_back_without_overlapping_dispatch() {
  let (mut env, mut a) = fixture();
  a.nat_beq = a.nat_add.clone();
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert!(!tc.admit_nat_operation(&a.nat_add));
  let expr = apps(cnst(&tc.prims.nat_add), &[lit(2), lit(3)]);
  assert!(tc.is_def_eq(&expr, &lit(5)).unwrap());
}

#[test]
fn unrelated_binding_changes_reuse_native_nat_capabilities() {
  let mut a = PrimAddrs::new();
  a.string = id("another string layout").addr;
  let mut env = KEnv::<Anon>::new();
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert!(tc.admit_nat_operation(&a.nat_div));
  assert!(tc.admit_nat_operation(&a.nat_mul));
  assert!(tc.env.primitive_admission.is_empty());
  assert!(tc.prims.native.offsets);
  assert!(!tc.prims.native.strings);
}

#[test]
fn string_admission_does_not_inherit_infer_only_argument_skipping() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  let p = Primitives::from_env_with(&env, &a);
  let list_char = E::app(
    E::cnst(p.list.clone(), Box::new([KUniv::zero()])),
    cnst(&p.char_type),
  );
  // The instantiated result has the expected type, but the first argument
  // expects a Nat value rather than a type. Inference-only mode must not
  // bypass this obligation during binding admission.
  axiom(
    &mut env,
    &p.list_cons,
    1,
    arrow(
      cnst(&p.nat),
      arrow(cnst(&p.char_type), arrow(list_char.clone(), list_char)),
    ),
  );
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  tc.infer_only = true;
  assert!(tc.infer(&str_lit("a")).is_err());
}

#[test]
fn admission_is_invalidated_when_environment_declarations_are_replaced() {
  let (mut env, a) = fixture();
  bind(&mut env, &a);
  assert!(TypeChecker::new(&mut env).admit_nat_operation(&a.nat_add));
  let p = env.prims().clone();
  let nat = cnst(&p.nat);
  definition(
    &mut env,
    &p.nat_add,
    arrow(nat.clone(), arrow(nat.clone(), nat.clone())),
    lam(nat.clone(), lam(nat, var(1))),
  );
  assert!(!TypeChecker::new(&mut env).admit_nat_operation(&a.nat_add));
  env.clear();
  assert!(env.primitive_admission.is_empty());
}

#[test]
fn recursive_alias_cannot_supply_its_own_equation_evidence() {
  let (mut env, a) = fixture();
  let p = Primitives::from_env_with(&env, &a);
  let nat = cnst(&p.nat);
  definition(
    &mut env,
    &p.nat_add,
    arrow(nat.clone(), arrow(nat.clone(), nat)),
    cnst(&p.nat_add),
  );
  bind(&mut env, &a);
  assert!(!TypeChecker::new(&mut env).admit_nat_operation(&a.nat_add));
}

#[test]
fn string_construction_may_change_representation_and_need_not_be_injective() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  let p = Primitives::from_env_with(&env, &a);
  let ctor = id("singleton string constructor");
  env.insert(
    p.string.clone(),
    KConst::Indc {
      name: (),
      level_params: (),
      lvls: 0,
      params: 0,
      indices: 0,
      is_unsafe: false,
      block: p.string.clone(),
      member_idx: 0,
      ty: E::sort(KUniv::succ(KUniv::zero())),
      ctors: vec![ctor.clone()],
      lean_all: (),
    },
  );
  env.insert(
    ctor.clone(),
    KConst::Ctor {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 0,
      induct: p.string.clone(),
      cidx: 0,
      params: 0,
      fields: 0,
      ty: cnst(&p.string),
    },
  );
  let list_char = E::app(
    E::cnst(p.list.clone(), Box::new([KUniv::zero()])),
    cnst(&p.char_type),
  );
  definition(
    &mut env,
    &p.string_of_list,
    arrow(list_char.clone(), cnst(&p.string)),
    lam(list_char, cnst(&ctor)),
  );
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  assert_eq!(tc.infer(&str_lit("a")).unwrap(), cnst(&p.string));
  assert!(tc.is_def_eq(&str_lit("a"), &str_lit("b")).unwrap());
}

#[test]
fn typed_interface_admission_accepts_definitionally_equal_signatures() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  let p = Primitives::from_env_with(&env, &a);
  let alias = id("character type alias");
  definition(
    &mut env,
    &alias,
    E::sort(KUniv::succ(KUniv::zero())),
    cnst(&p.char_type),
  );
  axiom(&mut env, &p.char_of_nat, 0, arrow(cnst(&p.nat), cnst(&alias)));
  bind(&mut env, &a);
  assert!(TypeChecker::new(&mut env).infer(&str_lit("a")).is_ok());
}

#[test]
fn circular_literal_support_is_rejected_with_a_bounded_error() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  let p = Primitives::from_env_with(&env, &a);
  axiom(&mut env, &p.char_type, 0, str_lit("type"));
  bind(&mut env, &a);
  let err = TypeChecker::new(&mut env).infer(&str_lit("a")).unwrap_err();
  assert!(format!("{err:?}").contains("circular primitive contract"));
}

#[test]
fn custom_list_bindings_do_not_enable_invalid_string_collapse() {
  let (mut env, mut a) = fixture();
  string_fixture(&mut env, &mut a);
  let p = Primitives::from_env_with(&env, &a);
  let sort1 = E::sort(KUniv::succ(KUniv::zero()));
  let nat = cnst(&p.nat);
  definition(
    &mut env,
    &p.list,
    arrow(sort1.clone(), sort1.clone()),
    lam(sort1.clone(), nat.clone()),
  );
  let mut list_decl = env.get(&p.list).unwrap();
  if let KConst::Defn { lvls, .. } = &mut list_decl {
    *lvls = 1;
  }
  env.insert(p.list.clone(), list_decl);
  axiom(&mut env, &p.list_nil, 1, arrow(sort1.clone(), nat.clone()));
  axiom(
    &mut env,
    &p.list_cons,
    1,
    arrow(sort1, arrow(var(0), arrow(nat.clone(), nat.clone()))),
  );
  bind(&mut env, &a);
  let mut tc = TypeChecker::new(&mut env);
  tc.require_primitive(Rule::String).unwrap();
  let nil_nat =
    E::app(E::cnst(p.list_nil.clone(), Box::new([KUniv::zero()])), nat);
  let term = E::app(cnst(&p.string_of_list), nil_nat);
  assert_eq!(tc.infer(&term).unwrap(), cnst(&p.string));
  assert!(!tc.is_def_eq(&term, &str_lit("")).unwrap());
}

#[test]
#[ignore = "requires IX_TEST_PRIMITIVE_ENV pointing to an exported Lean environment"]
fn exported_lean_profile_admission() {
  let path = std::env::var("IX_TEST_PRIMITIVE_ENV").unwrap();
  let bytes = std::fs::read(&path).unwrap();
  let index = ixon::env::Env::parse_lazy_index(&bytes).unwrap();
  let input = ixon::env::Env::from_lazy_index(&index, &bytes).unwrap();
  let profile = ixon::prim_profile::PrimProfile::from_env(&input).unwrap();
  let a = profile.to_addrs().unwrap();
  let mut env = KEnv::<Anon>::new();
  let p = Primitives::from_env_with(&env, &a);
  assert!(env.set_prims(p).is_ok());
  let mut tc = TypeChecker::new_with_lazy_anon(&mut env, &input);
  tc.require_primitive(Rule::Nat).unwrap();
  tc.require_primitive(Rule::String).unwrap();
  for rule in [
    Rule::Pred,
    Rule::Add,
    Rule::Sub,
    Rule::Mul,
    Rule::Pow,
    Rule::Beq,
    Rule::Ble,
  ] {
    assert!(tc.validate_primitive(rule).unwrap(), "{path}: {rule:?} equations");
  }
  for (addr, x, y, expected) in [(&a.nat_add, 2, 3, 5), (&a.nat_mul, 2, 3, 6)] {
    let expr = apps(cnst(&KId::new(addr.clone(), ())), &[lit(x), lit(y)]);
    assert!(tc.is_def_eq(&expr, &lit(expected)).unwrap());
  }
  assert!(
    matches!(tc.infer(&str_lit("cross-version 🙂")).unwrap().data(), ExprData::Const(id, _, _) if id.addr == a.string)
  );
  let mut swapped = a.clone();
  std::mem::swap(&mut swapped.nat_add, &mut swapped.nat_mul);
  let mut wrong_env = KEnv::new();
  let p = Primitives::from_env_with(&wrong_env, &swapped);
  assert!(wrong_env.set_prims(p).is_ok());
  let mut wrong = TypeChecker::new_with_lazy_anon(&mut wrong_env, &input);
  let mul = apps(cnst(&KId::new(a.nat_mul.clone(), ())), &[lit(2), lit(3)]);
  assert!(wrong.is_def_eq(&mul, &lit(6)).unwrap());
  assert!(!wrong.is_def_eq(&mul, &lit(5)).unwrap());
  eprintln!(
    "{path}: profile {}, literal contracts and Nat equations accepted",
    profile.address().hex()
  );
}
