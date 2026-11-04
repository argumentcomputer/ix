//! Constructed native results against a validated, generated role binding.

use super::*;
use crate::env::KEnv;
use crate::ingress::IxonIngressLookups;
use crate::mode::Anon;
use crate::primitive_context::PrimitiveContext;
use crate::role_admission::ArtifactSource;

type E = KExpr<Anon>;

fn call_at(
  source: &ArtifactSource,
  role: Role,
  levels: Vec<KUniv<Anon>>,
  args: Vec<E>,
) -> E {
  let head = E::cnst(
    KId::new(source.required_role(role).unwrap().clone(), ()),
    levels.into(),
  );
  args.into_iter().fold(head, E::app)
}

fn call(source: &ArtifactSource, role: Role, args: Vec<E>) -> E {
  call_at(source, role, vec![], args)
}

fn number(value: u64) -> E {
  let value = Nat::from(value);
  let key = Address::hash(&value.to_le_bytes());
  E::nat(value, key)
}

fn string(value: &str) -> E {
  E::str(value.to_owned(), Address::hash(value.as_bytes()))
}

fn expect_number(value: &E, expected: u64) {
  let ExprData::Nat(actual, _, _) = value.data() else {
    panic!("expected a native Nat literal");
  };
  assert_eq!(actual.to_u64(), Some(expected));
}

fn same_type(checker: &mut TypeChecker<'_, Anon>, before: &E, after: &E) {
  let before = checker.infer(before).unwrap();
  let after = checker.infer(after).unwrap();
  assert!(checker.is_def_eq(&before, &after).unwrap());
}

fn check_bound_reductions() {
  let path = std::env::var("IX_ROLE_ARTIFACT")
    .expect("IX_ROLE_ARTIFACT must name the validated all-role artifact");
  let bytes = std::fs::read(path).unwrap();
  let mut input = bytes.as_slice();
  let env = ixon::env::Env::get(&mut input).unwrap();
  assert!(input.is_empty());
  let source = ArtifactSource::prepare(env).unwrap();
  assert_eq!(source.admission().admitted_count(), Role::ALL.len());
  assert!(source.admission().refused().is_empty());
  let context =
    PrimitiveContext::bound(source.clone(), source.admission().roles(), |_| {
      None
    });
  let lookups = IxonIngressLookups::default();
  let mut env = KEnv::<Anon>::new();
  let mut checker =
    TypeChecker::for_artifact_anon(&mut env, &source, &lookups, context);
  assert!(checker.takes_extra(ExtraReduction::String));
  assert!(checker.takes_extra(ExtraReduction::BitVec));
  for disabled in [
    ExtraReduction::Decidable,
    ExtraReduction::NatOffsets,
    ExtraReduction::NatRecLinear,
  ] {
    assert!(!checker.takes_extra(disabled));
  }

  let append =
    call(&source, Role::StringAppend, vec![string("aλ"), string("é🌍")]);
  let appended = checker.try_reduce_string(&append).unwrap().unwrap();
  let ExprData::Str(value, _, _) = appended.data() else {
    panic!("append did not produce a literal")
  };
  assert_eq!(value, "aλé🌍");
  same_type(&mut checker, &append, &appended);

  let size = call(&source, Role::StringUtf8ByteSize, vec![appended]);
  let sized = checker.try_reduce_string(&size).unwrap().unwrap();
  expect_number(&sized, 9);
  same_type(&mut checker, &size, &sized);
  for (value, expected) in [("aλ", 'λ'), ("", 'A')] {
    let back = call(&source, Role::StringBack, vec![string(value)]);
    let result = checker.try_reduce_string(&back).unwrap().unwrap();
    assert_eq!(checker.char_lit_value(&result), Some(expected));
    same_type(&mut checker, &back, &result);
  }
  let bytes = call(&source, Role::StringToByteArray, vec![string("")]);
  let result = checker.try_reduce_string(&bytes).unwrap().unwrap();
  let ExprData::Const(id, _, _) = result.data() else {
    panic!("expected ByteArray.empty")
  };
  assert_eq!(&id.addr, source.required_role(Role::ByteArrayEmpty).unwrap());
  same_type(&mut checker, &bytes, &result);
  let nonempty = call(&source, Role::StringToByteArray, vec![string("x")]);
  assert!(checker.try_reduce_string(&nonempty).unwrap().is_none());

  let equal = call(&source, Role::StringDecEq, vec![string("λ"), string("λ")]);
  let result = checker.try_reduce_string(&equal).unwrap().unwrap();
  let (head, arguments) = collect_app_spine(&result);
  let ExprData::Const(id, _, _) = head.data() else {
    panic!("expected a Decidable constructor")
  };
  assert_eq!(&id.addr, source.required_role(Role::DecidableIsTrue).unwrap());
  assert_eq!(arguments.len(), 2);
  same_type(&mut checker, &equal, &result);
  let unequal =
    call(&source, Role::StringDecEq, vec![string("x"), string("y")]);
  assert!(checker.try_reduce_string(&unequal).unwrap().is_none());

  let char_type = call(&source, Role::Char, vec![]);
  let nil = call_at(
    &source,
    Role::ListNil,
    vec![KUniv::zero()],
    vec![char_type.clone()],
  );
  let chars = call_at(
    &source,
    Role::ListCons,
    vec![KUniv::zero()],
    vec![
      char_type,
      call(&source, Role::CharOfNat, vec![number(u64::from(u32::from('λ')))]),
      nil,
    ],
  );
  let from_list = call(&source, Role::StringOfList, vec![chars]);
  let result = checker.try_reduce_string(&from_list).unwrap().unwrap();
  let ExprData::Str(value, _, _) = result.data() else {
    panic!("expected constructor collapse to a literal")
  };
  assert_eq!(value, "λ");
  same_type(&mut checker, &from_list, &result);

  let of_nat =
    |width, n| call(&source, Role::BitVecOfNat, vec![number(width), number(n)]);
  for (width, n, expected) in [(4, 19, 3), (0, 19, 0)] {
    let term =
      call(&source, Role::BitVecToNat, vec![number(width), of_nat(width, n)]);
    let result = checker.try_reduce_bitvec(&term).unwrap().unwrap();
    expect_number(&result, expected);
    same_type(&mut checker, &term, &result);
  }
  let width = call(&source, Role::NatAdd, vec![number(1), number(3)]);
  let term = call(&source, Role::BitVecToNat, vec![width, of_nat(4, 19)]);
  expect_number(&checker.try_reduce_bitvec(&term).unwrap().unwrap(), 3);
  for (left, expected) in [(19, Role::BoolTrue), (5, Role::BoolFalse)] {
    let term = call(
      &source,
      Role::BitVecUlt,
      vec![number(4), of_nat(4, left), of_nat(4, 4)],
    );
    let result = checker.try_reduce_bitvec(&term).unwrap().unwrap();
    let ExprData::Const(id, _, _) = result.data() else {
      panic!("expected Bool result")
    };
    assert_eq!(&id.addr, source.required_role(expected).unwrap());
    same_type(&mut checker, &term, &result);
  }
  for term in [
    call(&source, Role::BitVecToNat, vec![number(3), of_nat(4, 19)]),
    call(&source, Role::BitVecUlt, vec![number(3), of_nat(4, 1), of_nat(4, 2)]),
    call(&source, Role::BitVecToNat, vec![number(4), E::var(0, ())]),
    call(
      &source,
      Role::BitVecUlt,
      vec![number(4), E::var(0, ()), of_nat(4, 2)],
    ),
  ] {
    assert!(checker.try_reduce_bitvec(&term).unwrap().is_none());
  }

  // A candidate table may know a head before its group is admitted. Another
  // admitted head in the same family must not authorize the candidate's rule.
  for role in [Role::StringAppend, Role::BitVecUlt] {
    let admitted = source
      .admission()
      .roles()
      .keys()
      .copied()
      .filter(|candidate| *candidate != role)
      .collect();
    let context = PrimitiveContext::bound_with_table(
      source.clone(),
      source.admission().roles(),
      admitted,
      |_| None,
    );
    let mut env = KEnv::<Anon>::new();
    let mut candidate =
      TypeChecker::for_artifact_anon(&mut env, &source, &lookups, context);
    if role == Role::StringAppend {
      assert!(candidate.try_reduce_string(&append).unwrap().is_none());
    } else {
      let term =
        call(&source, role, vec![number(4), of_nat(4, 1), of_nat(4, 2)]);
      assert!(candidate.try_reduce_bitvec(&term).unwrap().is_none());
    }
  }
}

#[test]
#[ignore = "requires IX_ROLE_ARTIFACT from the validated Lean generator"]
fn admitted_bound_reducers_return_typed_results_only_for_specified_inputs() {
  std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(check_bound_reductions)
    .unwrap()
    .join()
    .unwrap();
}
