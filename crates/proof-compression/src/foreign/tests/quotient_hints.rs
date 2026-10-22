use super::*;
use quotient::QuotientHint;

fn reference(
  coefficients: [i128; 5],
  offset: &BigInt,
  values: &[Scalar],
) -> Result<Scalar, String> {
  let [a, b, c] = [integer(values[0]), integer(values[1]), integer(values[2])];
  let [qm, qa, qb, qc, k] = coefficients;
  let sum = qm * &a * &b + qa * a + qb * b + qc * c + k + offset;
  if &sum % P != BigInt::from(0) {
    return Err("invalid Goldilocks gate".into());
  }
  Ok(scalar(&(sum / P)))
}

fn offset(coefficients: [i128; 5]) -> BigInt {
  let (low, _) = interval(coefficients, [P - 1; 3]);
  if low < BigInt::from(0) { ((-low + P - 1) / P) * P } else { BigInt::from(0) }
}

fn goldilocks(value: i128) -> Val {
  let magnitude = Val::from_u64(u64::try_from(value.unsigned_abs()).unwrap());
  if value < 0 { -magnitude } else { magnitude }
}

fn cases(count: usize) -> Vec<([i128; 5], [Scalar; 3])> {
  let mut state = 0xda45_83f7_91a2_b603u64;
  let mut next = || {
    state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
    state
  };
  (0..count)
    .map(|i| {
      let mut coefficients =
        std::array::from_fn(|_| signed(Val::from_u64(next())));
      coefficients[3] = -1;
      if i < 8 {
        coefficients = [
          [-i128::from(P / 2), -1, 0, 1, i128::from(P / 2)][i % 5],
          i128::from(P / 2),
          -i128::from(P / 2),
          -1,
          i128::from(P / 2),
        ];
      }
      let [a, b] = if i < 8 {
        [Val::from_u64([0, 1, P - 1, 1 << 63][i % 4]), Val::from_u64(P - 1)]
      } else {
        [Val::from_u64(next()), Val::from_u64(next())]
      };
      let [qm, qa, qb, _, k] = coefficients.map(goldilocks);
      let c = qm * a * b + qa * a + qb * b + k;
      (coefficients, [a, b, c].map(|v| Scalar::from_u64(v.as_canonical_u64())))
    })
    .collect()
}

#[test]
fn bounded_quotient_hints_match_integer_division_and_reject_residuals() {
  for (coefficients, values) in cases(2048) {
    let offset = offset(coefficients);
    let hint = QuotientHint::new(coefficients, &offset);
    let expected = reference(coefficients, &offset, &values).unwrap();
    assert_eq!(hint.evaluate(&values), Ok(expected));
    let mut invalid = values;
    invalid[2] += Scalar::ONE;
    assert!(reference(coefficients, &offset, &invalid).is_err());
    assert_eq!(
      hint.evaluate(&invalid),
      reference(coefficients, &offset, &invalid)
    );
  }
}

#[test]
fn bounded_quotient_hints_preserve_negative_and_large_input_behavior() {
  let inputs = [
    [Scalar::from_u64(P), Scalar::ONE, Scalar::ZERO],
    [Scalar::from_u64(u64::MAX); 3],
    [Scalar::from_limbs_le([0, 1, 0, 0]), Scalar::from_u64(P), Scalar::ONE],
    [
      Scalar::from_limbs_le([0, 0, 0, 1 << 6]),
      Scalar::from_u64(P),
      Scalar::ZERO,
    ],
    [Scalar::NEG_ONE, Scalar::from_u64(P), Scalar::ZERO],
  ];
  for coefficients in [
    [-1, 0, 0, 0, 0],
    [1, 0, 0, -1, 0],
    [0, -1, 0, 0, 0],
    [i128::from(P / 2), -i128::from(P / 2), i128::from(P / 2), -1, 7],
  ] {
    for offset in [BigInt::from(0), offset(coefficients)] {
      let hint = QuotientHint::new(coefficients, &offset);
      for values in inputs {
        assert_eq!(
          hint.evaluate(&values),
          reference(coefficients, &offset, &values)
        );
      }
    }
  }
  let negative = QuotientHint::new([-1, 0, 0, 0, 0], &BigInt::from(0));
  assert_eq!(negative.evaluate(&inputs[0]), Ok(Scalar::NEG_ONE));

  let offset = (((BigInt::from(1u8) << 193usize) - 1u8) / P) * P;
  for coefficient in [-i128::from(P / 2), i128::from(P / 2)] {
    let coefficients = [coefficient; 5];
    let coefficients =
      [coefficients[0], coefficients[1], coefficients[2], coefficients[3], 0];
    let hint = QuotientHint::new(coefficients, &offset);
    let divisible = [Scalar::from_u64(P); 3];
    assert_eq!(
      hint.evaluate(&divisible),
      Ok(reference(coefficients, &offset, &divisible).unwrap())
    );
    assert_eq!(
      hint.evaluate(&inputs[1]),
      reference(coefficients, &offset, &inputs[1])
    );
  }
}

fn proof_fixture(bounded: bool) -> (Circuit<Scalar>, Assignment<Scalar>) {
  let mut b = CircuitBuilder::<Scalar>::new();
  let table =
    b.fixed_table("limbs", (0..16).map(|n| vec![Scalar::from_u8(n)]).collect());
  let inputs = [b.input("a"), b.input("b"), b.input("c")];
  let coefficients = [1, 0, 0, -1, 0];
  let offset = BigInt::from(P);
  let quotient = if bounded {
    let hint = QuotientHint::new(coefficients, &offset);
    b.hint("quotient", &inputs, move |v| hint.evaluate(v))
  } else {
    b.hint("quotient", &inputs, move |v| reference(coefficients, &offset, v))
  };
  range(&mut b, table, quotient, 64);
  let product = b.mul(inputs[0], inputs[1]);
  let residual = b.linear_combination(
    &[
      (Scalar::ONE, product),
      (-Scalar::ONE, inputs[2]),
      (-Scalar::from_u64(P), quotient),
    ],
    Scalar::from_u64(P),
  );
  let zero = b.constant(Scalar::ZERO);
  b.assert_equal(residual, zero);
  b.expose_public(inputs[2]);
  let circuit = b.finish();
  let mut witness = circuit.witness();
  for (input, value) in inputs.into_iter().zip([P - 1, 2, P - 2]) {
    witness.set(input, Scalar::from_u64(value)).unwrap();
  }
  let assignment = witness.generate().unwrap();
  (circuit, assignment)
}

#[test]
fn bounded_quotient_hints_preserve_assignment_constraints_and_kzg_bytes() {
  use crate::kzg::{KzgConfig, Srs, compact::FixedProofCodec};
  use multi_stark::system::{System, SystemWitness};
  use std::sync::Arc;
  let fixtures = [proof_fixture(false), proof_fixture(true)];
  assert_eq!(fixtures[0].0.stats(), fixtures[1].0.stats());
  assert_eq!(
    fixtures[0].1.values(fixtures[0].0.id()).unwrap(),
    fixtures[1].1.values(fixtures[1].0.id()).unwrap()
  );
  for (reference, bounded) in
    fixtures[0].0.gates().iter().zip(fixtures[1].0.gates())
  {
    assert_eq!(
      reference.wires.map(|v| v.index()),
      bounded.wires.map(|v| v.index())
    );
    assert_eq!(reference.coefficients, bounded.coefficients);
  }
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(128, b"quotient-hint-parity")),
    4,
  );
  let mut bytes = Vec::new();
  for (circuit, assignment) in fixtures {
    let compiled = circuit.lower_to_multi_stark(Scalar::from_u8(78)).unwrap();
    let traces = compiled.traces(&assignment).unwrap();
    let claims = compiled.claims(assignment.public_values()).unwrap();
    let (system, key) = System::new(config.clone(), compiled.circuit_inputs());
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(traces, &system),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();
    bytes.push(
      FixedProofCodec::new(&system, &proof.log_degrees)
        .unwrap()
        .encode(&proof)
        .unwrap(),
    );
  }
  assert_eq!(bytes[0], bytes[1]);
}
