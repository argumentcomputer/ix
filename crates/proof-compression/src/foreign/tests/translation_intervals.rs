use super::*;
use ark_ff::BigInt as Limbs;
use interval::GatePlan;

fn reference_plan(coefficients: [i128; 5], bounds: [u64; 3]) -> GatePlan {
  let (low, high) = interval(coefficients, bounds);
  let p = BigInt::from(P);
  if low > -&p && high < p {
    return GatePlan::Direct;
  }
  let shift =
    if low < BigInt::from(0) { (-low + &p - 1) / &p } else { BigInt::from(0) };
  let offset = &shift * &p;
  let max_q: BigInt = (high + &offset) / &p;
  let bits = usize::try_from(max_q.bits()).unwrap();
  let (sign, words) = offset.to_u64_digits();
  assert_ne!(sign, Sign::Minus);
  let mut offset = Limbs::zero();
  offset.0[..words.len()].copy_from_slice(&words);
  GatePlan::Quotient { offset, bits }
}

#[test]
fn fixed_intervals_match_signed_boundaries_and_quotient_bits() {
  let half = i128::from(P / 2);
  for coefficients in [
    [0; 5],
    [0, -1, 0, 0, 0],
    [0, -1, 0, 0, -1],
    [0, 1, 0, 0, 0],
    [0, 1, 0, 0, 1],
    [1, 0, 0, 0, 0],
    [-1, 0, 0, 0, -1],
    [-half, -half, -half, -half, -half],
    [half; 5],
    [half, -half, half, -half, -half],
  ] {
    for bounds in [
      [0; 3],
      [1; 3],
      [P - 2, 1, 0],
      [P - 1; 3],
      [P; 3],
      [P + 1; 3],
      [u64::MAX; 3],
    ] {
      assert_eq!(
        GatePlan::new(coefficients, bounds),
        reference_plan(coefficients, bounds),
        "coefficients={coefficients:?}, bounds={bounds:?}"
      );
    }
  }
  assert_eq!(
    GatePlan::new([0, -1, 0, 0, -1], [P - 1, 0, 0]),
    GatePlan::Quotient { offset: Limbs::from(P), bits: 0 }
  );
  for bit in 1..64 {
    for maximum in [(1u64 << bit) - 1, 1u64 << bit, (1u64 << bit) + 1] {
      let coefficients = [1, 0, 0, 0, 0];
      let bounds = [P, maximum, 0];
      assert_eq!(
        GatePlan::new(coefficients, bounds),
        reference_plan(coefficients, bounds)
      );
    }
  }
  let mut state = 0x5fcd_06a9_8372_b14du64;
  let mut next = || {
    state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
    state
  };
  for _ in 0..16_384 {
    let coefficients = std::array::from_fn(|_| signed(Val::from_u64(next())));
    let bounds = std::array::from_fn(|_| next());
    assert_eq!(
      GatePlan::new(coefficients, bounds),
      reference_plan(coefficients, bounds)
    );
    for coefficient in coefficients {
      assert_eq!(
        signed_scalar(coefficient),
        scalar(&BigInt::from(coefficient))
      );
    }
  }
}

fn fixture(reference: bool, count: usize) -> (Circuit<Scalar>, [Value; 3]) {
  let mut source = CircuitBuilder::<Val>::new();
  let source_wires = [source.input("a"), source.input("b"), source.input("c")];
  let mut builder = CircuitBuilder::<Scalar>::new();
  let table = builder
    .fixed_table("limbs", (0..16).map(|i| vec![Scalar::from_u8(i)]).collect());
  let zero = builder.constant(Scalar::ZERO);
  let values = [builder.input("a"), builder.input("b"), builder.input("c")];
  let wires = [zero, values[0], values[1], values[2]];
  for i in 0..count {
    let coefficients = match i % 6 {
      0 => [1, 0, 0, -1, 0],
      1 => [-1, 1, 0, -1, 0],
      2 => [0, 1, -1, -1, 0],
      3 => [0, 1, 1, -1, 0],
      4 => [i128::from(P / 2), -7, 13, -1, -1],
      _ => [-i128::from(P / 2), 19, -31, -1, 7],
    };
    let coefficients = coefficients.map(|v| {
      let magnitude = Val::from_u64(u64::try_from(v.unsigned_abs()).unwrap());
      if v < 0 { -magnitude } else { magnitude }
    });
    let gate = Gate { wires: source_wires, coefficients };
    if reference {
      constrain_reference(
        &mut builder,
        table,
        &gate,
        &wires,
        &[P - 1; 4],
        false,
      );
    } else {
      constrain_gate(&mut builder, table, &gate, &wires, &[P - 1; 4], false);
    }
  }
  builder.expose_public(values[2]);
  (builder.finish(), values)
}

#[test]
fn fixed_intervals_preserve_constraint_layout() {
  let (expected, _) = fixture(true, 24);
  let (actual, _) = fixture(false, 24);
  assert_eq!(expected.stats(), actual.stats());
  for (a, b) in expected.gates().iter().zip(actual.gates()) {
    assert_eq!(a.wires.map(|v| v.index()), b.wires.map(|v| v.index()));
    assert_eq!(a.coefficients, b.coefficients);
  }
  for (a, b) in expected.lookups().iter().zip(actual.lookups()) {
    assert_eq!(a.table.index(), b.table.index());
    assert_eq!(
      a.values.iter().map(|v| v.index()).collect::<Vec<_>>(),
      b.values.iter().map(|v| v.index()).collect::<Vec<_>>()
    );
  }
  assert!(expected.value_sources().zip(actual.value_sources()).all(
    |(a, b)| { std::mem::discriminant(&a) == std::mem::discriminant(&b) }
  ));
}

#[test]
fn fixed_intervals_preserve_assignment_and_kzg_bytes() {
  use crate::kzg::{KzgConfig, Srs, compact::FixedProofCodec};
  use multi_stark::system::{System, SystemWitness};
  use std::sync::Arc;
  let mut assignments = Vec::new();
  let mut proofs = Vec::new();
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(128, b"interval-plan-parity")),
    4,
  );
  for reference in [true, false] {
    let (circuit, inputs) = fixture(reference, 1);
    let mut witness = circuit.witness();
    for (wire, value) in inputs.into_iter().zip([P - 1, 2, P - 2]) {
      witness.set(wire, Scalar::from_u64(value)).unwrap();
    }
    let assignment = witness.generate().unwrap();
    assignments.push(assignment.values(circuit.id()).unwrap().to_vec());
    let compiled = circuit.lower_to_multi_stark(Scalar::from_u8(87)).unwrap();
    let traces = compiled.traces(&assignment).unwrap();
    let claims = compiled.claims(assignment.public_values()).unwrap();
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let (system, key) = System::new(config.clone(), compiled.circuit_inputs());
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(traces, &system),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();
    proofs.push(
      FixedProofCodec::new(&system, &proof.log_degrees)
        .unwrap()
        .encode(&proof)
        .unwrap(),
    );
  }
  assert_eq!(assignments[0], assignments[1]);
  assert_eq!(proofs[0], proofs[1]);
}

/// The modular gate construction before fixed-width interval planning,
/// kept as the reference for the plan's offsets and quotient bounds.
fn constrain_reference(
  b: &mut CircuitBuilder<Scalar>,
  table: Table,
  gate: &Gate<Val>,
  wires: &[Value],
  bounds: &[u64],
  integer_relation: bool,
) {
  let coefficients = gate.coefficients.map(signed);
  let values = gate.wires.map(|v| wires[v.index()]);
  if integer_relation
    || boolean_gate(gate)
    || small_interval(coefficients, gate.wires.map(|v| bounds[v.index()]))
      .is_some_and(|(low, high)| low > -i128::from(P) && high < i128::from(P))
  {
    b.constrain_gate(values, coefficients.map(signed_scalar));
    return;
  }
  let (low, high) =
    interval(coefficients, gate.wires.map(|v| bounds[v.index()]));
  let p = BigInt::from(P);
  if low > -&p && high < p {
    b.constrain_gate(values, coefficients.map(|c| scalar(&BigInt::from(c))));
    return;
  }
  let shift =
    if low < BigInt::from(0) { (-low + &p - 1) / &p } else { BigInt::from(0) };
  let offset = &shift * &p;
  let max_q = (high + &offset) / &p;
  let bits = usize::try_from(max_q.bits()).expect("quotient fits usize");
  assert!(bits <= 130, "Goldilocks gate quotient bound");
  let hint = quotient::QuotientHint::new(coefficients, &offset);
  let quotient =
    b.hint("Goldilocks quotient", &values, move |v| hint.evaluate(v));
  range(b, table, quotient, bits);
  let [qm, qa, qb, qc, k] = coefficients.map(|c| scalar(&BigInt::from(c)));
  let product = b.mul(values[0], values[1]);
  let residual = b.linear_combination(
    &[
      (qm, product),
      (qa, values[0]),
      (qb, values[1]),
      (qc, values[2]),
      (-Scalar::from_u64(P), quotient),
    ],
    k + scalar(&offset),
  );
  let zero = b.constant(Scalar::ZERO);
  b.assert_equal(residual, zero);
}
