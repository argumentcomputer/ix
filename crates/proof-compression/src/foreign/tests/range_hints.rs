use super::*;

fn single_limb_range(
  b: &mut CircuitBuilder<Scalar>,
  table: Table,
  value: Value,
  bits: usize,
) {
  if bits == 0 {
    let zero = b.constant(Scalar::ZERO);
    b.assert_equal(value, zero);
    return;
  }
  if bits == 1 {
    b.assert_bool(value);
    return;
  }
  let mut terms = Vec::new();
  let mut coefficient = Scalar::ONE;
  for i in 0..bits.div_ceil(16) {
    let limb = b.hint("integer limb", &[value], move |v| {
      let words = v[0].canonical_limbs_le();
      Ok(Scalar::from_u64((words[i / 4] >> (16 * (i % 4))) & 0xffff))
    });
    b.lookup(table, &[limb]);
    terms.push((coefficient, limb));
    coefficient *= Scalar::from_u32(1 << 16);
  }
  let packed = b.linear_combination(&terms, Scalar::ZERO);
  b.assert_equal(value, packed);
}

fn fixture(
  bits: &[usize],
  grouped: bool,
  table_size: u32,
) -> (Circuit<Scalar>, Vec<Value>) {
  let mut b = CircuitBuilder::<Scalar>::new();
  let table = b.fixed_table(
    "limbs",
    (0..table_size).map(|v| vec![Scalar::from_u32(v)]).collect(),
  );
  let inputs = bits.iter().map(|_| b.input("integer")).collect::<Vec<_>>();
  for (&bits, &value) in bits.iter().zip(&inputs) {
    if grouped {
      range(&mut b, table, value, bits);
    } else {
      single_limb_range(&mut b, table, value, bits);
    }
    b.expose_public(value);
  }
  (b.finish(), inputs)
}

fn assign(
  circuit: &Circuit<Scalar>,
  inputs: &[Value],
  values: &[Scalar],
) -> Assignment<Scalar> {
  let mut witness = circuit.witness();
  for (&input, &value) in inputs.iter().zip(values) {
    witness.set(input, value).unwrap();
  }
  witness.generate().unwrap()
}

#[test]
fn grouped_range_hints_preserve_wires_constraints_and_boundary_values() {
  let bits = [0, 1, 2, 16, 17, 32, 33, 48, 64, 65, 80, 96, 112, 128, 129, 130];
  let (single, old_inputs) = fixture(&bits, false, 1 << 16);
  let (grouped, new_inputs) = fixture(&bits, true, 1 << 16);
  assert_eq!(
    old_inputs.iter().map(|v| v.index()).collect::<Vec<_>>(),
    new_inputs.iter().map(|v| v.index()).collect::<Vec<_>>()
  );
  let mut expected = single.stats();
  assert!(grouped.stats().hint_calls < expected.hint_calls);
  expected.hint_calls = grouped.stats().hint_calls;
  assert_eq!(grouped.stats(), expected);
  for (old, new) in single.gates().iter().zip(grouped.gates()) {
    assert_eq!(old.wires.map(|v| v.index()), new.wires.map(|v| v.index()));
    assert_eq!(old.coefficients, new.coefficients);
  }
  for (old, new) in single.lookups().iter().zip(grouped.lookups()) {
    assert_eq!(old.table.index(), new.table.index());
    assert_eq!(
      old.values.iter().map(|v| v.index()).collect::<Vec<_>>(),
      new.values.iter().map(|v| v.index()).collect::<Vec<_>>()
    );
  }
  for digit in [0u64, 1, 0x5555, 0xffff] {
    let values = bits.map(|bits| {
      if bits <= 1 {
        return Scalar::from_u64(digit & u64::try_from(bits).unwrap());
      }
      (0..bits.div_ceil(16)).fold(Scalar::ZERO, |value, _| {
        value * Scalar::from_u32(1 << 16) + Scalar::from_u64(digit)
      })
    });
    let old = assign(&single, &old_inputs, &values);
    let new = assign(&grouped, &new_inputs, &values);
    assert_eq!(
      old.values(single.id()).unwrap(),
      new.values(grouped.id()).unwrap()
    );
    assert_eq!(old.public_values(), new.public_values());
  }
}

#[test]
fn grouped_range_hints_still_reject_non_limbs_with_valid_packing() {
  let (circuit, inputs) = fixture(&[32], true, 1 << 16);
  let assignment = assign(&circuit, &inputs, &[Scalar::ZERO]);
  let mut forged = assignment.values(circuit.id()).unwrap().to_vec();
  // The two limb hints directly follow the input; both limbs pack to zero
  // while neither is a table entry.
  let limbs: Vec<_> = circuit
    .value_sources()
    .enumerate()
    .filter_map(|(index, source)| {
      matches!(source, Recipe::Hint).then_some(index)
    })
    .take(2)
    .collect();
  assert_eq!(limbs.len(), 2);
  assert_eq!(limbs[1], limbs[0] + 1);
  forged[limbs[0]] = Scalar::from_u32(1 << 16);
  forged[limbs[1]] = Scalar::NEG_ONE;
  assert_eq!(
    circuit.check_values(&forged),
    Err(WitnessError::LookupMissing { table: "limbs".into() })
  );
}

#[test]
fn grouped_range_hints_preserve_kzg_proof_bytes() {
  use crate::kzg::{KzgConfig, Srs, compact::FixedProofCodec};
  use multi_stark::system::{System, SystemWitness};
  use std::sync::Arc;
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(64, b"range-hint-parity")),
    4,
  );
  let mut proofs = Vec::new();
  for grouped in [false, true] {
    let (circuit, inputs) = fixture(&[17, 32], grouped, 16);
    let assignment = assign(
      &circuit,
      &inputs,
      &[Scalar::from_u32((1 << 16) + 9), Scalar::from_u32((7 << 16) + 3)],
    );
    let compiled = circuit.lower_to_multi_stark(Scalar::from_u8(77)).unwrap();
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
    proofs.push(
      FixedProofCodec::new(&system, &proof.log_degrees)
        .unwrap()
        .encode(&proof)
        .unwrap(),
    );
  }
  assert_eq!(proofs[0], proofs[1]);
}
