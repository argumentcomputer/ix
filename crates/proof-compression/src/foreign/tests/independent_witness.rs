use super::*;

struct Fixture {
  circuit: Circuit<Val>,
  assignment: Assignment<Val>,
}

impl Fixture {
  fn new(rounds: usize) -> Self {
    let mut b = CircuitBuilder::<Val>::new();
    let bytes = b
      .fixed_table("byte", (0..=255).map(|i| vec![Val::from_u16(i)]).collect());
    let mut inputs = Vec::new();
    let boundary = [0, 1, P - 1, u64::from(u32::MAX), 1 << 32, P - (1 << 32)];
    for i in 0..rounds {
      let constant = b.constant(Val::from_usize(19 + i % 31));
      let wide = b.input("wide");
      let factor = b.input("factor");
      let byte = b.input("byte");
      let bit = b.input("bit");
      inputs.extend([
        (wide, Val::from_u64(boundary[i % boundary.len()])),
        (factor, Val::from_u64(P - 3 - u64::try_from(i % 127).unwrap())),
        (byte, Val::from_usize(i % 256)),
        (bit, Val::from_usize(i % 2)),
      ]);
      b.lookup(bytes, &[byte]);
      let bit = b.assert_bool(bit);
      let product = b.mul(wide, factor);
      let shifted = b.add(product, constant);
      let chosen = b.select(bit, shifted, byte);
      let copies = [
        b.hint("copy", &[chosen], |values| Ok(values[0])),
        b.hint("copy", &[chosen], |values| Ok(values[0])),
      ];
      for copy in copies {
        b.assert_equal(copy, chosen);
      }
      b.constant(Val::from_usize(333 + i % 37));
      if i + 1 == rounds {
        b.expose_public(copies[0]);
      }
    }
    let circuit = b.finish();
    let mut witness = circuit.witness();
    for (input, value) in inputs {
      witness.set(input, value).unwrap();
    }
    let assignment = witness.generate().unwrap();
    Self { circuit, assignment }
  }

  fn translate(&self, chunk_size: usize) -> GoldilocksCircuit {
    let mut b = CircuitBuilder::new();
    let inputs = GoldilocksCircuit::translate_with_chunk_size(
      &self.circuit,
      &mut b,
      false,
      chunk_size,
    );
    GoldilocksCircuit { circuit: b.finish(), inputs }
  }

  fn witness<'a>(
    &self,
    translated: &'a GoldilocksCircuit,
  ) -> Witness<'a, Scalar> {
    let mut witness = translated.circuit.witness();
    translated.assign(&self.assignment, &mut witness).unwrap();
    witness
  }
}

fn assert_relation(left: &Circuit<Scalar>, right: &Circuit<Scalar>) {
  assert_eq!(left.stats(), right.stats());
  for (left, right) in left.value_sources().zip(right.value_sources()) {
    match (left, right) {
      (Recipe::Input, Recipe::Input) | (Recipe::Hint, Recipe::Hint) => {},
      (Recipe::Arithmetic(a), Recipe::Arithmetic(b)) => assert_eq!(a, b),
      (Recipe::Constant(a), Recipe::Constant(b)) => assert_eq!(a, b),
      _ => panic!("different recipe kind"),
    }
  }
  for (left, right) in left.gates().iter().zip(right.gates()) {
    assert_eq!(left.wires.map(Value::index), right.wires.map(Value::index));
    assert_eq!(left.coefficients, right.coefficients);
  }
  for (left, right) in left.tables().iter().zip(right.tables()) {
    assert_eq!(left.name(), right.name());
    assert_eq!(left.rows(), right.rows());
  }
  for (left, right) in left.lookups().iter().zip(right.lookups()) {
    assert_eq!(left.table.index(), right.table.index());
    assert_eq!(
      left.values.iter().map(|v| v.index()).collect::<Vec<_>>(),
      right.values.iter().map(|v| v.index()).collect::<Vec<_>>()
    );
  }
  assert_eq!(
    left.public_values().iter().map(|v| v.index()).collect::<Vec<_>>(),
    right.public_values().iter().map(|v| v.index()).collect::<Vec<_>>()
  );
}

#[test]
fn scheduled_translation_preserves_assignments_and_errors() {
  let fixture = Fixture::new(24);
  let serial = fixture.translate(0);
  let scheduled = fixture.translate(64);
  assert_relation(&serial.circuit, &scheduled.circuit);
  assert_eq!(
    GoldilocksCircuit::estimate(&fixture.circuit),
    scheduled.circuit.stats()
  );
  let expected = fixture.witness(&serial).generate().unwrap();
  let actual = fixture.witness(&scheduled).generate().unwrap();
  assert_eq!(
    expected.values(serial.circuit.id()).unwrap(),
    actual.values(scheduled.circuit.id()).unwrap()
  );
  assert_eq!(expected.public_values(), actual.public_values());
  let values = fixture.assignment.values(fixture.circuit.id()).unwrap();
  let indices: Vec<_> = scheduled
    .inputs
    .is_input
    .iter()
    .enumerate()
    .filter_map(|(index, &input)| input.then_some(index))
    .collect();
  for missing in
    [indices[0], indices[indices.len() / 2], *indices.last().unwrap()]
  {
    let mut errors = Vec::new();
    for translated in [&serial, &scheduled] {
      let mut witness = translated.circuit.witness();
      for &index in &indices {
        if index != missing {
          witness
            .set(
              translated.inputs.wires[index],
              Scalar::from_u64(values[index].as_canonical_u64()),
            )
            .unwrap();
        }
      }
      errors.push(witness.generate().err());
    }
    assert_eq!(errors[0], errors[1]);
    assert_eq!(
      errors[0],
      Some(WitnessError::MissingInput {
        name: format!("goldilocks[{missing}]")
      })
    );
  }
  // A noncanonical Goldilocks alias must be rejected on both schedules.
  let mut errors = Vec::new();
  for translated in [&serial, &scheduled] {
    let mut witness = translated.circuit.witness();
    for &index in &indices {
      let value =
        if index == indices[0] { P } else { values[index].as_canonical_u64() };
      witness
        .set(translated.inputs.wires[index], Scalar::from_u64(value))
        .unwrap();
    }
    errors.push(witness.generate().err());
  }
  assert!(errors[0].is_some());
  assert_eq!(errors[0], errors[1]);
}

#[test]
fn public_translation_activates_parallel_schedule() {
  // Large enough for several default-size chunks on the public path.
  let fixture = Fixture::new(2048);
  let translated = GoldilocksCircuit::new_preallocated(&fixture.circuit);
  assert!(translated.circuit.stats().values > 2 << 16);
  assert_eq!(translated.inputs.scheduled(), cfg!(feature = "parallel"));
  assert!(!fixture.translate(0).inputs.scheduled());
  assert!(
    !GoldilocksCircuit::new_with_expanded_hashes(&fixture.circuit)
      .inputs
      .scheduled()
  );
  let mut census = CircuitBuilder::counting();
  let counted = GoldilocksCircuit::translate_with_chunk_size(
    &fixture.circuit,
    &mut census,
    false,
    1,
  );
  assert!(!counted.scheduled());
  let serial = fixture.translate(0);
  let expected = fixture.witness(&serial).generate().unwrap();
  let actual = fixture.witness(&translated).generate().unwrap();
  assert_eq!(
    expected.values(serial.circuit.id()).unwrap(),
    actual.values(translated.circuit.id()).unwrap()
  );
}

#[test]
fn scheduled_translation_preserves_verified_kzg_bytes() {
  use crate::kzg::{KzgConfig, Srs, compact::FixedProofCodec};
  use multi_stark::system::{System, SystemWitness};
  use std::sync::Arc;
  let fixture = Fixture::new(2);
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(1 << 16, b"independent-witness-advice")),
    4,
  );
  let mut proofs = Vec::new();
  for chunk_size in [0, 16] {
    let translated = fixture.translate(chunk_size);
    assert_eq!(
      translated.inputs.scheduled(),
      chunk_size > 0 && cfg!(feature = "parallel")
    );
    let assignment = fixture.witness(&translated).generate().unwrap();
    let compiled =
      translated.circuit.lower_to_multi_stark(Scalar::from_u8(89)).unwrap();
    let claims = compiled.claims(assignment.public_values()).unwrap();
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let (system, key) = System::new(config.clone(), compiled.circuit_inputs());
    let traces = compiled.traces(&assignment).unwrap();
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
