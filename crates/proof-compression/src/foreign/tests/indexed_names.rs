use super::*;

struct Fixture {
  circuit: Circuit<Val>,
  inputs: Vec<(Value, Val)>,
}

impl Fixture {
  fn new(rounds: usize) -> Self {
    let mut builder = CircuitBuilder::<Val>::new();
    let bytes = builder.fixed_table(
      "bytes",
      (0..=255).map(|i| vec![Val::from_u16(i)]).collect(),
    );
    let mut inputs = Vec::new();
    for i in 0..rounds {
      let constant = builder.constant(Val::from_usize(17 + i % 31));
      let bit = builder.input("choice");
      inputs.push((bit, Val::from_usize(i % 2)));
      let bit = builder.assert_bool(bit);
      let byte = builder.input("byte");
      inputs.push((byte, Val::from_usize(7 + i % 249)));
      builder.lookup(bytes, &[byte]);
      let wide = builder.input("wide");
      inputs
        .push((wide, Val::from_u64(P - 1 - u64::try_from(i % 257).unwrap())));
      let product = builder.mul(wide, byte);
      let shifted = builder.add(product, constant);
      let selected = builder.select(bit, shifted, byte);
      let copied = builder.hint("copy", &[selected], |values| Ok(values[0]));
      builder.assert_equal(copied, selected);
      builder.constant(Val::from_usize(333 + i % 37));
      if i + 1 == rounds {
        builder.expose_public(copied);
      }
    }
    Self { circuit: builder.finish(), inputs }
  }

  fn assignment(&self) -> Assignment<Val> {
    let mut witness = self.circuit.witness();
    for &(wire, value) in &self.inputs {
      witness.set(wire, value).unwrap();
    }
    witness.generate().unwrap()
  }
}

fn translate<const INDEXED: bool>(
  source: &Circuit<Val>,
  builder: &mut CircuitBuilder<Scalar>,
) -> GoldilocksInputs {
  if INDEXED {
    GoldilocksCircuit::translate(source, builder, false)
  } else {
    GoldilocksCircuit::translate_with_inputs(
      source,
      builder,
      false,
      |builder, i| builder.input(format!("goldilocks[{i}]")),
    )
  }
}

fn preallocated<const INDEXED: bool>(
  source: &Circuit<Val>,
) -> GoldilocksCircuit {
  let stats = {
    let mut builder = CircuitBuilder::counting();
    translate::<INDEXED>(source, &mut builder);
    builder.stats()
  };
  let mut builder = CircuitBuilder::new();
  builder.reserve(stats);
  let inputs = translate::<INDEXED>(source, &mut builder);
  assert_eq!(builder.stats(), stats);
  GoldilocksCircuit { circuit: builder.finish(), inputs }
}

fn assert_layout(expected: &GoldilocksCircuit, actual: &GoldilocksCircuit) {
  assert_eq!(expected.circuit.stats(), actual.circuit.stats());
  assert_eq!(expected.inputs.is_input, actual.inputs.is_input);
  assert_eq!(
    expected.inputs.wires.iter().map(|v| v.index()).collect::<Vec<_>>(),
    actual.inputs.wires.iter().map(|v| v.index()).collect::<Vec<_>>()
  );
  for (left, right) in
    expected.circuit.value_sources().zip(actual.circuit.value_sources())
  {
    match (left, right) {
      (Recipe::Input, Recipe::Input) | (Recipe::Hint, Recipe::Hint) => {},
      (Recipe::Arithmetic(a), Recipe::Arithmetic(b)) => assert_eq!(a, b),
      (Recipe::Constant(a), Recipe::Constant(b)) => assert_eq!(a, b),
      _ => panic!("different recipe kind"),
    }
  }
  for (left, right) in
    expected.circuit.gates().iter().zip(actual.circuit.gates())
  {
    assert_eq!(left.wires.map(|v| v.index()), right.wires.map(|v| v.index()));
    assert_eq!(left.coefficients, right.coefficients);
  }
  for (left, right) in
    expected.circuit.tables().iter().zip(actual.circuit.tables())
  {
    assert_eq!(left.name(), right.name());
    assert_eq!(left.rows(), right.rows());
  }
  for (left, right) in
    expected.circuit.lookups().iter().zip(actual.circuit.lookups())
  {
    assert_eq!(left.table.index(), right.table.index());
    assert_eq!(
      left.values.iter().map(|v| v.index()).collect::<Vec<_>>(),
      right.values.iter().map(|v| v.index()).collect::<Vec<_>>()
    );
  }
  assert_eq!(
    expected
      .circuit
      .public_values()
      .iter()
      .map(|v| v.index())
      .collect::<Vec<_>>(),
    actual
      .circuit
      .public_values()
      .iter()
      .map(|v| v.index())
      .collect::<Vec<_>>()
  );
}

fn assign(
  translated: &GoldilocksCircuit,
  source: &Assignment<Val>,
) -> Assignment<Scalar> {
  let mut witness = translated.circuit.witness();
  translated.assign(source, &mut witness).unwrap();
  witness.generate().unwrap()
}

#[test]
fn indexed_names_preserve_translation_layout_values_and_missing_inputs() {
  let fixture = Fixture::new(5);
  let source = fixture.assignment();
  let expected = preallocated::<false>(&fixture.circuit);
  let actual = GoldilocksCircuit::new_preallocated(&fixture.circuit);
  assert_layout(&expected, &actual);
  let old_assignment = assign(&expected, &source);
  let new_assignment = assign(&actual, &source);
  assert_eq!(
    old_assignment.values(expected.circuit.id()).unwrap(),
    new_assignment.values(actual.circuit.id()).unwrap()
  );
  assert_eq!(old_assignment.public_values(), new_assignment.public_values());
  let indices: Vec<_> = actual
    .inputs
    .is_input
    .iter()
    .enumerate()
    .filter_map(|(index, &input)| input.then_some(index))
    .collect();
  assert!(indices.windows(2).any(|pair| pair[1] != pair[0] + 1));
  let values = source.values(fixture.circuit.id()).unwrap();
  for missing in
    [indices[0], indices[indices.len() / 2], *indices.last().unwrap()]
  {
    for translated in [&expected, &actual] {
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
      assert_eq!(
        witness.generate().err(),
        Some(WitnessError::MissingInput {
          name: format!("goldilocks[{missing}]")
        })
      );
    }
  }
}

#[test]
fn indexed_names_preserve_owned_names_and_lazy_census() {
  struct UnusedName;
  // The conversion must never run; counting builders keep names lazy.
  #[allow(clippy::fallible_impl_from)]
  impl From<UnusedName> for String {
    fn from(_: UnusedName) -> Self {
      panic!("counting must not materialize an input name")
    }
  }
  let mut census = CircuitBuilder::<Scalar>::counting();
  census.input(UnusedName);
  census.input_indexed("goldilocks", usize::MAX);
  assert_eq!(census.stats().inputs, 2);
  for name in ["", "input α[17]"] {
    let mut builder = CircuitBuilder::<Scalar>::new();
    builder.input(name);
    assert_eq!(
      builder.finish().witness().generate().err(),
      Some(WitnessError::MissingInput { name: name.into() })
    );
  }
  let mut builder = CircuitBuilder::<Scalar>::new();
  builder.input_indexed("goldilocks", usize::MAX);
  assert_eq!(
    builder.finish().witness().generate().err(),
    Some(WitnessError::MissingInput {
      name: format!("goldilocks[{}]", usize::MAX)
    })
  );
}

#[test]
fn indexed_names_preserve_verified_kzg_bytes() {
  use crate::kzg::{KzgConfig, Srs, compact::FixedProofCodec};
  use multi_stark::system::{System, SystemWitness};
  use std::sync::Arc;
  let fixture = Fixture::new(2);
  let source = fixture.assignment();
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(1 << 16, b"indexed-input-names")),
    4,
  );
  let mut proofs = Vec::new();
  for indexed in [false, true] {
    let translated = if indexed {
      GoldilocksCircuit::new_preallocated(&fixture.circuit)
    } else {
      preallocated::<false>(&fixture.circuit)
    };
    let assignment = assign(&translated, &source);
    let compiled =
      translated.circuit.lower_to_multi_stark(Scalar::from_u8(88)).unwrap();
    let claims = compiled.claims(assignment.public_values()).unwrap();
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let traces = compiled.traces(&assignment).unwrap();
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
  assert_eq!(proofs[0], proofs[1]);
}
