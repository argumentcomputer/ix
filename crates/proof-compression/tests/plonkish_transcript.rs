#[path = "support/parity_algebra.rs"]
mod adapter;
#[path = "support/parity.rs"]
mod parity;

use ix_proof_compression::fri::AlgebraicInputs;
use ix_proof_compression::fri::ByteGadgets;
use ix_proof_compression::fri::TranscriptCommitments;
use ix_proof_compression::fri::constrain_algebraic_checks;
use ix_proof_compression::fri::constrain_transcript;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::Val;

#[test]
fn parity_transcript_and_algebra_match_native_and_reject_changed_roots() {
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  let mut builder = CircuitBuilder::new();
  let inputs = AlgebraicInputs::allocate(&mut builder, &system.circuits, &[3]);
  let bytes = ByteGadgets::new(&mut builder);
  let roots = TranscriptCommitments::allocate(&mut builder, &bytes);
  constrain_transcript(
    &mut builder,
    &bytes,
    &system,
    &[parity::LOG_HEIGHT; 2],
    &inputs,
    &roots,
  );
  constrain_algebraic_checks(
    &mut builder,
    &system.circuits,
    &[parity::LOG_HEIGHT; 2],
    &inputs,
  );
  // This intermediate test deliberately omits PCS verification.
  adapter::expose_boundary(&mut builder, &inputs);
  for byte in roots.stage1.iter().chain(&roots.stage2).chain(&roots.quotient) {
    builder.expose_public(byte.value());
  }
  let circuit = builder.finish();
  println!(
    "Transcript + algebra: {} gates, {} lookups, {} values",
    circuit.gates().len(),
    circuit.lookups().len(),
    circuit.num_values()
  );
  for (function, n) in [
    (parity::Function::Even, 0),
    (parity::Function::Odd, 17),
    (parity::Function::Even, 100),
    (parity::Function::Odd, 127),
  ] {
    let claim = parity::claim(function, n, function.result(n));
    let proof = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(parity::traces(function, n), &system),
    );
    system.verify(&claim, &proof).unwrap();
    let challenges = adapter::challenges(&system, &proof, &[&claim]);
    let digests = [
      proof.commitments.stage_1_trace.roots()[0],
      proof.commitments.stage_2_trace.roots()[0],
      proof.commitments.quotient_chunks.roots()[0],
    ];
    for altered_root in [None, Some(0), Some(1), Some(2)] {
      let mut witness = circuit.witness();
      adapter::assign(&mut witness, &inputs, &proof, &[&claim], challenges)
        .unwrap();
      for (i, (wires, digest)) in
        [&roots.stage1, &roots.stage2, &roots.quotient]
          .into_iter()
          .zip(digests)
          .enumerate()
      {
        for (j, (wire, value)) in wires.iter().zip(digest).enumerate() {
          let value = value ^ u8::from(altered_root == Some(i) && j == 0);
          witness.set(wire.value(), Val::from_u8(value)).unwrap();
        }
      }
      let result = witness.generate();
      if altered_root.is_some() {
        assert!(result.is_err(), "altered root {altered_root:?}");
      } else {
        let assignment = result.unwrap();
        let mut expected = adapter::statement(&proof, &[&claim], challenges);
        expected.extend(digests.into_iter().flatten().map(Val::from_u8));
        assert_eq!(assignment.public_values(), expected);
      }
    }
  }
}
