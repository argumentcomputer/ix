#[path = "support/parity.rs"]
mod parity;

use ix_proof_compression::fri::FixedPcsShape;
use ix_proof_compression::fri::build_fixed_verifier;
use ix_proof_compression::fri::expand_pcs_witness;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_field::PrimeField64;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::ExtVal;
use multi_stark::types::Val;
use p3_symmetric::MerkleCap;

#[test]
fn full_fixed_verifier_accepts_native_proofs_and_rejects_corruption() {
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  let (circuit, inputs) =
    build_fixed_verifier(&system, parity::LOG_HEIGHT, &[3]);
  println!(
    "Full verifier: {} gates, {} lookups, {} values",
    circuit.gates().len(),
    circuit.lookups().len(),
    circuit.num_values()
  );
  assert_eq!(circuit.public_values().len(), 3);
  for (function, n) in [
    (parity::Function::Even, 100),
    (parity::Function::Odd, 127),
    (parity::Function::Odd, 0),
  ] {
    let claim = parity::claim(function, n, function.result(n));
    let proof = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(parity::traces(function, n), &system),
    );
    system.verify(&claim, &proof).unwrap();
    let expanded =
      expand_pcs_witness(&system, &inputs.shape, &proof, &[&claim]).unwrap();
    let mut witness = circuit.witness();
    expanded.assign(&mut witness, &inputs).unwrap();
    let assignment = witness.generate().unwrap();
    assert_eq!(assignment.public_values(), claim);
    for (bits, &native) in inputs.query_bits.iter().zip(&expanded.query_indices)
    {
      let derived: u64 = bits
        .iter()
        .enumerate()
        .map(|(i, bit)| {
          assignment.value(bit.value()).unwrap().as_canonical_u64() << i
        })
        .sum();
      assert_eq!(derived, u64::try_from(native).unwrap());
    }
    if n != 100 {
      continue;
    }
    for attack in 0..13 {
      let mut wrong = expanded.clone();
      match attack {
        0 => wrong.claims[0][2] += Val::ONE,
        1 => wrong.proof.stage_1_opened_values[0][0][0] += ExtVal::ONE,
        2 => {
          wrong.proof.opening_proof.input_openings[0].opened_values[0][0][0] +=
            Val::ONE
        },
        3 => wrong.input_paths[0][0][0][0] ^= 1,
        4 => wrong.fri_paths[0][0][0][0] ^= 1,
        5 => {
          wrong.proof.opening_proof.commit_phase_openings[0].sibling_values
            [0][0] += ExtVal::ONE
        },
        6 => wrong.proof.opening_proof.final_poly[0] += ExtVal::ONE,
        7 => wrong.proof.intermediate_accumulators[0] += ExtVal::ONE,
        8 => {
          wrong.proof.opening_proof.input_openings[3].opened_values[0][0][0] +=
            Val::ONE
        },
        9 => wrong.challenges[3] += ExtVal::ONE,
        10 => {
          let root = &mut wrong.proof.opening_proof.commit_phase_commits[0];
          let mut digest = root.roots()[0];
          digest[0] ^= 1;
          *root = MerkleCap::new(vec![digest]);
        },
        11 => {
          wrong
            .proof
            .opening_proof
            .commit_phase_openings
            .last_mut()
            .unwrap()
            .sibling_values[3][0] += ExtVal::ONE;
        },
        _ => wrong.fri_paths[3].last_mut().unwrap()[0][0] ^= 1,
      }
      let mut witness = circuit.witness();
      wrong.assign(&mut witness, &inputs).unwrap();
      assert!(witness.generate().is_err(), "accepted attack {attack}");
    }
  }
}

#[test]
fn full_verifier_adapter_rejects_malformed_fixed_shapes() {
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  let shape = FixedPcsShape::new(&system, parity::LOG_HEIGHT);
  let claim = parity::claim(parity::Function::Odd, 17, true);
  let proof = system.prove(
    &key,
    &claim,
    SystemWitness::from_stage_1(
      parity::traces(parity::Function::Odd, 17),
      &system,
    ),
  );
  for attack in 0..6 {
    let mut wrong = proof.clone();
    match attack {
      0 => wrong.log_degrees[0] -= 1,
      1 => {
        wrong.opening_proof.input_openings[0].opened_values.pop();
      },
      2 => wrong.opening_proof.commit_phase_openings[0].log_arity = 2,
      3 => wrong.opening_proof.final_poly.push(ExtVal::ZERO),
      4 => {
        wrong.opening_proof.input_openings[0]
          .opening_proof
          .sibling_hashes
          .pop();
      },
      _ => wrong.opening_proof.input_openings[0]
        .opening_proof
        .sibling_hashes
        .push([0; 32]),
    }
    assert!(
      expand_pcs_witness(&system, &shape, &wrong, &[&claim]).is_err(),
      "malformed shape {attack}"
    );
  }
}
