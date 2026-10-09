#[path = "support/root_profile.rs"]
mod fixture;

use ix_proof_compression::fri::ExpandedPcsWitness;
use ix_proof_compression::fri::expand_pcs_witness;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_field::PrimeField64;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::ExtVal;
use multi_stark::types::Val;
use p3_blake3::Blake3;
use p3_symmetric::CryptographicHasher;

fn accepts(
  verifier: &fixture::StatementVerifier,
  expanded: &ExpandedPcsWitness,
  subject: [u8; 32],
) -> bool {
  let mut witness = verifier.circuit.witness();
  if expanded.assign_proof(&mut witness, &verifier.inputs).is_err() {
    return false;
  }
  for (wire, value) in verifier.subject.iter().zip(subject) {
    witness.set(wire.value(), Val::from_u8(value)).unwrap();
  }
  witness.generate().is_ok()
}

#[test]
fn root_profile_constrains_sparse_mixed_height_grouped_proof_and_statement() {
  let profile = fixture::Profile::Smoke;
  let (system, key) =
    System::new(profile.config(), fixture::circuit_inputs(profile));
  let verifier = fixture::build_statement_verifier(&system, profile);
  assert_eq!(verifier.circuit.public_values().len(), 32);
  assert_eq!(
    verifier.circuit.stats().tables,
    3,
    "statement and verifier share byte tables"
  );
  assert_eq!(verifier.inputs.shape.preprocessed, [2, 4]);
  assert_eq!(verifier.inputs.shape.widths[3], [11, 11]);
  assert_eq!(system.circuits[0].quotient_degree(), 4);
  assert_eq!(system.circuits[0].stage_2_width, 4);
  assert_eq!(system.circuits[2].stage_2_width, 2);
  println!("Root-profile circuit: {:?}", verifier.circuit.stats());
  for subject in [[0x5a; 32], [0xa5; 32]] {
    let claim = fixture::claim(subject);
    let proof = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(fixture::traces(profile, subject), &system),
    );
    system.verify(&claim, &proof).unwrap();
    assert_eq!(proof.active, fixture::ACTIVE);
    assert_eq!(proof.log_degrees, profile.logs());
    let expanded =
      expand_pcs_witness(&system, &verifier.inputs.shape, &proof, &[&claim])
        .unwrap();
    let mut witness = verifier.circuit.witness();
    expanded.assign_proof(&mut witness, &verifier.inputs).unwrap();
    for (wire, value) in verifier.subject.iter().zip(subject) {
      witness.set(wire.value(), Val::from_u8(value)).unwrap();
    }
    let assignment = witness.generate().unwrap();
    assert_eq!(assignment.public_values(), subject.map(Val::from_u8));
    for (&wire, &value) in verifier.inputs.algebra.claims[0].iter().zip(&claim)
    {
      assert_eq!(assignment.value(wire).unwrap(), value);
    }
    for (bits, &index) in
      verifier.inputs.query_bits.iter().zip(&expanded.query_indices)
    {
      let actual: u64 = bits
        .iter()
        .enumerate()
        .map(|(i, b)| {
          assignment.value(b.value()).unwrap().as_canonical_u64() << i
        })
        .sum();
      assert_eq!(actual, u64::try_from(index).unwrap());
    }
    let mut wrong_subject = subject;
    wrong_subject[0] ^= 1;
    assert!(!accepts(&verifier, &expanded, wrong_subject));
    if subject[0] != 0x5a {
      continue;
    }
    for attack in 0..18 {
      let mut bad = expanded.clone();
      match attack {
        0 => bad.proof.active.swap(1, 2),
        1 => bad.proof.log_degrees[2] += 1,
        2 => bad.proof.stage_2_opened_values[0][0][3] += ExtVal::ONE,
        3 => bad.proof.quotient_opened_values[0][0][7] += ExtVal::ONE,
        4 => {
          bad.proof.preprocessed_opened_values.as_mut().unwrap()[1][1][10] +=
            ExtVal::ONE
        },
        5 => {
          bad.proof.opening_proof.input_openings[0].opened_values[0][2][0] +=
            Val::ONE
        },
        6 => {
          bad.proof.opening_proof.input_openings[3].opened_values[0][0][0] +=
            Val::ONE
        },
        7 => {
          bad.proof.opening_proof.input_openings[3].opened_values[0][1][10] +=
            Val::ONE
        },
        8 => bad.input_paths[0][0][0][0] ^= 1,
        9 => bad.input_paths[0][3][0][0] ^= 1,
        10 => bad.proof.opening_proof.commit_pow_witnesses[0] += Val::ONE,
        11 => bad.proof.opening_proof.query_pow_witness += Val::ONE,
        12 => {
          bad.proof.opening_proof.commit_phase_openings[2].sibling_values[0]
            [0] += ExtVal::ONE
        },
        13 => {
          bad.proof.opening_proof.commit_phase_openings[5].sibling_values[0]
            [0] += ExtVal::ONE
        },
        14 => {
          bad.proof.opening_proof.input_openings[0].opened_values[0][6][0] +=
            Val::ONE
        },
        15 => bad.proof.intermediate_accumulators[2] += ExtVal::ONE,
        16 => bad.proof.stage_1_opened_values[1][1][2] += ExtVal::ONE,
        _ => bad.proof.opening_proof.final_poly[0] += ExtVal::ONE,
      }
      assert!(!accepts(&verifier, &bad, subject), "accepted attack {attack}");
    }
    // The enclosing circuit, not the host adapter, supplies the claim.
    let mut ignored_claim = expanded.clone();
    ignored_claim.claims[0][1] += Val::ONE;
    assert!(accepts(&verifier, &ignored_claim, subject));

    // These are VALID native fixture proofs, but receipts for the wrong
    // statement type/scope/assumptions. Rejection must come from the
    // composed circuit, not native acceptance in the witness adapter.
    for attack in 0..5 {
      let mut encoded = fixture::receipt_bytes(subject);
      match attack {
        0 => encoded[0] = 0xe4, // wrong claim tag
        1 => encoded[1] = 2,    // old object format
        2 => encoded[2] = 0,    // wrong validator identifier
        3 => {
          encoded[35] = 1;
          encoded.extend([0x33; 32]);
        }, // conditional
        _ => encoded.push(0),   // noncanonical trailing byte
      }
      let digest: [u8; 32] = Blake3.hash_iter(encoded);
      let mut wrong_claim = claim.clone();
      for (word, chunk) in
        wrong_claim[10..].iter_mut().zip(digest.as_chunks::<4>().0)
      {
        *word = Val::from_u32(u32::from_le_bytes(*chunk));
      }
      let mut traces = fixture::traces(profile, subject);
      traces[0].values[1..9].copy_from_slice(&wrong_claim[10..]);
      let wrong_proof = system.prove(
        &key,
        &wrong_claim,
        SystemWitness::from_stage_1(traces, &system),
      );
      system.verify(&wrong_claim, &wrong_proof).unwrap();
      let wrong = expand_pcs_witness(
        &system,
        &verifier.inputs.shape,
        &wrong_proof,
        &[&wrong_claim],
      )
      .unwrap();
      assert!(
        !accepts(&verifier, &wrong, subject),
        "accepted wrong statement codec {attack}"
      );
    }

    // Same dimensions/active map, different trusted preprocessing OR AIR.
    for attack in 0..2 {
      let mut definitions = fixture::circuit_inputs(profile);
      let mut traces = fixture::traces(profile, subject);
      if attack == 0 {
        definitions[3].preprocessed.as_mut().unwrap().values[10] += Val::ONE;
      } else {
        use multi_stark::expr::Expr;
        definitions[8].constraints =
          vec![Expr::main(0) - Expr::constant(Val::from_u8(18))];
        traces[8].values[0] = Val::from_u8(18);
      }
      let (other_system, other_key) =
        System::new(profile.config(), definitions);
      let other_proof = other_system.prove(
        &other_key,
        &claim,
        SystemWitness::from_stage_1(traces, &other_system),
      );
      other_system.verify(&claim, &other_proof).unwrap();
      let other = expand_pcs_witness(
        &other_system,
        &profile.shape(&other_system),
        &other_proof,
        &[&claim],
      )
      .unwrap();
      assert!(
        !accepts(&verifier, &other, subject),
        "accepted another key {attack}"
      );
    }
  }
}

#[test]
fn root_statement_codec_and_unit_consumer_policy_are_explicit() {
  let subject = std::array::from_fn(|i| u8::try_from(i).unwrap());
  let encoded = fixture::receipt_bytes(subject);
  // Golden fixture wire layout, written explicitly rather than using a shared helper
  // used to construct the circuit. The unconditional receipt is 36 bytes.
  assert_eq!(encoded.len(), 36);
  assert_eq!(&encoded[..3], &[0xe5, 3, 1]);
  assert_eq!(&encoded[3..35], &subject);
  assert_eq!(encoded[35], 0);
  let blob = fixture::allowed_blob();
  assert_eq!(blob.len(), 80);
  assert_eq!(&blob[32..40], &23u64.to_le_bytes());
  assert_eq!(&blob[72..80], &fixture::AGGR_INDEX.to_le_bytes());
  let bound = |slots: &[usize], active: &[bool], logs: &[u8], claims| {
    fixture::unit_lookup_bound(slots.iter().copied(), active, logs, claims)
  };
  assert_eq!(bound(&[2, 999, 3], &[true, false, true], &[7, 0], 1), Some(260));
  assert_eq!(
    bound(&[1], &[true], &[0], Val::ORDER_U64 - 2),
    Some(Val::ORDER_U64 - 1)
  );
  assert_eq!(bound(&[1], &[true], &[0], Val::ORDER_U64 - 1), None);
  assert_eq!(bound(&[3], &[true], &[63], 1), None);
  assert_eq!(bound(&[1], &[true], &[64], 1), None);
  assert_eq!(bound(&[1], &[false], &[], 1), None);
  assert_eq!(bound(&[1], &[true], &[], 1), None);
  assert_eq!(bound(&[1], &[true], &[0, 0], 1), None);
  assert_eq!(bound(&[1], &[true, false], &[0], 1), None);
}

#[test]
#[ignore = "full-size tables, 100 queries and 20-bit grinding; native + adapter only"]
fn root_profile_full_size_native_proof() {
  let profile = fixture::Profile::FullSize;
  let (system, key) =
    System::new(profile.config(), fixture::circuit_inputs(profile));
  let subject = [0x5a; 32];
  let claim = fixture::claim(subject);
  let proof = system.prove(
    &key,
    &claim,
    SystemWitness::from_stage_1(fixture::traces(profile, subject), &system),
  );
  system.verify(&claim, &proof).unwrap();
  let shape = profile.shape(&system);
  assert_eq!(shape.queries, 100);
  assert_eq!(shape.log_trace, 16);
  expand_pcs_witness(&system, &shape, &proof, &[&claim]).unwrap();
}
