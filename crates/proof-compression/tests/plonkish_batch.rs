#[path = "support/parity.rs"]
mod fixture;
use ix_proof_compression::fri::ExpandedPcsWitness;
use ix_proof_compression::fri::FixedPcsShape;
use ix_proof_compression::fri::FixedVerifierInputs;
use ix_proof_compression::fri::build_single_batch_verifier;
use ix_proof_compression::fri::expand_pcs_witness;
use ix_proof_compression::fri::expand_single_batch_witness;
use multi_stark::batch::BatchMessage;
use multi_stark::batch::ShardInput;
use multi_stark::plonkish::Assignment;
use multi_stark::plonkish::Circuit;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::ExtVal;
use multi_stark::types::Val;
use p3_field::{PrimeCharacteristicRing, PrimeField64};

fn assign(
  c: &Circuit<Val>,
  i: &FixedVerifierInputs,
  e: &ExpandedPcsWitness,
) -> Result<Assignment<Val>, String> {
  let mut w = c.witness();
  e.assign(&mut w, i)?;
  w.generate().map_err(|e| e.to_string())
}
#[test]
fn single_batch_binds_transcript_claims_messages_and_pcs() {
  let (system, key) = System::new(fixture::config(), fixture::circuit_inputs());
  let messages = vec![
    BatchMessage::pull(vec![Val::from_u8(77)]),
    BatchMessage::push(vec![Val::from_u8(77)]),
  ];
  let shape = FixedPcsShape::new(&system, fixture::LOG_HEIGHT);
  let (c, inputs) =
    build_single_batch_verifier(&system, &shape, &[3], &messages);
  for n in [0, 17] {
    let claim = fixture::claim(fixture::Function::Even, n, n % 2 == 0);
    let batch = system.prove_batch(
      &key,
      vec![ShardInput {
        claims: vec![claim.clone()],
        witness: SystemWitness::from_stage_1(
          fixture::traces(fixture::Function::Even, n),
          &system,
        ),
      }],
      messages.clone(),
    );
    system.verify_batch(&batch).unwrap();
    let expanded =
      expand_single_batch_witness(&system, &shape, &batch, &messages).unwrap();
    let a = assign(&c, &inputs, &expanded).unwrap();
    assert_eq!(a.public_values(), claim);
    for (bits, expected) in
      inputs.query_bits.iter().zip(&expanded.query_indices)
    {
      let actual: u64 = bits
        .iter()
        .enumerate()
        .map(|(i, b)| a.value(b.value()).unwrap().as_canonical_u64() << i)
        .sum();
      assert_eq!(actual, *expected as u64);
    }
    drop(a);
    if n == 0 {
      continue;
    }
    for attack in 0..8 {
      let mut bad = expanded.clone();
      match attack {
        0 => bad.claims[0][1] += Val::ONE,
        1 => bad.challenges[0] += ExtVal::ONE,
        2 => bad.proof.intermediate_accumulators[0] += ExtVal::ONE,
        3 => bad.proof.stage_1_opened_values[0][0][0] += ExtVal::ONE,
        4 => bad.input_paths[0][0][0][0] ^= 1,
        5 => {
          bad.proof.opening_proof.commit_phase_openings[0].sibling_values[0]
            [0] += ExtVal::ONE
        },
        6 => bad.proof.opening_proof.final_poly[0] += ExtVal::ONE,
        _ => bad.fri_paths[0][0][0][0] ^= 1,
      }
      assert!(assign(&c, &inputs, &bad).is_err(), "attack {attack}");
    }
    let changed_messages = vec![
      BatchMessage::pull(vec![Val::from_u8(78)]),
      BatchMessage::push(vec![Val::from_u8(78)]),
    ];
    let wrong = system.prove_batch(
      &key,
      vec![ShardInput {
        claims: vec![claim.clone()],
        witness: SystemWitness::from_stage_1(
          fixture::traces(fixture::Function::Even, n),
          &system,
        ),
      }],
      changed_messages.clone(),
    );
    system.verify_batch(&wrong).unwrap();
    assert!(
      expand_single_batch_witness(&system, &shape, &wrong, &messages).is_err()
    );
    let wrong_expanded =
      expand_single_batch_witness(&system, &shape, &wrong, &changed_messages)
        .unwrap();
    assert!(
      assign(&c, &inputs, &wrong_expanded).is_err(),
      "valid proof for different fixed messages"
    );
    let single = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(
        fixture::traces(fixture::Function::Even, n),
        &system,
      ),
    );
    system.verify(&claim, &single).unwrap();
    let single_expanded =
      expand_pcs_witness(&system, &shape, &single, &[&claim]).unwrap();
    assert!(
      assign(&c, &inputs, &single_expanded).is_err(),
      "non-batch transcript accepted"
    );
  }
}
#[test]
fn single_batch_constrains_nonzero_residual_against_messages() {
  let (system, key) = System::new(fixture::config(), fixture::circuit_inputs());
  let claim = fixture::claim(fixture::Function::Odd, 19, true);
  let messages = vec![BatchMessage::push(claim)];
  let batch = system.prove_batch(
    &key,
    vec![ShardInput {
      claims: vec![],
      witness: SystemWitness::from_stage_1(
        fixture::traces(fixture::Function::Odd, 19),
        &system,
      ),
    }],
    messages.clone(),
  );
  system.verify_batch(&batch).unwrap();
  assert_ne!(
    *batch.proofs[0].intermediate_accumulators.last().unwrap(),
    ExtVal::ZERO
  );
  let shape = FixedPcsShape::new(&system, fixture::LOG_HEIGHT);
  let (c, i) = build_single_batch_verifier(&system, &shape, &[], &messages);
  let e =
    expand_single_batch_witness(&system, &shape, &batch, &messages).unwrap();
  assign(&c, &i, &e).unwrap();
  let mut bad = e;
  *bad.proof.intermediate_accumulators.last_mut().unwrap() = ExtVal::ZERO;
  assert!(assign(&c, &i, &bad).is_err());
}

#[test]
fn compact_hash_batch_verification_can_be_proved() {
  use ix_proof_compression::fri::ByteGadgets;
  use ix_proof_compression::fri::constrain_single_batch_verifier;
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::types::CommitmentParameters;
  use multi_stark::types::FriParameters;
  use multi_stark::types::GoldilocksBlake3Config;
  let (inner, key) = System::new(fixture::config(), fixture::circuit_inputs());
  let claim = fixture::claim(fixture::Function::Odd, 19, true);
  let batch = inner.prove_batch(
    &key,
    vec![ShardInput {
      claims: vec![claim.clone()],
      witness: SystemWitness::from_stage_1(
        fixture::traces(fixture::Function::Odd, 19),
        &inner,
      ),
    }],
    vec![],
  );
  inner.verify_batch(&batch).unwrap();
  let shape = FixedPcsShape::new(&inner, fixture::LOG_HEIGHT);
  let mut b = CircuitBuilder::new();
  b.enable_compact_blake3();
  let wires =
    (0..claim.len()).map(|i| b.public_input(format!("claim{i}"))).collect();
  let bytes = ByteGadgets::new(&mut b);
  let inputs = constrain_single_batch_verifier(
    &mut b,
    &bytes,
    &inner,
    &shape,
    vec![wires],
    &[],
  );
  let circuit = b.finish();
  let expanded =
    expand_single_batch_witness(&inner, &shape, &batch, &[]).unwrap();
  let a = assign(&circuit, &inputs, &expanded).unwrap();
  for (bits, &expected) in inputs.query_bits.iter().zip(&expanded.query_indices)
  {
    let actual: u64 = bits
      .iter()
      .enumerate()
      .map(|(i, bit)| a.value(bit.value()).unwrap().as_canonical_u64() << i)
      .sum();
    assert_eq!(actual, expected as u64);
  }
  let compiled = circuit.lower_to_multi_stark(Val::from_u8(99)).unwrap();
  let claims = compiled.claims(&claim).unwrap();
  let traces = compiled.traces(&a).unwrap();
  let mut defs = compiled.circuit_inputs();
  for d in &mut defs {
    d.lookup_group_size = 3;
  }
  let cfg = GoldilocksBlake3Config::new(
    CommitmentParameters { log_blowup: 2, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 32,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  );
  let (outer, key) = System::new(cfg, defs);
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let proof = outer.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(traces, &outer),
  );
  outer.verify_multiple_claims(&refs, &proof).unwrap();
  let mut bad = claim;
  bad[1] += Val::ONE;
  let bad = compiled.claims(&bad).unwrap();
  assert!(
    outer
      .verify_multiple_claims(
        &bad.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &proof
      )
      .is_err()
  );
}
