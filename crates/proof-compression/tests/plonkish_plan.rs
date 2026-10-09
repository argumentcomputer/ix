//! Tests the generic generator using a small lookup system.
use ix_proof_compression::fri::*;
use multi_stark::batch::BatchMessage;
use multi_stark::batch::ShardInput;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::system::CircuitInputs;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::CommitmentParameters;
use multi_stark::types::FriParameters;
use multi_stark::types::GoldilocksBlake3Config as Config;
use multi_stark::types::Val;
use p3_matrix::dense::RowMajorMatrix;

fn config() -> Config {
  Config::new(
    CommitmentParameters { log_blowup: 2, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  )
}
fn setup() -> (System<Config>, multi_stark::system::ProverKey<Config>) {
  System::new(
    config(),
    [CircuitInputs {
      main_width: 1,
      preprocessed: Some(RowMajorMatrix::new(vec![Val::ONE, Val::ZERO], 1)),
      constraints: vec![],
      ext_constraints: vec![],
      lookups: vec![Lookup {
        multiplicity: -Expr::preprocessed(0),
        args: vec![Expr::main(0)],
      }],
      lookup_group_size: 1,
    }],
  )
}
fn trace(system: &System<Config>, value: Val) -> SystemWitness<Val> {
  SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(vec![value; 2], 1)],
    system,
  )
}

fn profile(envelope: Envelope) -> ProofProfile {
  ProofProfile {
    envelope,
    active: vec![true],
    log_degrees: vec![1],
    claim_lengths: if envelope == Envelope::Ordinary {
      vec![1]
    } else {
      vec![]
    },
    message_lengths: if envelope == Envelope::SingleBatch {
      vec![1]
    } else {
      vec![]
    },
    max_field_retries: 2,
  }
}

#[test]
fn dynamic_batch_statements_reuse_circuit_and_outer_key() {
  let (system, pk) = setup();
  let key = VerifierKey::from_system(&system);
  assert!(key.system().circuits.iter().all(|c| c.preprocessed.is_none()));
  let mut batch_profile = profile(Envelope::SingleBatch);
  batch_profile.message_lengths.push(1);
  let plan =
    VerifierPlan::validate(&key, batch_profile, VerifierLimits::default())
      .unwrap();
  let schema = Statement {
    claims: vec![],
    messages: vec![
      Message {
        args: vec![StatementSlot::Public],
        multiplicity: StatementSlot::Public,
      };
      2
    ],
  };
  let (circuit, inputs) =
    plan.build(schema, ImplementationOptions::default()).unwrap();
  assert_eq!(
    circuit.stats().inputs,
    plan.resources().proof_values + plan.resources().statement_values
  );
  let compiled = circuit.lower_to_multi_stark(Val::from_u8(91)).unwrap();
  let (outer, outer_pk) = System::new(config(), compiled.circuit_inputs());
  for (value, first) in
    [(Val::from_u8(13), Val::ONE), (Val::from_u8(91), Val::from_u8(3))]
  {
    let second = Val::ONE - first;
    let batch = system.prove_batch(
      &pk,
      vec![ShardInput { claims: vec![], witness: trace(&system, value) }],
      vec![
        BatchMessage { args: vec![value], multiplicity: first },
        BatchMessage { args: vec![value], multiplicity: second },
      ],
    );
    system.verify_batch(&batch).unwrap();
    let prepared =
      plan.expand_witness(ProofEnvelope::SingleBatch(&batch)).unwrap();
    let statement = Statement {
      claims: vec![],
      messages: vec![
        Message { args: vec![value], multiplicity: first },
        Message { args: vec![value], multiplicity: second },
      ],
    };
    let mut w = compiled.witness();
    inputs.assign_statement(&mut w, &statement).unwrap();
    prepared.assign_proof(&mut w, &inputs).unwrap();
    let a = w.generate().unwrap();
    let public = [value, first, value, second];
    assert_eq!(a.public_values(), &public);
    let claims = compiled.claims(&public).unwrap();
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = outer.prove_multiple_claims(
      &outer_pk,
      &refs,
      SystemWitness::from_stage_1(compiled.traces(&a).unwrap(), &outer),
    );
    outer.verify_multiple_claims(&refs, &proof).unwrap();
    let wrong_claims =
      compiled.claims(&[value + Val::ONE, first, value, second]).unwrap();
    assert!(
      outer
        .verify_multiple_claims(
          &wrong_claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
          &proof
        )
        .is_err()
    );
    for change_multiplicity in [false, true] {
      let mut bad = statement.clone();
      if change_multiplicity {
        bad.messages[0].multiplicity += Val::ONE;
      } else {
        bad.messages[0].args[0] += Val::ONE;
      }
      let mut w = compiled.witness();
      inputs.assign_statement(&mut w, &bad).unwrap();
      prepared.assign_proof(&mut w, &inputs).unwrap();
      assert!(w.generate().is_err());
    }
    let mut malformed = batch.clone();
    malformed.preamble.headers[0].log_degrees[0] = 2;
    assert!(
      plan.expand_witness(ProofEnvelope::SingleBatch(&malformed)).is_err()
    );
  }
}

#[test]
fn ordinary_composition_proof_assignment_preserves_statement_owner() {
  let (system, pk) = setup();
  let key = VerifierKey::from_system(&system);
  let plan = VerifierPlan::validate(
    &key,
    profile(Envelope::Ordinary),
    VerifierLimits::default(),
  )
  .unwrap();
  let mut b = CircuitBuilder::new();
  let public = b.public_input("subject");
  let one = b.constant(Val::ONE);
  let derived = b.add(public, one);
  let inputs = plan
    .constrain(
      &mut b,
      Statement {
        claims: vec![vec![StatementBinding::Wire(derived)]],
        messages: vec![],
      },
      ImplementationOptions::default(),
    )
    .unwrap();
  let c = b.finish();
  for value in [Val::from_u8(4), Val::from_u8(19)] {
    let claims = vec![vec![value]];
    let proof = system.prove(&pk, &claims[0], trace(&system, value));
    system.verify(&claims[0], &proof).unwrap();
    let prepared = plan
      .expand_witness(ProofEnvelope::Ordinary {
        proof: &proof,
        claims: &claims,
      })
      .unwrap();
    let mut w = c.witness();
    w.set(public, value - Val::ONE).unwrap();
    prepared.assign_proof(&mut w, &inputs).unwrap();
    assert_eq!(w.generate().unwrap().public_values(), &[value - Val::ONE]);
    let mut w = c.witness();
    prepared.assign_proof(&mut w, &inputs).unwrap();
    assert!(
      w.generate().is_err(),
      "proof assignment must not assign the public subject"
    );
    let mut w = c.witness();
    w.set(public, value).unwrap();
    prepared.assign_proof(&mut w, &inputs).unwrap();
    assert!(w.generate().is_err());
    let mut corrupt = proof.clone();
    corrupt.opening_proof.final_poly[0] += multi_stark::types::ExtVal::ONE;
    if let Ok(p) = plan.expand_witness(ProofEnvelope::Ordinary {
      proof: &corrupt,
      claims: &claims,
    }) {
      let mut w = c.witness();
      w.set(public, value - Val::ONE).unwrap();
      p.assign_proof(&mut w, &inputs).unwrap();
      assert!(w.generate().is_err());
    }
  }
}

#[test]
fn malformed_profiles_are_rejected_before_construction() {
  let (system, _) = setup();
  let key = VerifierKey::from_system(&system);
  for mutation in 0..7 {
    let mut p = profile(Envelope::Ordinary);
    match mutation {
      0 => p.active.clear(),
      1 => p.log_degrees.clear(),
      2 => p.log_degrees[0] = u8::MAX,
      3 => p.log_degrees[0] = 2,
      4 => p.message_lengths.push(1),
      5 => p.max_field_retries = usize::MAX,
      _ => p.claim_lengths = vec![usize::MAX, 1],
    }
    assert!(
      VerifierPlan::validate(&key, p, VerifierLimits::default()).is_err()
    );
  }
  let limits =
    VerifierLimits { max_proof_values: 1, ..VerifierLimits::default() };
  assert!(matches!(
    VerifierPlan::validate(&key, profile(Envelope::Ordinary), limits),
    Err(VerifierError::Limit { resource: "proof values", .. })
  ));
}

#[test]
fn key_transport_constants_and_implementation_equivalence() {
  let (system, pk) = setup();
  let key = VerifierKey::from_system(&system);
  let encoded = key.to_bytes().unwrap();
  let decoded = VerifierKey::from_bytes(&encoded).unwrap();
  assert_eq!(key.fingerprint().unwrap(), decoded.fingerprint().unwrap());
  assert_eq!(decoded.to_bytes().unwrap(), encoded);
  for mut bad in [encoded[..encoded.len() / 2].to_vec(), encoded.clone()] {
    bad.push(0xff);
    assert!(VerifierKey::from_bytes(&bad).is_err());
  }
  let plan = VerifierPlan::validate(
    &decoded,
    profile(Envelope::Ordinary),
    VerifierLimits::default(),
  )
  .unwrap();
  let value = Val::from_u8(31);
  let claims = vec![vec![value]];
  let proof = system.prove(&pk, &claims[0], trace(&system, value));
  let schema = Statement {
    claims: vec![vec![StatementSlot::Constant(value)]],
    messages: vec![],
  };
  let id = plan.identity(&schema).unwrap();
  let different = Statement {
    claims: vec![vec![StatementSlot::Constant(value + Val::ONE)]],
    messages: vec![],
  };
  assert_ne!(id, plan.identity(&different).unwrap());
  for compact_blake3 in [false, true] {
    let (c, i) = plan
      .build(schema.clone(), ImplementationOptions { compact_blake3 })
      .unwrap();
    let expanded = plan
      .expand_witness(ProofEnvelope::Ordinary {
        proof: &proof,
        claims: &claims,
      })
      .unwrap();
    let mut w = c.witness();
    i.assign_statement(
      &mut w,
      &Statement { claims: claims.clone(), messages: vec![] },
    )
    .unwrap();
    expanded.assign_proof(&mut w, &i).unwrap();
    assert!(w.generate().unwrap().public_values().is_empty());
    let bad =
      system.prove(&pk, &[value + Val::ONE], trace(&system, value + Val::ONE));
    let bad_claims = vec![vec![value + Val::ONE]];
    let bad_expanded = plan
      .expand_witness(ProofEnvelope::Ordinary {
        proof: &bad,
        claims: &bad_claims,
      })
      .unwrap();
    let mut w = c.witness();
    bad_expanded.assign_proof(&mut w, &i).unwrap();
    assert!(w.generate().is_err());
  }
  let mut altered = setup().0;
  altered.circuits[0].graph.nodes.push(multi_stark::graph::Node::Public(8));
  altered.circuits[0].graph.degrees.push(0);
  let key = VerifierKey::new(altered);
  assert!(matches!(
    VerifierPlan::validate(
      &key,
      profile(Envelope::Ordinary),
      VerifierLimits::default()
    ),
    Err(VerifierError::Circuit { field: "public index", .. })
  ));
}

#[allow(dead_code)]
#[path = "support/root_profile.rs"]
mod root;
#[test]
fn generic_plan_handles_sparse_mixed_heights_and_grinding() {
  let profile = root::Profile::Smoke;
  let (system, key) =
    System::new(profile.config(), root::circuit_inputs(profile));
  let vk = VerifierKey::from_system(&system);
  let plan = VerifierPlan::validate(
    &vk,
    ProofProfile {
      envelope: Envelope::Ordinary,
      active: root::ACTIVE.to_vec(),
      log_degrees: profile.logs(),
      claim_lengths: vec![18],
      message_lengths: vec![],
      max_field_retries: 2,
    },
    VerifierLimits::default(),
  )
  .unwrap();
  let (c, inputs) = plan
    .build(
      Statement {
        claims: vec![vec![StatementSlot::Public; 18]],
        messages: vec![],
      },
      ImplementationOptions::default(),
    )
    .unwrap();
  for subject in [[0x5a; 32], [0xa5; 32]] {
    let claim = root::claim(subject);
    let proof = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(root::traces(profile, subject), &system),
    );
    system.verify(&claim, &proof).unwrap();
    let statement = Statement { claims: vec![claim], messages: vec![] };
    let p = plan
      .expand_witness(ProofEnvelope::Ordinary {
        proof: &proof,
        claims: &statement.claims,
      })
      .unwrap();
    let mut w = c.witness();
    inputs.assign_statement(&mut w, &statement).unwrap();
    p.assign_proof(&mut w, &inputs).unwrap();
    w.generate().unwrap();
    let mut wrong = proof.clone();
    wrong.active[1] = true;
    assert!(
      plan
        .expand_witness(ProofEnvelope::Ordinary {
          proof: &wrong,
          claims: &statement.claims
        })
        .is_err()
    );
  }
}

#[test]
fn statement_modes_and_keys_are_bound() {
  let (system, pk) = setup();
  let value = Val::from_u8(13);
  let claim = vec![value];
  let ordinary = system.prove(&pk, &claim, trace(&system, value));
  let batch = system.prove_batch(
    &pk,
    vec![ShardInput { claims: vec![], witness: trace(&system, value) }],
    vec![BatchMessage::push(claim.clone())],
  );
  let key = VerifierKey::from_system(&system);
  let plan = VerifierPlan::validate(
    &key,
    profile(Envelope::SingleBatch),
    VerifierLimits::default(),
  )
  .unwrap();
  assert!(
    plan
      .expand_witness(ProofEnvelope::Ordinary {
        proof: &ordinary,
        claims: std::slice::from_ref(&claim)
      })
      .is_err()
  );
  for dynamic in [false, true] {
    let slot = |v| {
      if dynamic { StatementSlot::Public } else { StatementSlot::Constant(v) }
    };
    let schema = Statement {
      claims: vec![],
      messages: vec![Message {
        args: vec![slot(value)],
        multiplicity: slot(Val::ONE),
      }],
    };
    let (c, i) = plan.build(schema, ImplementationOptions::default()).unwrap();
    println!("Batch binding dynamic={dynamic}: {:?}", c.stats());
    let prepared =
      plan.expand_witness(ProofEnvelope::SingleBatch(&batch)).unwrap();
    let mut w = c.witness();
    i.assign_statement(
      &mut w,
      &Statement {
        claims: vec![],
        messages: vec![Message { args: vec![value], multiplicity: Val::ONE }],
      },
    )
    .unwrap();
    prepared.assign_proof(&mut w, &i).unwrap();
    w.generate().unwrap();
  }
  let plan = VerifierPlan::validate(
    &key,
    profile(Envelope::Ordinary),
    VerifierLimits::default(),
  )
  .unwrap();
  assert!(plan.expand_witness(ProofEnvelope::SingleBatch(&batch)).is_err());
  let schema =
    Statement { claims: vec![vec![StatementSlot::Public]], messages: vec![] };
  let (c, i) =
    plan.build(schema.clone(), ImplementationOptions::default()).unwrap();
  let mut other = setup().0;
  other.preprocessed_commit =
    Some(multi_stark::types::Commitment::from(vec![[0u8; 32]]));
  let other = VerifierKey::new(other);
  let wrong_plan = VerifierPlan::validate(
    &other,
    profile(Envelope::Ordinary),
    VerifierLimits::default(),
  )
  .unwrap();
  assert_ne!(
    plan.identity(&schema).unwrap(),
    wrong_plan.identity(&schema).unwrap()
  );
  if let Ok(p) = wrong_plan.expand_witness(ProofEnvelope::Ordinary {
    proof: &ordinary,
    claims: std::slice::from_ref(&claim),
  }) {
    assert!(
      p.assign_proof(&mut c.witness(), &i).is_err(),
      "cannot mix plan assignment"
    );
    let (wrong_c, wrong_i) =
      wrong_plan.build(schema, ImplementationOptions::default()).unwrap();
    let mut w = wrong_c.witness();
    wrong_i
      .assign_statement(
        &mut w,
        &Statement { claims: vec![claim], messages: vec![] },
      )
      .unwrap();
    p.assign_proof(&mut w, &wrong_i).unwrap();
    assert!(
      w.generate().is_err(),
      "native proof must not validate under another key"
    );
  }
}

#[test]
fn height_one_only_profile_checks_zero_round_fri() {
  let (system, pk) = System::new(
    config(),
    [CircuitInputs {
      main_width: 1,
      preprocessed: Some(RowMajorMatrix::new(vec![Val::ONE], 1)),
      lookups: vec![Lookup {
        multiplicity: -Expr::preprocessed(0),
        args: vec![Expr::main(0)],
      }],
      ..CircuitInputs::default()
    }],
  );
  let value = Val::from_u8(7);
  let claims = vec![vec![value]];
  let proof = system.prove(
    &pk,
    &claims[0],
    SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new(vec![value], 1)],
      &system,
    ),
  );
  system.verify(&claims[0], &proof).unwrap();
  assert!(proof.opening_proof.commit_phase_commits.is_empty());
  let key = VerifierKey::from_system(&system);
  let mut p = profile(Envelope::Ordinary);
  p.log_degrees[0] = 0;
  let plan =
    VerifierPlan::validate(&key, p, VerifierLimits::default()).unwrap();
  let (c, i) = plan
    .build(
      Statement { claims: vec![vec![StatementSlot::Public]], messages: vec![] },
      ImplementationOptions::default(),
    )
    .unwrap();
  let prepared = plan
    .expand_witness(ProofEnvelope::Ordinary { proof: &proof, claims: &claims })
    .unwrap();
  let mut w = c.witness();
  i.assign_statement(
    &mut w,
    &Statement { claims: claims.clone(), messages: vec![] },
  )
  .unwrap();
  prepared.assign_proof(&mut w, &i).unwrap();
  w.generate().unwrap();
  let mut bad = proof;
  bad.opening_proof.final_poly[0] += multi_stark::types::ExtVal::ONE;
  if let Ok(prepared) = plan
    .expand_witness(ProofEnvelope::Ordinary { proof: &bad, claims: &claims })
  {
    let mut w = c.witness();
    i.assign_statement(&mut w, &Statement { claims, messages: vec![] })
      .unwrap();
    prepared.assign_proof(&mut w, &i).unwrap();
    assert!(w.generate().is_err());
  }
}

#[test]
fn complete_helpers_cannot_drop_queries_through_modified_shape() {
  let (system, pk) = setup();
  let value = Val::from_u8(13);
  let claims = vec![vec![value]];
  let ordinary = system.prove(&pk, &claims[0], trace(&system, value));
  let batch = system.prove_batch(
    &pk,
    vec![ShardInput { claims: claims.clone(), witness: trace(&system, value) }],
    vec![],
  );
  for envelope in [Envelope::Ordinary, Envelope::SingleBatch] {
    let mut shape = FixedPcsShape::new(&system, 1);
    // Public shape fields are redundant metadata, never permission to
    // weaken the protocol selected by the trusted system configuration.
    shape.queries = 0;
    let mut builder = CircuitBuilder::new();
    builder.enable_compact_blake3();
    let claim = builder.public_input("claim");
    let bytes = ByteGadgets::new(&mut builder);
    let inputs = match envelope {
      Envelope::Ordinary => constrain_fixed_verifier(
        &mut builder,
        &bytes,
        &system,
        &shape,
        vec![vec![claim]],
      ),
      Envelope::SingleBatch => constrain_single_batch_verifier(
        &mut builder,
        &bytes,
        &system,
        &shape,
        vec![vec![claim]],
        &[],
      ),
    };
    let circuit = builder.finish();
    let expanded = match envelope {
      Envelope::Ordinary => {
        expand_pcs_witness(&system, &inputs.shape, &ordinary, &[&claims[0]])
      },
      Envelope::SingleBatch => {
        expand_single_batch_witness(&system, &inputs.shape, &batch, &[])
      },
    }
    .unwrap();
    let mut witness = circuit.witness();
    expanded.assign(&mut witness, &inputs).unwrap();
    witness.generate().unwrap();
    for query in 0..system.config.fri_parameters().num_queries {
      let mut bad = expanded.clone();
      bad.proof.opening_proof.input_openings[0].opened_values[query][0][0] +=
        Val::ONE;
      let mut witness = circuit.witness();
      bad.assign(&mut witness, &inputs).unwrap();
      assert!(
        witness.generate().is_err(),
        "{envelope:?}: omitted query {query}"
      );
    }
    assert_eq!(
      inputs.pcs.queries.len(),
      system.config.fri_parameters().num_queries
    );
  }
}

#[test]
fn profile_enforces_native_quotient_domain_bound() {
  let x = Expr::main(0);
  let (system, pk) = System::new(
    config(),
    [
      CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; 2])),
        ..Default::default()
      },
      CircuitInputs {
        main_width: 1,
        constraints: vec![x.clone() * x.clone() * x.clone() - x],
        ..Default::default()
      },
    ],
  );
  assert_eq!(system.circuits[1].quotient_degree(), 2);
  let mut proof = system.prove_multiple_claims(
    &pk,
    &[],
    SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new_col(vec![Val::ZERO; 2]); 2],
      &system,
    ),
  );
  system.verify_multiple_claims(&[], &proof).unwrap();
  proof.log_degrees[1] = 30;
  assert!(matches!(
    system.verify_shape(&proof),
    Err(multi_stark::verifier::VerificationError::InvalidProofShape)
  ));
  let key = VerifierKey::from_system(&system);
  let profile = ProofProfile {
    envelope: Envelope::Ordinary,
    active: vec![true, true],
    log_degrees: vec![1, 30], // LDE fits 2^32, but quotient exceeds native limit 2^30.
    claim_lengths: vec![],
    message_lengths: vec![],
    max_field_retries: 0,
  };
  assert!(
    VerifierPlan::validate(&key, profile, VerifierLimits::default()).is_err()
  );
  assert!(
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      FixedPcsShape::from_profile(&system, &[true, true], &[1, 30])
    }))
    .is_err()
  );
}
