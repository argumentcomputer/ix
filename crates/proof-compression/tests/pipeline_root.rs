//! Generated aggregate-shaped statements, including multi-shard Aiur batches.
use aiur::vk_codec::{AiurVerifyingKey, to_bytes};
use ix_proof_compression::kzg::Srs;
use ix_proof_compression::pipeline::{
  FixedRoot, FriVerifier, KzgVerifier, RecursiveVerifier, prepare_kzg,
  prepare_recursive, prepare_root, setup,
};
use multi_stark::batch::ShardInput;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use multi_stark::types::{
  CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;

fn root_system() -> (
  System<GoldilocksBlake3Config>,
  multi_stark::system::ProverKey<GoldilocksBlake3Config>,
  CommitmentParameters,
  FriParameters,
) {
  root_system_with_blowup(1)
}

fn root_system_with_blowup(
  log_blowup: usize,
) -> (
  System<GoldilocksBlake3Config>,
  multi_stark::system::ProverKey<GoldilocksBlake3Config>,
  CommitmentParameters,
  FriParameters,
) {
  let cp = CommitmentParameters { log_blowup, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 2,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  // A small relation carrying the same 18-word shape as an aggregate call.
  // Its trusted key accepts any values; the caller selects the expected claim.
  let (system, pk) = System::new(
    GoldilocksBlake3Config::new(cp, fp),
    [CircuitInputs {
      main_width: 19,
      preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; 2])),
      lookups: vec![Lookup::pull(
        Expr::main(18),
        (0..18).map(Expr::main).collect(),
      )],
      ..Default::default()
    }],
  );
  (system, pk, cp, fp)
}

#[test]
fn different_root_statements_and_trace_shard_counts() {
  let (system, pk, cp, fp) = root_system();
  let key_bytes = to_bytes(&system, cp, fp);
  let key = AiurVerifyingKey::from_bytes(&key_bytes).unwrap();
  for (seed, shards) in [(7, 1), (31, 2)] {
    let expected: Vec<_> = (0..18).map(|i| Val::from_u32(seed + i)).collect();
    let inputs = || {
      (0..shards)
        .map(|i| {
          let mut row = expected.clone();
          row.push(Val::from_bool(i == shards - 1));
          row.extend(vec![Val::ZERO; 19]);
          ShardInput {
            claims: if i == 0 { vec![expected.clone()] } else { vec![] },
            witness: SystemWitness::from_stage_1(
              vec![RowMajorMatrix::new(row, 19)],
              &system,
            ),
          }
        })
        .collect()
    };
    let proof = system.prove_batch(&pk, inputs(), vec![]);
    let stage =
      prepare_root(&key, &proof, &expected, Default::default()).unwrap();
    assert_eq!(stage.public_values(), expected);
    check_cli_root(
      &key_bytes,
      &proof,
      &expected,
      shards,
      stage.circuit().stats(),
    );
    let mut wrong = expected.clone();
    wrong[17] += Val::ONE;
    assert!(prepare_root(&key, &proof, &wrong, Default::default()).is_err());
    let mut bad = proof.clone();
    bad.proofs.pop();
    assert!(prepare_root(&key, &bad, &expected, Default::default()).is_err());
    // A balanced pair can satisfy the generic batch protocol but violate
    // Aiur's memory-closure policy. The public root API must reject it.
    let messages = vec![
      multi_stark::batch::BatchMessage::push(vec![Val::ONE]),
      multi_stark::batch::BatchMessage::pull(vec![Val::ONE]),
    ];
    let bad = system.prove_batch(&pk, inputs(), messages);
    system.verify_batch(&bad).unwrap();
    assert!(prepare_root(&key, &bad, &expected, Default::default()).is_err());
    let insufficient =
      prepare_root(&key, &proof, &expected, Default::default()).unwrap();
    assert!(
      insufficient
        .prove_fri(GoldilocksBlake3Config::new(cp, fp), 1 << 16)
        .is_err()
    );
    let (verifier, compressed) = stage
      .prove_fri(
        GoldilocksBlake3Config::new(
          CommitmentParameters { log_blowup: 2, cap_height: 0 },
          fp,
        ),
        1 << 16,
      )
      .unwrap();
    verifier.verify(&compressed, &expected).unwrap();
    assert!(verifier.verify(&compressed, &wrong).is_err());
  }
}

#[test]
fn shared_batch_root_preserves_single_batch_verifier_and_proof_bytes()
-> Result<(), Box<dyn std::error::Error>> {
  use ix_proof_compression::fri::{
    Envelope, ImplementationOptions, ProofEnvelope, ProofProfile, Statement,
    StatementBinding, VerifierKey, VerifierPlan,
  };
  use multi_stark::plonkish::CircuitBuilder;

  let (system, pk, cp, fp) = root_system_with_blowup(2);
  let key = AiurVerifyingKey::from_bytes(&to_bytes(&system, cp, fp))?;
  let expected: Vec<_> = (0..18).map(|i| Val::from_u32(41 + i)).collect();
  let mut row = expected.clone();
  row.push(Val::ONE);
  row.extend(vec![Val::ZERO; 19]);
  let proof = system.prove_batch(
    &pk,
    vec![ShardInput {
      claims: vec![expected.clone()],
      witness: SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new(row, 19)],
        &system,
      ),
    }],
    vec![],
  );
  let prepared = prepare_root(&key, &proof, &expected, Default::default())?;

  let verifier_key = VerifierKey::from_system(key.system());
  let header = &proof.preamble.headers[0];
  let plan = VerifierPlan::validate(
    &verifier_key,
    ProofProfile {
      envelope: Envelope::SingleBatch,
      active: header.active.clone(),
      log_degrees: header.log_degrees.clone(),
      claim_lengths: vec![expected.len()],
      message_lengths: vec![],
      max_field_retries: 2,
    },
    Default::default(),
  )?;
  let expanded = plan.expand_witness(ProofEnvelope::SingleBatch(&proof))?;
  let mut builder = CircuitBuilder::new();
  builder.enable_compact_blake3();
  let claims = vec![
    (0..expected.len())
      .map(|i| {
        StatementBinding::Wire(builder.public_input(format!("claim[0][{i}]")))
      })
      .collect(),
  ];
  let inputs = plan.constrain(
    &mut builder,
    Statement { claims, messages: vec![] },
    ImplementationOptions { compact_blake3: true },
  )?;
  let circuit = builder.finish();
  let mut witness = circuit.witness();
  inputs.assign_statement(
    &mut witness,
    &Statement { claims: vec![expected.clone()], messages: vec![] },
  )?;
  expanded.assign_proof(&mut witness, &inputs)?;
  let assignment = witness.generate()?;
  let compiled =
    circuit.lower_to_multi_stark_sharded(Val::from_u8(107), 1 << 24)?;
  let claims = compiled.claims(&expected)?;
  let template = compiled.claims(&vec![Val::ZERO; expected.len()])?;
  let traces = compiled.traces(&assignment)?;
  let mut definitions = compiled.circuit_inputs();
  for definition in &mut definitions {
    definition.lookup_group_size = 3;
  }
  drop(compiled);
  drop(assignment);
  let (reference, key) =
    System::new(GoldilocksBlake3Config::new(cp, fp), definitions);
  let proof = reference.prove_multiple_claims(
    &key,
    &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
    SystemWitness::from_stage_1(traces, &reference),
  );
  let reference_key = VerifierKey::from_system(&reference).to_bytes()?;
  let reference_proof = proof.to_bytes()?;
  drop(reference);

  let (verifier, proof) =
    prepared.prove_fri(GoldilocksBlake3Config::new(cp, fp), 1 << 24)?;
  type EncodedVerifier = (Vec<u8>, (Vec<Vec<Val>>, Vec<(usize, usize)>));
  let bytes = verifier.to_bytes()?;
  let ((key, (actual_template, locations)), consumed): (
    EncodedVerifier,
    usize,
  ) = bincode::serde::decode_from_slice(
    &bytes[8..],
    bincode::config::standard(),
  )?;
  assert_eq!(consumed, bytes.len() - 8);
  assert_eq!(key, reference_key);
  assert_eq!(actual_template, template);
  assert_eq!(
    locations,
    (1..=expected.len()).map(|i| (i, 3)).collect::<Vec<_>>()
  );
  assert_eq!(proof.to_bytes()?, reference_proof);
  Ok(())
}

fn check_cli_root(
  key: &[u8],
  proof: &aiur::synthesis::AiurProof,
  expected: &[Val],
  shards: usize,
  stats: multi_stark::plonkish::CircuitStats,
) {
  use ix_proof_compression::fri::*;
  use p3_field::PrimeField64;
  use std::fs;

  let directory = std::env::temp_dir()
    .join(format!("ix-cli-root-{}-{shards}", std::process::id()));
  fs::create_dir(&directory).unwrap();
  let result = (|| -> Result<(), Box<dyn std::error::Error>> {
    let input = directory.join("input");
    let output = directory.join("output");
    fs::create_dir(&input)?;
    fs::write(input.join("root-vk.bin"), key)?;
    fs::write(input.join("root-proof.bin"), proof.to_bytes()?)?;
    let mut claims = 1u64.to_le_bytes().to_vec();
    claims.extend((expected.len() as u64).to_le_bytes());
    for value in expected {
      claims.extend(value.as_canonical_u64().to_le_bytes());
    }
    fs::write(input.join("root-claims.bin"), claims)?;
    ix_proof_compression::pipeline::command(
      "fri",
      &[
        input.to_string_lossy().into_owned(),
        output.to_string_lossy().into_owned(),
        "--check-only".into(),
      ],
    )?;
    assert!(output.join("CHECKED").is_file());
    assert!(
      fs::read_to_string(output.join("circuit-cost.txt"))?
        .starts_with(&format!("Stats: {stats:?}\n"))
    );
    if shards == 1 {
      let key = AiurVerifyingKey::from_bytes(key)?;
      let key = VerifierKey::from_system(key.system());
      let header = &proof.preamble.headers[0];
      let plan = VerifierPlan::validate(
        &key,
        ProofProfile {
          envelope: Envelope::SingleBatch,
          active: header.active.clone(),
          log_degrees: header.log_degrees.clone(),
          claim_lengths: vec![expected.len()],
          message_lengths: vec![],
          max_field_retries: DEFAULT_FIELD_RETRIES,
        },
        Default::default(),
      )?;
      let identity = plan.identity(&Statement {
        claims: vec![vec![StatementSlot::Public; expected.len()]],
        messages: vec![],
      })?;
      assert_eq!(fs::read(output.join("plan-id.bin"))?, identity);
    }
    Ok(())
  })();
  fs::remove_dir_all(directory).unwrap();
  result.unwrap();
}

/// Runs all real compression circuits; expensive because it includes two KZG provers.
#[test]
#[ignore = "complete compression chain, including recursive KZG proving"]
fn complete_compression_chain() -> Result<(), Box<dyn std::error::Error>> {
  let (system, pk, cp, fp) = root_system();
  let key = AiurVerifyingKey::from_bytes(&to_bytes(&system, cp, fp))?;
  let height = 1 << 22;
  let srs =
    Arc::new(Srs::unsafe_dev_setup(height, b"complete-compression-test"));
  srs.validate()?;
  let fixed = FixedRoot::new(1, vec![], 18)?;
  let config = || {
    GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters { num_queries: 1, ..fp },
    )
  };
  eprintln!("deriving the local verifier without a proof");
  let local = setup(&key, &fixed, srs.clone(), config(), 1 << 20, height)?;
  let local_bytes = local.to_bytes()?;
  drop(local);
  eprintln!("local verifier ready; generating the root proof");
  let expected: Vec<_> = (0..18).map(|i| Val::from_u32(71 + i)).collect();
  let mut row = expected.clone();
  row.push(Val::ONE);
  row.extend(vec![Val::ZERO; 19]);
  let root = system.prove_batch(
    &pk,
    vec![ShardInput {
      claims: vec![expected.clone()],
      witness: SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new(row, 19)],
        &system,
      ),
    }],
    vec![],
  );
  let prepared = fixed.prepare(&key, &root, &expected, Default::default())?;
  eprintln!("root verifier: {:?}", prepared.circuit().stats());
  let (fri, proof) = prepared.prove_fri(config(), 1 << 20)?;
  let fri = FriVerifier::from_bytes(&fri.to_bytes()?)?;
  let prepared = prepare_kzg(&fri, &proof, &expected, Default::default())?;
  eprintln!("foreign verifier: {:?}", prepared.circuit().stats());
  let (kzg, proof) = prepared.prove_kzg(srs.clone(), height)?;
  let kzg = KzgVerifier::from_bytes(&kzg.to_bytes()?)?;
  eprintln!("foreign proof verified");
  let recursive = prepare_recursive(&kzg, &proof, &expected)?;
  eprintln!("recursive verifier: {:?}", recursive.circuit().stats());
  let (verifier, proof) = recursive.prove(srs, height)?;
  assert_eq!(verifier.to_bytes()?, local_bytes);
  let verifier = RecursiveVerifier::from_bytes(&local_bytes)?;
  verifier.verify(&proof, &expected)?;
  let bytes = verifier.encode_proof(&proof)?;
  verifier.verify_bytes(&bytes, &expected)?;
  let mut wrong = expected.clone();
  wrong[17] += Val::ONE;
  assert!(verifier.verify_bytes(&bytes, &wrong).is_err());
  let mut corrupt = bytes;
  let last = corrupt.len() - 1;
  corrupt[last] ^= 1;
  assert!(verifier.verify_bytes(&corrupt, &expected).is_err());
  Ok(())
}
