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
  let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
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
  let key = AiurVerifyingKey::from_bytes(&to_bytes(&system, cp, fp)).unwrap();
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
