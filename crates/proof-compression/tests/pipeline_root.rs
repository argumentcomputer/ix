//! Generated aggregate-shaped statements, including multi-shard Aiur batches.
use aiur::vk_codec::{AiurVerifyingKey, to_bytes};
use ix_proof_compression::pipeline::prepare_root;
use multi_stark::batch::ShardInput;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use multi_stark::types::{
  CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val,
};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

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
