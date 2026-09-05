//! Small native proofs for specialization and verifier-boundary regressions.

use aiur::vk_codec::aiur_config_system_to_bytes;
use ix_terminal::ValidatedStage2RootV1;
use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val},
};

/// Two interchangeable circuits under one key. A zero height makes a circuit
/// inactive; the first active circuit consumes the claim exactly once.
pub(crate) fn interchangeable_root(
  heights: [usize; 2],
  claim_seed: u64,
) -> ValidatedStage2RootV1 {
  let commitment = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fri = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 2,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let circuit = || CircuitInputs {
    main_width: 19,
    lookups: vec![Lookup::pull(
      Expr::main(0),
      (1..=18).map(Expr::main).collect(),
    )],
    ..Default::default()
  };
  let (system, key) = System::new(
    GoldilocksBlake3Config::new(commitment, fri),
    [circuit(), circuit()],
  );
  let claim: Vec<_> =
    (0..18).map(|word| Val::from_u64(claim_seed + word)).collect();
  let first_active = heights.iter().position(|&height| height != 0).unwrap();
  let traces = heights
    .into_iter()
    .enumerate()
    .map(|(index, height)| {
      let mut values = vec![Val::ZERO; height * 19];
      if index == first_active {
        values[0] = Val::ONE;
        values[1..19].copy_from_slice(&claim);
      }
      RowMajorMatrix::new(values, 19)
    })
    .collect();
  let proof =
    system.prove(&key, &claim, SystemWitness::from_stage_1(traces, &system));
  let vk = aiur_config_system_to_bytes(&system, commitment, fri);
  let claim_bytes: Vec<_> = claim
    .iter()
    .flat_map(|word| word.as_canonical_u64().to_le_bytes())
    .collect();
  crate::FlockStage3Backend
    .prepare_witness(&vk, &claim_bytes, &proof.to_bytes().unwrap(), &fri)
    .unwrap()
}
