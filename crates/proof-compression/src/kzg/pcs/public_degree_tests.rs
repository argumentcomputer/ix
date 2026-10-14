use super::KzgPcs;
use crate::kzg::{KzgConfig, Scalar, Srs};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  prover::{Commitments, Proof, observe_claims, sample_lookup_challenges},
  system::{CircuitInputs, System},
  traits::{Algebra, EvaluationDomain, Field, Pcs, Transcript, TwoAdicField},
  verifier::VerificationError,
};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;

fn high_degree_air_proof(
  constant: Scalar,
) -> (System<KzgConfig>, Proof<KzgConfig>) {
  let srs = Arc::new(Srs::unsafe_dev_setup(8, b"high-degree-air"));
  let pcs = KzgPcs::new(srs.clone(), 1);
  let (system, _) = System::new(
    KzgConfig::with_max_trace_len(srs, 2, 1),
    [CircuitInputs {
      main_width: 1,
      constraints: vec![Expr::main(0)],
      ..Default::default()
    }],
  );
  assert_eq!(system.circuits[0].constraint_count(), 2);
  let trace_domain = pcs.natural_domain_for_degree(2);
  let polynomial_domain = pcs.natural_domain_for_degree(4);
  let (main, mut main_data) = pcs.commit(vec![(
    polynomial_domain,
    RowMajorMatrix::new_col(
      (0..4)
        .map(|i| Scalar::two_adic_generator(2).exp_u64(i))
        .map(|x| x * x + constant)
        .collect(),
    ),
  )]);
  // A malicious committer can use public powers beyond the trace height.
  main_data.matrices[0].domain = trace_domain;
  let (stage2, stage2_data) = pcs.commit(vec![(
    trace_domain,
    RowMajorMatrix::new_col(vec![Scalar::ZERO; 2]),
  )]);

  let mut transcript = system.config.initialise_challenger();
  system.observe_shape(&mut transcript);
  transcript.observe_field(Scalar::ONE);
  transcript.observe_commitment(main.clone());
  transcript.observe_field(Scalar::ONE);
  observe_claims::<KzgConfig>(&mut transcript, &[]);
  sample_lookup_challenges::<KzgConfig>(&mut transcript);
  transcript.observe_commitment(stage2.clone());
  transcript.observe_challenge(Scalar::ZERO);
  let alpha = transcript.sample_challenge();
  let (quotient, quotient_data) =
    pcs.commit(vec![(trace_domain, RowMajorMatrix::new_col(vec![alpha; 2]))]);
  transcript.observe_commitment(quotient.clone());
  let zeta = transcript.sample_challenge();
  let (opened, opening_proof) = pcs.open(
    vec![
      (&main_data, vec![vec![zeta]]),
      (&stage2_data, vec![vec![zeta, trace_domain.next_point(zeta)]]),
      (&quotient_data, vec![vec![zeta]]),
    ],
    &mut transcript,
  );
  let mut opened = opened.into_iter();
  let proof = Proof {
    active: vec![true],
    commitments: Commitments {
      stage_1_trace: main,
      stage_2_trace: stage2,
      quotient_chunks: quotient,
    },
    intermediate_accumulators: vec![Scalar::ZERO],
    log_degrees: vec![1],
    opening_proof,
    stage_1_opened_values: opened.next().unwrap(),
    stage_2_opened_values: opened.next().unwrap(),
    quotient_opened_values: opened.next().unwrap(),
    preprocessed_opened_values: None,
  };
  (system, proof)
}

#[test]
fn public_degree_air_accepts_a_high_degree_domain_vanishing_polynomial() {
  let (system, proof) = high_degree_air_proof(Scalar::NEG_ONE);
  system.verify_multiple_claims(&[], &proof).unwrap();
}

#[test]
fn public_degree_air_rejects_invalid_rows_with_valid_high_degree_openings() {
  let (system, proof) = high_degree_air_proof(Scalar::ZERO);
  assert!(matches!(
    system.verify_multiple_claims(&[], &proof),
    Err(VerificationError::OodEvaluationMismatch)
  ));
}
