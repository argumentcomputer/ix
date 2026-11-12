use aiur::field::FieldBackend;
use ark_bn254::{G1Affine, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::Zero;
use ix_proof_compression::{
  aiur_backend::{Bn254, kzg::Proof},
  kzg::{KzgConfig, Scalar},
};
use multi_stark::{
  config::ProofConfig,
  prover::{observe_claims, sample_lookup_challenges},
  system::System,
  traits::{Transcript, TwoAdicField},
};

/// Replay native transcript methods and the PCS's group arithmetic directly.
/// This is a test reference, never an advice provider to the Aiur verifier.
pub(super) fn accumulator(
  system: &System<KzgConfig>,
  proof: &Proof,
  claims: &[Vec<Scalar>],
  generator: G1Affine,
) -> [G1Affine; 2] {
  let mut transcript = system.config.initialise_challenger();
  system.observe_shape(&mut transcript);
  for &active in &proof.active {
    transcript.observe_field(Bn254.from_u64(u64::from(active)));
  }
  if let Some(fixed) = &system.preprocessed_commit {
    transcript.observe_commitment(fixed.clone());
  }
  transcript.observe_commitment(proof.commitments.stage_1_trace.clone());
  for &log in &proof.log_degrees {
    transcript.observe_field(Bn254.from_u64(u64::from(log)));
  }
  let claims: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  observe_claims::<KzgConfig>(&mut transcript, &claims);
  sample_lookup_challenges::<KzgConfig>(&mut transcript);
  transcript.observe_commitment(proof.commitments.stage_2_trace.clone());
  for &value in &proof.intermediate_accumulators {
    transcript.observe_challenge(value);
  }
  let _alpha = transcript.sample_challenge();
  transcript.observe_commitment(proof.commitments.quotient_chunks.clone());
  let zeta = transcript.sample_challenge();
  let mut rounds = vec![
    (
      &proof.commitments.stage_1_trace,
      proof.log_degrees.clone(),
      &proof.stage_1_opened_values,
    ),
    (
      &proof.commitments.stage_2_trace,
      proof.log_degrees.clone(),
      &proof.stage_2_opened_values,
    ),
    (
      &proof.commitments.quotient_chunks,
      proof.log_degrees.clone(),
      &proof.quotient_opened_values,
    ),
  ];
  if let Some(fixed) = &system.preprocessed_commit {
    let logs = system
      .circuits
      .iter()
      .filter(|c| c.preprocessed_width != 0)
      .map(|c| u8::try_from(c.preprocessed_height.ilog2()).unwrap())
      .collect();
    rounds.push((
      fixed,
      logs,
      proof.preprocessed_opened_values.as_ref().unwrap(),
    ));
  }
  for (commitment, logs, _) in &rounds {
    transcript.observe_commitment((*commitment).clone());
    for &log in logs {
      transcript.observe_canonical(&u64::from(log));
    }
  }
  let mut batches: Vec<(Scalar, Vec<G1Affine>, Vec<Scalar>)> = vec![];
  for (commitment, logs, openings) in &rounds {
    for ((points, &log), rows) in commitment.0.iter().zip(logs).zip(*openings) {
      for (i, row) in rows.iter().enumerate() {
        for &value in row {
          transcript.observe_challenge(value);
        }
        let point = zeta
          * if i == 0 {
            Bn254.one()
          } else {
            Scalar::two_adic_generator(usize::from(log))
          };
        let index =
          if let Some(index) = batches.iter().position(|b| b.0 == point) {
            index
          } else {
            batches.push((point, vec![], vec![]));
            batches.len() - 1
          };
        batches[index].1.extend(points);
        batches[index].2.extend(row);
      }
    }
  }
  assert_eq!(batches.len(), proof.opening_proof.0.len());
  let v = transcript.sample_challenge();
  for point in &proof.opening_proof.0 {
    transcript.observe_canonical(point);
  }
  let r = transcript.sample_challenge();
  let mut left = G1Projective::zero();
  let mut right = G1Projective::zero();
  let mut weight = Bn254.one();
  for ((z, points, values), &witness) in
    batches.into_iter().zip(&proof.opening_proof.0)
  {
    let mut combined = G1Projective::zero();
    let mut expected = Bn254.zero();
    let mut power = Bn254.one();
    for (point, value) in points.into_iter().zip(values) {
      combined += point * power.0;
      expected += power * value;
      power *= v;
    }
    left += (combined - generator * expected.0 + witness * z.0) * weight.0;
    right -= witness * weight.0;
    weight *= r;
  }
  [left.into_affine(), right.into_affine()]
}
