//! Fixed-profile proof transport. The verifier supplies the system and heights;
//! this codec omits their redundant shape metadata, not cryptographic checks.

#[cfg(test)]
use crate::foreign::KzgCircuitExt;

use ark_bls12_381::G1Affine;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use super::KzgCommitment;
use super::KzgConfig;
use super::KzgProof;
use super::Scalar;
use multi_stark::config::ProofConfig;
use multi_stark::prover::Commitments;
use multi_stark::prover::Proof;
use multi_stark::system::System;
use multi_stark::traits::Algebra;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CompactProofError;

impl std::fmt::Display for CompactProofError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_str("invalid compact KZG proof or profile")
  }
}
impl std::error::Error for CompactProofError {}

/// Balanced ordinary proofs with all circuits active. Authenticate the system/profile separately and
/// run normal proof verification after decoding; decoding is not verification.
pub struct FixedProofCodec {
  template: Proof<KzgConfig>,
  max_openings: usize,
  body_bytes: usize,
}

impl FixedProofCodec {
  pub fn new(
    system: &System<KzgConfig>,
    log_degrees: &[u8],
  ) -> Result<Self, CompactProofError> {
    if log_degrees.len() != system.circuits.len() || log_degrees.is_empty() {
      return Err(CompactProofError);
    }
    let max_log = system.config.max_log_degree();
    let mut commitments = [
      KzgCommitment(vec![], vec![]),
      KzgCommitment(vec![], vec![]),
      KzgCommitment(vec![], vec![]),
    ];
    let mut rounds = [vec![], vec![], vec![], vec![]];
    let mut heights = Vec::new();
    for (ci, (c, &log)) in system.circuits.iter().zip(log_degrees).enumerate() {
      let height =
        1usize.checked_shl(u32::from(log)).ok_or(CompactProofError)?;
      if usize::from(log) > max_log
        || (c.preprocessed_width != 0 && c.preprocessed_height != height)
      {
        return Err(CompactProofError);
      }
      if !heights.contains(&log) {
        heights.push(log);
      }
      for (i, width) in [c.main_width, c.stage_2_width, c.quotient_degree()]
        .into_iter()
        .enumerate()
      {
        commitments[i].0.push(vec![G1Affine::default(); width]);
        commitments[i].1.push(vec![
          G1Affine::default();
          if usize::from(log) < max_log {
            width
          } else {
            0
          }
        ]);
        let count = match i {
          0 => {
            1 + usize::from(
              system.opens_next_row(ci, multi_stark::expr::Source::Main),
            )
          },
          1 => 2,
          _ => 1,
        };
        rounds[i].push(vec![vec![Scalar::ZERO; width]; count]);
      }
      if c.preprocessed_width != 0 {
        rounds[3].push(vec![
          vec![Scalar::ZERO; c.preprocessed_width];
          1 + usize::from(system.opens_next_row(
            ci,
            multi_stark::expr::Source::Preprocessed
          ))
        ]);
      }
    }
    let [stage_1_trace, stage_2_trace, quotient_chunks] = commitments;
    let [
      stage_1_opened_values,
      stage_2_opened_values,
      quotient_opened_values,
      prep,
    ] = rounds;
    let template = Proof {
      active: vec![true; log_degrees.len()],
      log_degrees: log_degrees.to_vec(),
      commitments: Commitments {
        stage_1_trace,
        stage_2_trace,
        quotient_chunks,
      },
      intermediate_accumulators: vec![Scalar::ZERO; log_degrees.len()],
      opening_proof: KzgProof(vec![]),
      stage_1_opened_values,
      stage_2_opened_values,
      quotient_opened_values,
      preprocessed_opened_values: system
        .preprocessed_commit
        .as_ref()
        .map(|_| prep),
    };
    let body_bytes =
      points(&template).count() * 48 + fields(&template).count() * 32;
    Ok(Self { template, max_openings: heights.len() + 1, body_bytes })
  }

  pub fn encode(
    &self,
    proof: &Proof<KzgConfig>,
  ) -> Result<Vec<u8>, CompactProofError> {
    if proof.active != self.template.active
      || proof.log_degrees != self.template.log_degrees
      || proof.intermediate_accumulators.last() != Some(&Scalar::ZERO)
      || shape(proof) != shape(&self.template)
      || proof.opening_proof.0.is_empty()
      || proof.opening_proof.0.len() > self.max_openings
    {
      return Err(CompactProofError);
    }
    let mut bytes = b"KQP1".to_vec();
    bytes.push(
      u8::try_from(proof.opening_proof.0.len())
        .map_err(|_error| CompactProofError)?,
    );
    for point in points(proof) {
      point
        .serialize_compressed(&mut bytes)
        .map_err(|_error| CompactProofError)?;
    }
    for field in fields(proof) {
      field
        .0
        .serialize_compressed(&mut bytes)
        .map_err(|_error| CompactProofError)?;
    }
    Ok(bytes)
  }

  pub fn decode(
    &self,
    bytes: &[u8],
  ) -> Result<Proof<KzgConfig>, CompactProofError> {
    if bytes.len() < 5 || &bytes[..4] != b"KQP1" {
      return Err(CompactProofError);
    }
    let openings = usize::from(bytes[4]);
    if openings == 0
      || openings > self.max_openings
      || bytes.len() != 5 + self.body_bytes + 48 * openings
    {
      return Err(CompactProofError);
    }
    let mut proof = self.template.clone();
    proof.opening_proof.0.resize(openings, G1Affine::default());
    let mut input = &bytes[5..];
    for commitment in [
      &mut proof.commitments.stage_1_trace,
      &mut proof.commitments.stage_2_trace,
      &mut proof.commitments.quotient_chunks,
    ] {
      for point in commitment.0.iter_mut().chain(&mut commitment.1).flatten() {
        *point = G1Affine::deserialize_compressed(&mut input)
          .map_err(|_error| CompactProofError)?;
      }
    }
    for point in &mut proof.opening_proof.0 {
      *point = G1Affine::deserialize_compressed(&mut input)
        .map_err(|_error| CompactProofError)?;
    }
    let accumulator_count = proof.intermediate_accumulators.len() - 1;
    for value in
      proof.intermediate_accumulators.iter_mut().take(accumulator_count).chain(
        [
          &mut proof.stage_1_opened_values,
          &mut proof.stage_2_opened_values,
          &mut proof.quotient_opened_values,
        ]
        .into_iter()
        .chain(proof.preprocessed_opened_values.as_mut())
        .flatten()
        .flatten()
        .flatten(),
      )
    {
      value.0 = ark_bls12_381::Fr::deserialize_compressed(&mut input)
        .map_err(|_error| CompactProofError)?;
    }
    if !input.is_empty() {
      return Err(CompactProofError);
    }
    Ok(proof)
  }
}

fn points(proof: &Proof<KzgConfig>) -> impl Iterator<Item = &G1Affine> {
  [
    &proof.commitments.stage_1_trace,
    &proof.commitments.stage_2_trace,
    &proof.commitments.quotient_chunks,
  ]
  .into_iter()
  .flat_map(|c| c.0.iter().chain(&c.1).flatten())
  .chain(&proof.opening_proof.0)
}

fn fields(proof: &Proof<KzgConfig>) -> impl Iterator<Item = &Scalar> {
  proof
    .intermediate_accumulators
    .iter()
    .take(proof.intermediate_accumulators.len().saturating_sub(1))
    .chain(
      [
        &proof.stage_1_opened_values,
        &proof.stage_2_opened_values,
        &proof.quotient_opened_values,
      ]
      .into_iter()
      .chain(proof.preprocessed_opened_values.as_ref())
      .flatten()
      .flatten()
      .flatten(),
    )
}

fn shape(proof: &Proof<KzgConfig>) -> Vec<usize> {
  let mut shape = vec![
    proof.intermediate_accumulators.len(),
    usize::from(proof.preprocessed_opened_values.is_some()),
  ];
  for c in [
    &proof.commitments.stage_1_trace,
    &proof.commitments.stage_2_trace,
    &proof.commitments.quotient_chunks,
  ] {
    for matrices in [&c.0, &c.1] {
      shape.push(matrices.len());
      shape.extend(matrices.iter().map(Vec::len));
    }
  }
  for round in [
    &proof.stage_1_opened_values,
    &proof.stage_2_opened_values,
    &proof.quotient_opened_values,
  ]
  .into_iter()
  .chain(proof.preprocessed_opened_values.as_ref())
  {
    shape.push(round.len());
    for matrix in round {
      shape.push(matrix.len());
      shape.extend(matrix.iter().map(Vec::len));
    }
  }
  shape
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::expr::Expr;
  use multi_stark::system::CircuitInputs;
  use multi_stark::system::SystemWitness;
  use multi_stark::traits::Field;
  use p3_matrix::dense::RowMajorMatrix;
  use std::sync::Arc;

  #[test]
  fn merged_tables_do_not_allow_cross_table_substitution() {
    use multi_stark::plonkish::CircuitBuilder;
    let mut b = CircuitBuilder::<Scalar>::new();
    let a = b.fixed_table("a", vec![vec![Scalar::ONE]]);
    b.fixed_table("b", vec![vec![Scalar::ONE]]);
    let one = b.constant(Scalar::ONE);
    b.lookup(a, &[one]);
    let compiled = b
      .finish()
      .lower_to_multi_stark(Scalar::from_u8(93))
      .unwrap()
      .merge_table_traces(16)
      .unwrap();
    let assignment = compiled.witness().generate().unwrap();
    let (system, key) = System::new(
      KzgConfig::new(
        Arc::new(super::super::Srs::unsafe_dev_setup(16, b"table-ids")),
        4,
      ),
      compiled.kzg_circuit_inputs(16, 4).unwrap(),
    );
    let claims = compiled.claims(&[]).unwrap();
    let claims: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let mut traces = compiled.traces(&assignment).unwrap();
    let proof = system.prove_multiple_claims(
      &key,
      &claims,
      SystemWitness::from_stage_1(traces.clone(), &system),
    );
    system.verify_multiple_claims(&claims, &proof).unwrap();
    assert_eq!(traces[1].values, [Scalar::ONE, Scalar::ZERO]);
    // The tuple is identical, but paying through the other table is invalid.
    traces[1].values.swap(0, 1);
    let forged = system.prove_multiple_claims(
      &key,
      &claims,
      SystemWitness::from_stage_1(traces, &system),
    );
    assert!(system.verify_multiple_claims(&claims, &forged).is_err());
  }

  #[test]
  fn roundtrip_and_reject_malformed_transport() {
    let f = Scalar::from_u8;
    let (system, key) = System::new(
      KzgConfig::new(
        Arc::new(super::super::Srs::unsafe_dev_setup(8, b"codec")),
        4,
      ),
      [CircuitInputs {
        main_width: 1,
        constraints: vec![Expr::main(0) - Expr::constant(f(7))],
        ..Default::default()
      }],
    );
    let proof = system.prove_multiple_claims(
      &key,
      &[],
      SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new_col(vec![f(7); 4])],
        &system,
      ),
    );
    let codec = FixedProofCodec::new(&system, &[2]).unwrap();
    let bytes = codec.encode(&proof).unwrap();
    let decoded = codec.decode(&bytes).unwrap();
    assert_eq!(decoded.to_bytes().unwrap(), proof.to_bytes().unwrap());
    system.verify_multiple_claims(&[], &decoded).unwrap();
    assert!(bytes.len() < proof.to_bytes().unwrap().len());
    for end in 0..bytes.len() {
      assert!(codec.decode(&bytes[..end]).is_err());
    }
    let mut bad = bytes.clone();
    bad.push(0);
    assert!(codec.decode(&bad).is_err());
    bad = bytes.clone();
    bad[5..53].fill(0xff);
    assert!(codec.decode(&bad).is_err());
    bad = bytes.clone();
    let n = bad.len();
    bad[n - 32..].fill(0xff);
    assert!(codec.decode(&bad).is_err());
    let mut bad_proof = proof.clone();
    bad_proof.stage_1_opened_values[0][0].clear();
    assert!(codec.encode(&bad_proof).is_err());
    bad_proof = proof.clone();
    bad_proof.active[0] = false;
    assert!(codec.encode(&bad_proof).is_err());
    bad_proof = proof.clone();
    bad_proof.intermediate_accumulators[0] = Scalar::ONE;
    assert!(codec.encode(&bad_proof).is_err());
    bad_proof = proof.clone();
    bad_proof.stage_1_opened_values[0][0][0] += Scalar::ONE;
    let forged = codec.decode(&codec.encode(&bad_proof).unwrap()).unwrap();
    assert!(system.verify_multiple_claims(&[], &forged).is_err());
  }
}
