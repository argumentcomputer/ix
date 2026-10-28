use std::sync::Arc;

use ark_bn254::Fr;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ix_proof_compression::kzg::compact::FixedProofCodec;
use ix_proof_compression::kzg::curve::{G1Affine, G2Affine};
use ix_proof_compression::kzg::encoding::{read_scalars, write_scalars};
use ix_proof_compression::kzg::{
  KzgConfig, Scalar, Srs, TranscriptKind, VerifierParams,
};
use multi_stark::config::ProofConfig;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use multi_stark::traits::{Algebra, Field, TwoAdicField};
use p3_matrix::dense::RowMajorMatrix;

const HEIGHTS: [usize; 2] = [4, 8];
const QUOTIENT_DEGREE: usize = 4;
const SEED: &[u8] = b"bn254-kzg-integration";

fn claims() -> [[Scalar; 3]; 2] {
  HEIGHTS.map(|height| {
    let last = Scalar::from_usize(height - 1);
    [Scalar::from_usize(height), last, last * last]
  })
}

#[test]
fn blake3_proof_roundtrips_and_rejects_tampering_without_proving_powers() {
  let srs = Srs::unsafe_dev_setup(8, SEED);
  srs.validate().unwrap();
  let config = KzgConfig::new(Arc::new(srs), QUOTIENT_DEGREE)
    .with_transcript(TranscriptKind::Blake3);
  let (mut system, key) = System::new(
    config,
    HEIGHTS.map(|height| {
      let x = Expr::main(0);
      let square = Expr::main(1);
      CircuitInputs {
        main_width: 2,
        preprocessed: Some(RowMajorMatrix::new(
          (0..height)
            .flat_map(|row| {
              [Scalar::from_usize(row), Scalar::from_bool(row + 1 == height)]
            })
            .collect(),
          2,
        )),
        constraints: vec![
          x.clone() - Expr::preprocessed(0),
          square.clone() - x.clone() * x.clone(),
          Expr::IsTransition
            * (Expr::main_next(0) - x.clone() - Expr::constant(Scalar::ONE)),
        ],
        lookups: vec![Lookup::pull(
          Expr::preprocessed(1),
          vec![Expr::constant(Scalar::from_usize(height)), x, square],
        )],
        ..Default::default()
      }
    }),
  );
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|claim| claim.as_slice()).collect();
  let traces = HEIGHTS
    .map(|height| {
      RowMajorMatrix::new(
        (0..height)
          .flat_map(|row| {
            let x = Scalar::from_usize(row);
            [x, x * x]
          })
          .collect(),
        2,
      )
    })
    .to_vec();
  let proof = system.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(traces, &system),
  );
  system.verify_multiple_claims(&refs, &proof).unwrap();
  assert_eq!(proof.log_degrees, [2, 3]);
  assert_eq!(proof.opening_proof.0.len(), 3);

  let codec = FixedProofCodec::new(&system, &proof.log_degrees).unwrap();
  let encoded = codec.encode(&proof).unwrap();
  assert_eq!(&encoded[..4], b"KBN1");
  let mut wrong_curve = encoded.clone();
  wrong_curve[..4].copy_from_slice(b"KQP4");
  assert!(codec.decode(&wrong_curve).is_err());
  let decoded = codec.decode(&encoded).unwrap();
  assert_eq!(codec.encode(&decoded).unwrap(), encoded);

  let anchors = Srs::unsafe_dev_setup_prefix(2, 7, SEED);
  let params = VerifierParams::with_max_trace_len(&anchors, 8);
  let parameters = params.to_bytes().unwrap();
  assert_eq!(
    parameters,
    system.config.pcs().verifier_params().to_bytes().unwrap()
  );
  let params = VerifierParams::from_bytes(&parameters).unwrap();
  assert_eq!(params.public_setup(), anchors.public_setup);
  assert_eq!(params.max_trace_len(), 8);
  let verifier = KzgConfig::verifier_only(params, QUOTIENT_DEGREE)
    .with_transcript(TranscriptKind::Blake3);
  assert_eq!(verifier.transcript_seed(), system.config.transcript_seed());
  system.config = verifier.clone();
  drop(key);
  system.verify_multiple_claims(&refs, &proof).unwrap();
  system.verify_multiple_claims(&refs, &decoded).unwrap();

  let mut changed_claims = claims;
  changed_claims[0][2] += Scalar::ONE;
  let changed_refs: Vec<_> =
    changed_claims.iter().map(|claim| claim.as_slice()).collect();
  assert!(system.verify_multiple_claims(&changed_refs, &decoded).is_err());

  for attack in ["evaluation", "commitment", "opening", "accumulator"] {
    let mut bad = proof.clone();
    match attack {
      "evaluation" => bad.stage_1_opened_values[0][0][0] += Scalar::ONE,
      "commitment" => {
        let point = &mut bad.commitments.stage_1_trace.0[0][0];
        *point = (*point + G1Affine::generator()).into_affine();
      },
      "opening" => {
        let point = &mut bad.opening_proof.0[0];
        *point = (*point + G1Affine::generator()).into_affine();
      },
      "accumulator" => bad.intermediate_accumulators[0] += Scalar::ONE,
      _ => unreachable!(),
    }
    let bad = codec.decode(&codec.encode(&bad).unwrap()).unwrap();
    assert!(
      system.verify_multiple_claims(&refs, &bad).is_err(),
      "accepted changed {attack}"
    );
  }

  for end in [0, 4, 5, encoded.len() - 1] {
    assert!(codec.decode(&encoded[..end]).is_err());
  }
  let mut bad = encoded.clone();
  bad.push(0);
  assert!(codec.decode(&bad).is_err());
  let mut bad = encoded.clone();
  bad[5..37].fill(0xff);
  assert!(codec.decode(&bad).is_err());
  let mut with_identity = proof.clone();
  with_identity.commitments.stage_1_trace.0[0][0] = G1Affine::identity();
  let mut aliased_identity = codec.encode(&with_identity).unwrap();
  codec.decode(&aliased_identity).unwrap();
  aliased_identity[5] = 1;
  assert!(codec.decode(&aliased_identity).is_err());
  let mut bad = encoded;
  let scalar_start = bad.len() - 32;
  bad[scalar_start..].copy_from_slice(&Fr::MODULUS.to_bytes_le());
  assert!(codec.decode(&bad).is_err());

  system.config = verifier.with_transcript(TranscriptKind::Keccak256);
  assert!(system.verify_multiple_claims(&refs, &proof).is_err());
}

#[test]
fn bn254_scalars_and_points_use_canonical_encodings() {
  let _: Fr = Scalar::ONE.0;
  assert_eq!(Scalar::TWO_ADICITY, 28);
  let values = [Scalar::ZERO, Scalar::ONE, Scalar::NEG_ONE];
  let mut encoded = Vec::new();
  write_scalars(&mut encoded, &values).unwrap();
  assert_eq!(encoded.len(), 3 * 32);
  assert_eq!(read_scalars(&mut encoded.as_slice(), 3).unwrap(), values);
  let mut native = Vec::new();
  for value in values {
    value.0.serialize_compressed(&mut native).unwrap();
  }
  assert_eq!(encoded, native);
  let modulus = Fr::MODULUS.to_bytes_le();
  assert!(read_scalars(&mut modulus.as_slice(), 1).is_err());
  assert!(read_scalars(&mut &encoded[..31], 1).is_err());

  for point in [G1Affine::generator(), G1Affine::identity()] {
    let mut bytes = Vec::new();
    point.serialize_compressed(&mut bytes).unwrap();
    assert_eq!(bytes.len(), 32);
    assert_eq!(
      G1Affine::deserialize_compressed(bytes.as_slice()).unwrap(),
      point
    );
  }
  let point = G2Affine::generator();
  let mut bytes = Vec::new();
  point.serialize_compressed(&mut bytes).unwrap();
  assert_eq!(bytes.len(), 64);
  assert_eq!(
    G2Affine::deserialize_compressed(bytes.as_slice()).unwrap(),
    point
  );
  assert!(G1Affine::deserialize_compressed([0xff; 32].as_slice()).is_err());
}

#[test]
fn portable_parameters_reject_inconsistent_anchors_and_extra_bytes() {
  let mut srs = Srs::unsafe_dev_setup(8, SEED);
  let parameters = VerifierParams::from_srs(&srs).to_bytes().unwrap();
  let mut trailing = parameters.clone();
  trailing.push(0);
  assert!(VerifierParams::from_bytes(&trailing).is_err());
  assert!(
    VerifierParams::from_bytes(&parameters[..parameters.len() - 1]).is_err()
  );

  srs.g1[1] = (srs.g1[1] + G1Affine::generator()).into_affine();
  let inconsistent = VerifierParams::from_srs(&srs).to_bytes().unwrap();
  assert!(VerifierParams::from_bytes(&inconsistent).is_err());
}
