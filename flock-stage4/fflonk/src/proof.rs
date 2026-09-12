use ark_bls12_381::{Fq, Fr, G1Affine};
use ark_ff::{BigInteger, PrimeField};
use core::fmt;

/// Number of G1 commitments in the Ix Stage 4 FFLONK proof profile.
pub const FFLONK_COMMITMENTS: usize = 4;

/// Number of scalar-field values in the Ix Stage 4 FFLONK proof profile.
pub const FFLONK_EVALUATIONS: usize = 15;

/// Width of one uncompressed EIP-2537 G1 point.
pub const EIP2537_G1_BYTES: usize = 128;

/// Width of one canonical BLS12-381 scalar-field value.
pub const BLS12_381_SCALAR_BYTES: usize = 32;

/// Exact encoded width of an Ix Stage 4 FFLONK proof.
pub const FFLONK_PROOF_BYTES: usize = FFLONK_COMMITMENTS * EIP2537_G1_BYTES
  + FFLONK_EVALUATIONS * BLS12_381_SCALAR_BYTES;

const EIP2537_BASE_FIELD_BYTES: usize = 64;

/// Canonical Stage 4 FFLONK proof transport.
///
/// The byte layout is four EIP-2537 G1 points followed by fifteen canonical,
/// big-endian BLS12-381 scalar-field elements. The wire decoder accepts the
/// EIP-2537 infinity encoding; protocol verification is responsible for any
/// stronger commitment-specific infinity policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FflonkProofV1 {
  pub commitments: [G1Affine; FFLONK_COMMITMENTS],
  pub evaluations: [Fr; FFLONK_EVALUATIONS],
}

/// Named view of the four commitment slots in [`FflonkProofV1`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkCommitmentsV1 {
  pub c1: G1Affine,
  pub c2: G1Affine,
  pub w1: G1Affine,
  pub w2: G1Affine,
}

/// Named view of the fifteen evaluation slots in [`FflonkProofV1`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkEvaluationsV1 {
  pub ql: Fr,
  pub qr: Fr,
  pub qm: Fr,
  pub qo: Fr,
  pub qc: Fr,
  pub s1: Fr,
  pub s2: Fr,
  pub s3: Fr,
  pub a: Fr,
  pub b: Fr,
  pub c: Fr,
  pub z: Fr,
  pub zw: Fr,
  pub t1w: Fr,
  pub t2w: Fr,
}

impl FflonkProofV1 {
  /// Returns commitment slots with their protocol names.
  #[must_use]
  pub fn named_commitments(&self) -> FflonkCommitmentsV1 {
    FflonkCommitmentsV1 {
      c1: self.commitments[0],
      c2: self.commitments[1],
      w1: self.commitments[2],
      w2: self.commitments[3],
    }
  }

  /// Returns evaluation slots with their protocol names.
  #[must_use]
  pub fn named_evaluations(&self) -> FflonkEvaluationsV1 {
    FflonkEvaluationsV1 {
      ql: self.evaluations[0],
      qr: self.evaluations[1],
      qm: self.evaluations[2],
      qo: self.evaluations[3],
      qc: self.evaluations[4],
      s1: self.evaluations[5],
      s2: self.evaluations[6],
      s3: self.evaluations[7],
      a: self.evaluations[8],
      b: self.evaluations[9],
      c: self.evaluations[10],
      z: self.evaluations[11],
      zw: self.evaluations[12],
      t1w: self.evaluations[13],
      t2w: self.evaluations[14],
    }
  }

  /// Decodes the canonical fixed-width Stage 4 proof representation.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, FflonkProofDecodeError> {
    if bytes.len() != FFLONK_PROOF_BYTES {
      return Err(FflonkProofDecodeError::WrongLength {
        expected: FFLONK_PROOF_BYTES,
        actual: bytes.len(),
      });
    }

    let mut commitments = [G1Affine::identity(); FFLONK_COMMITMENTS];
    for (index, output) in commitments.iter_mut().enumerate() {
      let offset = index * EIP2537_G1_BYTES;
      *output = decode_g1(&bytes[offset..offset + EIP2537_G1_BYTES], index)?;
    }

    let evaluations_offset = FFLONK_COMMITMENTS * EIP2537_G1_BYTES;
    let mut evaluations = [Fr::from(0_u64); FFLONK_EVALUATIONS];
    for (index, output) in evaluations.iter_mut().enumerate() {
      let offset = evaluations_offset + index * BLS12_381_SCALAR_BYTES;
      let encoded = &bytes[offset..offset + BLS12_381_SCALAR_BYTES];
      *output = decode_field_be(encoded)
        .ok_or(FflonkProofDecodeError::NonCanonicalScalar { index })?;
    }

    Ok(Self { commitments, evaluations })
  }

  /// Encodes the proof using the canonical fixed-width Stage 4 representation.
  #[must_use]
  pub fn to_bytes(&self) -> [u8; FFLONK_PROOF_BYTES] {
    let mut encoded = [0_u8; FFLONK_PROOF_BYTES];
    for (index, commitment) in self.commitments.iter().enumerate() {
      let offset = index * EIP2537_G1_BYTES;
      encode_g1(commitment, &mut encoded[offset..offset + EIP2537_G1_BYTES]);
    }

    let evaluations_offset = FFLONK_COMMITMENTS * EIP2537_G1_BYTES;
    for (index, evaluation) in self.evaluations.iter().enumerate() {
      let offset = evaluations_offset + index * BLS12_381_SCALAR_BYTES;
      encode_field_be(
        evaluation,
        &mut encoded[offset..offset + BLS12_381_SCALAR_BYTES],
      );
    }
    encoded
  }
}

/// Why a Stage 4 FFLONK proof failed canonical decoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkProofDecodeError {
  WrongLength { expected: usize, actual: usize },
  NonCanonicalBaseField { commitment: usize, coordinate: Coordinate },
  PointNotOnCurve { commitment: usize },
  PointNotInSubgroup { commitment: usize },
  NonCanonicalScalar { index: usize },
}

/// Affine coordinate associated with a decoding failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coordinate {
  X,
  Y,
}

impl fmt::Display for FflonkProofDecodeError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::WrongLength { expected, actual } => write!(
        formatter,
        "wrong proof length: expected {expected} bytes, got {actual}",
      ),
      Self::NonCanonicalBaseField { commitment, coordinate } => write!(
        formatter,
        "commitment {commitment} has a non-canonical {coordinate} coordinate",
      ),
      Self::PointNotOnCurve { commitment } => {
        write!(formatter, "commitment {commitment} is not on BLS12-381 G1")
      },
      Self::PointNotInSubgroup { commitment } => write!(
        formatter,
        "commitment {commitment} is not in the BLS12-381 G1 subgroup",
      ),
      Self::NonCanonicalScalar { index } => {
        write!(formatter, "evaluation {index} is not a canonical scalar")
      },
    }
  }
}

impl std::error::Error for FflonkProofDecodeError {}

impl fmt::Display for Coordinate {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::X => formatter.write_str("x"),
      Self::Y => formatter.write_str("y"),
    }
  }
}

fn decode_g1(
  encoded: &[u8],
  commitment: usize,
) -> Result<G1Affine, FflonkProofDecodeError> {
  if encoded.iter().all(|byte| *byte == 0) {
    return Ok(G1Affine::identity());
  }

  let x = decode_field_be::<Fq>(&encoded[..EIP2537_BASE_FIELD_BYTES]).ok_or(
    FflonkProofDecodeError::NonCanonicalBaseField {
      commitment,
      coordinate: Coordinate::X,
    },
  )?;
  let y = decode_field_be::<Fq>(&encoded[EIP2537_BASE_FIELD_BYTES..]).ok_or(
    FflonkProofDecodeError::NonCanonicalBaseField {
      commitment,
      coordinate: Coordinate::Y,
    },
  )?;
  let point = G1Affine::new_unchecked(x, y);
  if !point.is_on_curve() {
    return Err(FflonkProofDecodeError::PointNotOnCurve { commitment });
  }
  if !point.is_in_correct_subgroup_assuming_on_curve() {
    return Err(FflonkProofDecodeError::PointNotInSubgroup { commitment });
  }
  Ok(point)
}

fn encode_g1(point: &G1Affine, output: &mut [u8]) {
  debug_assert_eq!(output.len(), EIP2537_G1_BYTES);
  if point.infinity {
    output.fill(0);
    return;
  }
  encode_field_be(&point.x, &mut output[..EIP2537_BASE_FIELD_BYTES]);
  encode_field_be(&point.y, &mut output[EIP2537_BASE_FIELD_BYTES..]);
}

pub(crate) fn encode_g1_eip2537(point: &G1Affine) -> [u8; EIP2537_G1_BYTES] {
  let mut encoded = [0_u8; EIP2537_G1_BYTES];
  encode_g1(point, &mut encoded);
  encoded
}

pub(crate) fn encode_scalar_be(scalar: &Fr) -> [u8; BLS12_381_SCALAR_BYTES] {
  let mut encoded = [0_u8; BLS12_381_SCALAR_BYTES];
  encode_field_be(scalar, &mut encoded);
  encoded
}

fn decode_field_be<F: PrimeField>(encoded: &[u8]) -> Option<F> {
  let value = F::from_be_bytes_mod_order(encoded);
  let mut canonical = vec![0_u8; encoded.len()];
  encode_field_be(&value, &mut canonical);
  (canonical == encoded).then_some(value)
}

pub(crate) fn encode_field_be<F: PrimeField>(value: &F, output: &mut [u8]) {
  output.fill(0);
  let bytes = value.into_bigint().to_bytes_be();
  assert!(bytes.len() <= output.len());
  let offset = output.len() - bytes.len();
  output[offset..].copy_from_slice(&bytes);
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::AffineRepr;

  fn sample_proof() -> FflonkProofV1 {
    FflonkProofV1 {
      commitments: [G1Affine::generator(); FFLONK_COMMITMENTS],
      evaluations: core::array::from_fn(|index| Fr::from(index as u64)),
    }
  }

  #[test]
  fn wire_width_is_992_bytes() {
    assert_eq!(FFLONK_PROOF_BYTES, 992);
  }

  #[test]
  fn canonical_proof_round_trips() {
    let proof = sample_proof();
    let encoded = proof.to_bytes();
    assert_eq!(FflonkProofV1::from_bytes(&encoded), Ok(proof));
  }

  #[test]
  fn named_views_pin_the_protocol_slot_order() {
    let proof = sample_proof();
    let commitments = proof.named_commitments();
    assert_eq!(commitments.c1, proof.commitments[0]);
    assert_eq!(commitments.c2, proof.commitments[1]);
    assert_eq!(commitments.w1, proof.commitments[2]);
    assert_eq!(commitments.w2, proof.commitments[3]);

    let evaluations = proof.named_evaluations();
    assert_eq!(
      [
        evaluations.ql,
        evaluations.qr,
        evaluations.qm,
        evaluations.qo,
        evaluations.qc,
        evaluations.s1,
        evaluations.s2,
        evaluations.s3,
        evaluations.a,
        evaluations.b,
        evaluations.c,
        evaluations.z,
        evaluations.zw,
        evaluations.t1w,
        evaluations.t2w,
      ],
      proof.evaluations,
    );
  }

  #[test]
  fn canonical_infinity_round_trips() {
    let proof = FflonkProofV1 {
      commitments: [G1Affine::identity(); FFLONK_COMMITMENTS],
      evaluations: [Fr::from(0_u64); FFLONK_EVALUATIONS],
    };
    let encoded = proof.to_bytes();
    assert!(encoded.iter().all(|byte| *byte == 0));
    assert_eq!(FflonkProofV1::from_bytes(&encoded), Ok(proof));
  }

  #[test]
  fn rejects_wrong_length() {
    let error = FflonkProofV1::from_bytes(&[0_u8; 991]).unwrap_err();
    assert_eq!(
      error,
      FflonkProofDecodeError::WrongLength {
        expected: FFLONK_PROOF_BYTES,
        actual: 991,
      },
    );
  }

  #[test]
  fn rejects_noncanonical_base_field_coordinate() {
    let mut encoded = sample_proof().to_bytes();
    encoded[0] = 1;
    assert_eq!(
      FflonkProofV1::from_bytes(&encoded),
      Err(FflonkProofDecodeError::NonCanonicalBaseField {
        commitment: 0,
        coordinate: Coordinate::X,
      }),
    );
  }

  #[test]
  fn rejects_point_off_curve() {
    let mut encoded = sample_proof().to_bytes();
    encode_field_be(&Fq::from(0_u64), &mut encoded[..64]);
    encode_field_be(&Fq::from(1_u64), &mut encoded[64..128]);
    assert_eq!(
      FflonkProofV1::from_bytes(&encoded),
      Err(FflonkProofDecodeError::PointNotOnCurve { commitment: 0 }),
    );
  }

  #[test]
  fn rejects_point_outside_prime_order_subgroup() {
    let point = (0_u64..)
      .find_map(|x| {
        G1Affine::get_point_from_x_unchecked(Fq::from(x), false)
          .filter(|point| !point.is_in_correct_subgroup_assuming_on_curve())
      })
      .expect("BLS12-381 G1 has a nontrivial cofactor");
    let mut encoded = sample_proof().to_bytes();
    encode_g1(&point, &mut encoded[..EIP2537_G1_BYTES]);
    assert_eq!(
      FflonkProofV1::from_bytes(&encoded),
      Err(FflonkProofDecodeError::PointNotInSubgroup { commitment: 0 }),
    );
  }

  #[test]
  fn rejects_noncanonical_scalar() {
    let mut encoded = sample_proof().to_bytes();
    let scalar_offset = FFLONK_COMMITMENTS * EIP2537_G1_BYTES;
    encoded[scalar_offset..scalar_offset + BLS12_381_SCALAR_BYTES]
      .copy_from_slice(&Fr::MODULUS.to_bytes_be());
    assert_eq!(
      FflonkProofV1::from_bytes(&encoded),
      Err(FflonkProofDecodeError::NonCanonicalScalar { index: 0 }),
    );
  }
}
