//! Prepared recursive verification shared by local and bundled verifying keys.
use super::{
  KzgVerifier, Result, scalar_statement, statement::Statement,
  wrap::RecursiveProof,
};
use crate::kzg::{
  KzgConfig, Scalar,
  curve::{
    G1_COMPRESSED_BYTES, G1Affine, G2_COMPRESSED_BYTES, G2Affine, PairingCurve,
    read_g1_compressed,
  },
};
use crate::recursive::pairing::{self, PUBLIC_VALUES};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::{system::System, types::Val};

#[cfg(not(feature = "bn254"))]
const RECURSIVE_VERIFIER_MAGIC: &[u8; 8] = b"IXRECV02";
#[cfg(feature = "bn254")]
const RECURSIVE_VERIFIER_MAGIC: &[u8; 8] = b"IXBNRV02";

pub(in crate::pipeline) const PAIRING_BYTES: usize = 2 * G1_COMPRESSED_BYTES;

pub(in crate::pipeline) struct Pairings {
  pub(in crate::pipeline) keys: [G2Affine; 2],
}

impl Pairings {
  pub(in crate::pipeline) fn encode(
    &self,
    values: &[Scalar],
  ) -> Result<Vec<u8>> {
    pack_pairings(values)
  }

  pub(in crate::pipeline) fn verify(&self, values: &[Scalar]) -> Result<()> {
    self.verify_points(pairing::decode(values)?)
  }
}

pub struct RecursiveVerifier {
  pub(super) verifier: KzgVerifier,
  pub(super) pairings: Pairings,
  pub(super) claim_len: usize,
}

impl RecursiveVerifier {
  /// Encode all verification data, including both stages' public parameters
  /// and the pairing equations. Authenticate the complete encoding on transport.
  pub fn to_bytes(&self) -> Result<Vec<u8>> {
    let mut keys = vec![];
    for key in &self.pairings.keys {
      key.serialize_compressed(&mut keys)?;
    }
    super::codec::encode(
      RECURSIVE_VERIFIER_MAGIC,
      (self.verifier.to_bytes()?, self.claim_len, keys),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (verifier, claim_len, keys): (Vec<u8>, usize, Vec<u8>) =
      super::codec::decode(RECURSIVE_VERIFIER_MAGIC, bytes)?;
    let verifier = KzgVerifier::from_bytes(&verifier)?;
    if keys.len() != 2 * G2_COMPRESSED_BYTES
      || claim_len.checked_add(PUBLIC_VALUES)
        != Some(verifier.statement.locations.len())
    {
      return Err("invalid recursive public statement dimensions".into());
    }
    let encoded_keys = keys;
    let keys = encoded_keys
      .as_chunks::<G2_COMPRESSED_BYTES>()
      .0
      .iter()
      .map(|bytes| G2Affine::deserialize_compressed(bytes.as_slice()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut canonical_keys = Vec::with_capacity(encoded_keys.len());
    for key in &keys {
      key.serialize_compressed(&mut canonical_keys)?;
    }
    if canonical_keys != encoded_keys {
      return Err("noncanonical recursive pairing keys".into());
    }
    Self::from_parts(verifier.system, verifier.statement, &keys, claim_len)
  }

  /// Pack the public pairing operands followed by the fixed-shape KZG proof.
  /// The expected certificate claim and trusted verifier are supplied separately.
  pub fn encode_proof(&self, proof: &RecursiveProof) -> Result<Vec<u8>> {
    let mut bytes = self.pairings.encode(&proof.pairing_values)?;
    bytes.extend(self.verifier.encode_proof(&proof.proof)?);
    Ok(bytes)
  }

  pub fn verify_bytes(&self, bytes: &[u8], expected: &[Val]) -> Result<()> {
    self.verify_scalar_bytes(bytes, &scalar_statement(expected))
  }

  /// Verify the recursive proof, expected certificate statement, and the
  /// deferred inner opening pairing. No proving SRS is needed.
  pub fn verify(&self, proof: &RecursiveProof, expected: &[Val]) -> Result<()> {
    if expected.len() != self.claim_len {
      return Err("unexpected certificate claim length".into());
    }
    let mut public = scalar_statement(expected);
    public.extend_from_slice(&proof.pairing_values);
    self.verifier.verify(&proof.proof, &public)?;
    self.pairings.verify(&proof.pairing_values)
  }
}

impl RecursiveVerifier {
  pub(in crate::pipeline) fn from_parts(
    system: System<KzgConfig>,
    statement: Statement<Scalar>,
    keys: &[G2Affine],
    claim_len: usize,
  ) -> Result<Self> {
    let keys: [G2Affine; 2] =
      keys.try_into().map_err(|_keys| "expected two pairing keys")?;
    if keys.iter().any(|p| {
      p.is_zero()
        || !p.is_on_curve()
        || !p.is_in_correct_subgroup_assuming_on_curve()
    }) || statement.locations.len()
      != claim_len.checked_add(PUBLIC_VALUES).ok_or("public count overflow")?
    {
      return Err("invalid recursive verifier parameters".into());
    }
    Ok(Self {
      verifier: KzgVerifier::new(system, statement)?,
      pairings: Pairings { keys },
      claim_len,
    })
  }

  pub(in crate::pipeline) fn verify_scalar_bytes(
    &self,
    bytes: &[u8],
    expected: &[Scalar],
  ) -> Result<()> {
    if expected.len() != self.claim_len {
      return Err("unexpected certificate claim length".into());
    }
    verify_recursive_bytes(
      &self.verifier.system,
      &self.verifier.codec,
      &self.verifier.statement,
      &self.pairings,
      bytes,
      expected,
    )
  }
}

impl Pairings {
  pub(in crate::pipeline) fn verify_bytes(&self, bytes: &[u8]) -> Result<()> {
    self.verify_points(pairing_points(bytes)?)
  }

  fn verify_points(&self, points: [G1Affine; 2]) -> Result<()> {
    if !PairingCurve::multi_pairing(points, self.keys).is_zero() {
      return Err("external opening pairing equation failed".into());
    }
    Ok(())
  }
}

fn pairing_points(mut bytes: &[u8]) -> Result<[G1Affine; 2]> {
  if bytes.len() != PAIRING_BYTES {
    return Err("pairing point count".into());
  }
  Ok([read_g1_compressed(&mut bytes)?, read_g1_compressed(&mut bytes)?])
}

#[cfg(any(test, feature = "plonk"))]
pub(in crate::pipeline) fn unpack_pairings(
  bytes: &[u8],
) -> Result<Vec<Scalar>> {
  Ok(pairing::encode(pairing_points(bytes)?).to_vec())
}

pub(in crate::pipeline) fn pack_pairings(values: &[Scalar]) -> Result<Vec<u8>> {
  let mut bytes = Vec::with_capacity(PAIRING_BYTES);
  for point in pairing::decode(values)? {
    point.serialize_compressed(&mut bytes)?;
  }
  Ok(bytes)
}

pub(in crate::pipeline) fn verify_recursive_bytes(
  system: &System<KzgConfig>,
  codec: &crate::kzg::compact::FixedProofCodec,
  statement: &Statement<Scalar>,
  pairings: &Pairings,
  bytes: &[u8],
  expected: &[Scalar],
) -> Result<()> {
  if bytes.len() < PAIRING_BYTES {
    return Err("truncated pairing operands".into());
  }
  let points = pairing_points(&bytes[..PAIRING_BYTES])?;
  let mut public = expected.to_vec();
  public.extend(pairing::encode(points));
  let claims = statement.claims(&public)?;
  let proof = codec.decode(&bytes[PAIRING_BYTES..])?;
  system
    .verify_multiple_claims(
      &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
      &proof,
    )
    .map_err(|e| format!("outer KZG proof: {e:?}"))?;
  pairings.verify_points(points)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::Fr;
  use crate::recursive::pairing::POINT_LIMB_BYTES;
  use ark_ec::CurveGroup;
  use multi_stark::traits::Algebra;

  #[test]
  fn pairing_transport_preserves_points_and_rejects_noncanonical_values()
  -> Result<()> {
    let generator = G1Affine::generator();
    let multiple = (generator * Fr::from(7u8)).into_affine();
    for points in [
      [generator, multiple],
      [-generator, -multiple],
      [G1Affine::identity(), generator],
      [G1Affine::identity(); 2],
    ] {
      let values = pairing::encode(points);
      let encoded = pack_pairings(&values)?;
      assert_eq!(encoded.len(), PAIRING_BYTES);
      assert_eq!(pairing_points(&encoded)?, points);
      assert_eq!(unpack_pairings(&encoded)?, values);
      assert!(unpack_pairings(&encoded[..encoded.len() - 1]).is_err());
      let mut extra = encoded.clone();
      extra.push(0);
      assert!(unpack_pairings(&extra).is_err());
      let mut invalid = encoded;
      invalid[..G1_COMPRESSED_BYTES].fill(0xff);
      assert!(unpack_pairings(&invalid).is_err());
      for i in 0..PUBLIC_VALUES {
        let mut high_limb = [0; 4];
        high_limb[POINT_LIMB_BYTES / 8] = 1;
        let mut aliased = values;
        aliased[i] += Scalar::from_limbs_le(high_limb);
        assert!(pack_pairings(&aliased).is_err());
      }
      assert!(pack_pairings(&values[..PUBLIC_VALUES - 1]).is_err());
      assert!(pack_pairings(&[Scalar::ZERO; PUBLIC_VALUES + 1]).is_err());
    }
    Ok(())
  }

  #[cfg(feature = "bn254")]
  #[test]
  fn pairing_transport_rejects_infinity_coordinate_aliases() -> Result<()> {
    let values = pairing::encode([G1Affine::identity(); 2]);
    let mut encoded = pack_pairings(&values)?;
    encoded[0] = 1;
    assert!(unpack_pairings(&encoded).is_err());
    let mut aliased = values;
    aliased[0] = Scalar::ONE;
    assert!(pack_pairings(&aliased).is_err());
    Ok(())
  }
}
