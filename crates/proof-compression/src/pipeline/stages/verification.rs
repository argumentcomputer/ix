//! Prepared recursive verification shared by local and bundled profiles.
use super::{
  KzgVerifier, Result, scalar_statement, statement::Statement,
  wrap::RecursiveProof,
};
use crate::kzg::{KzgConfig, Scalar};
use ark_bls12_381::{Bls12_381, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::{system::System, types::Val};

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
    self.verify_bytes(&self.encode(values)?)
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
      b"IXRECV02",
      (self.verifier.to_bytes()?, self.claim_len, keys),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (verifier, claim_len, keys): (Vec<u8>, usize, Vec<u8>) =
      super::codec::decode(b"IXRECV02", bytes)?;
    let verifier = KzgVerifier::from_bytes(&verifier)?;
    if keys.len() != 2 * 96
      || claim_len.checked_add(4) != Some(verifier.statement.locations.len())
    {
      return Err("invalid recursive public statement dimensions".into());
    }
    let keys = keys
      .as_chunks::<96>()
      .0
      .iter()
      .map(|bytes| G2Affine::deserialize_compressed(bytes.as_slice()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
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
      != claim_len.checked_add(4).ok_or("public count overflow")?
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
    if bytes.len() != 96 {
      return Err("pairing point count".into());
    }
    let points = bytes
      .as_chunks::<48>()
      .0
      .iter()
      .map(|bytes| G1Affine::deserialize_compressed(bytes.as_slice()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    if !Bls12_381::multi_pairing(points, self.keys).is_zero() {
      return Err("external opening pairing equation failed".into());
    }
    Ok(())
  }
}

pub(in crate::pipeline) fn unpack_pairings(
  bytes: &[u8],
) -> Result<Vec<Scalar>> {
  if bytes.len() != 96 {
    return Err("pairing point count".into());
  }
  Ok(
    bytes
      .as_chunks::<24>()
      .0
      .iter()
      .map(|chunk| {
        let mut limbs = [0; 4];
        for (limb, bytes) in limbs.iter_mut().zip(chunk.as_chunks::<8>().0) {
          *limb = u64::from_le_bytes(*bytes);
        }
        Scalar::from_limbs_le(limbs)
      })
      .collect(),
  )
}

pub(in crate::pipeline) fn pack_pairings(values: &[Scalar]) -> Result<Vec<u8>> {
  if values.len() != 4 {
    return Err("incorrect pairing operand count".into());
  }
  let mut bytes = Vec::with_capacity(values.len() * 24);
  for value in values {
    let limbs = value.canonical_limbs_le();
    if limbs[3] != 0 {
      return Err("noncanonical packed pairing operand".into());
    }
    for limb in &limbs[..3] {
      bytes.extend(limb.to_le_bytes());
    }
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
  if bytes.len() < 96 {
    return Err("truncated pairing operands".into());
  }
  let mut public = expected.to_vec();
  public.extend(unpack_pairings(&bytes[..96])?);
  let claims = statement.claims(&public)?;
  let proof = codec.decode(&bytes[96..])?;
  system
    .verify_multiple_claims(
      &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
      &proof,
    )
    .map_err(|e| format!("outer KZG proof: {e:?}"))?;
  pairings.verify_bytes(&bytes[..96])
}
