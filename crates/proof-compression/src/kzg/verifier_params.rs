//! Public verifier parameters, with the original SRS degree range preserved.
use super::Srs;
use ark_bls12_381::{G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, SerializationError,
};

#[derive(Clone)]
pub struct VerifierParams {
  pub(crate) max_len: usize,
  pub(crate) g1: [G1Affine; 2],
  pub(crate) g2: G2Affine,
  pub(crate) tau_g2: G2Affine,
  pub(crate) degree_keys: Vec<G2Affine>,
}

impl VerifierParams {
  pub fn from_srs(srs: &Srs) -> Self {
    assert!(srs.max_len() >= 2 && srs.max_len().is_power_of_two());
    assert_eq!(srs.degree_keys.len(), srs.max_len().ilog2() as usize + 1);
    Self {
      max_len: srs.max_len(),
      g1: [srs.g1[0], srs.g1[1]],
      g2: srs.g2,
      tau_g2: srs.tau_g2,
      degree_keys: srs.degree_keys.clone(),
    }
  }

  pub fn max_len(&self) -> usize {
    self.max_len
  }

  pub fn to_bytes(&self) -> Result<Vec<u8>, SerializationError> {
    let mut out = vec![];
    1u64.serialize_compressed(&mut out)?;
    (self.max_len as u64).serialize_compressed(&mut out)?;
    for point in self.g1 {
      point.serialize_compressed(&mut out)?;
    }
    self.g2.serialize_compressed(&mut out)?;
    self.tau_g2.serialize_compressed(&mut out)?;
    for key in &self.degree_keys {
      key.serialize_compressed(&mut out)?;
    }
    Ok(out)
  }

  /// Validated point decoding and shape checks. Provenance must be established independently.
  pub fn from_bytes(mut input: &[u8]) -> Result<Self, SerializationError> {
    if u64::deserialize_compressed(&mut input)? != 1 {
      return Err(SerializationError::InvalidData);
    }
    let max_len = usize::try_from(u64::deserialize_compressed(&mut input)?)
      .map_err(|_error| SerializationError::InvalidData)?;
    if max_len < 2 || !max_len.is_power_of_two() || max_len.ilog2() > 32 {
      return Err(SerializationError::InvalidData);
    }
    let g1 = [
      G1Affine::deserialize_compressed(&mut input)?,
      G1Affine::deserialize_compressed(&mut input)?,
    ];
    let g2 = G2Affine::deserialize_compressed(&mut input)?;
    let tau_g2 = G2Affine::deserialize_compressed(&mut input)?;
    let degree_keys = (0..=max_len.ilog2())
      .map(|_| G2Affine::deserialize_compressed(&mut input))
      .collect::<Result<Vec<_>, _>>()?;
    if !input.is_empty()
      || g1.iter().any(AffineRepr::is_zero)
      || g2.is_zero()
      || tau_g2.is_zero()
      || degree_keys.iter().any(AffineRepr::is_zero)
      || degree_keys.last() != Some(&g2)
      || !ark_bls12_381::Bls12_381::multi_pairing([g1[1], -g1[0]], [g2, tau_g2])
        .is_zero()
    {
      return Err(SerializationError::InvalidData);
    }
    Ok(Self { max_len, g1, g2, tau_g2, degree_keys })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn encoding_preserves_degree_bound_and_rejects_malformed_keys() {
    let srs = Srs::unsafe_dev_setup(64, b"verifier-params");
    let params = VerifierParams::from_srs(&srs);
    let encoded = params.to_bytes().unwrap();
    let decoded = VerifierParams::from_bytes(&encoded).unwrap();
    assert_eq!(decoded.max_len(), 64);
    assert_eq!(decoded.g1.len(), 2);
    assert_eq!(decoded.degree_keys, srs.degree_keys);
    assert!(VerifierParams::from_bytes(&encoded[..encoded.len() - 1]).is_err());
    let mut extra = encoded.clone();
    extra.push(0);
    assert!(VerifierParams::from_bytes(&extra).is_err());
    let mut bad = params.clone();
    bad.max_len = 32;
    assert!(VerifierParams::from_bytes(&bad.to_bytes().unwrap()).is_err());
    let mut bad = params;
    bad.g1[1] = bad.g1[0];
    assert!(VerifierParams::from_bytes(&bad.to_bytes().unwrap()).is_err());
  }
}
