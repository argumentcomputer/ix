//! Portable KZG anchors and the complete public degree allowance.
use super::{PublicSetup, Srs};
use ark_bls12_381::{G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, SerializationError,
};

#[derive(Clone)]
pub struct VerifierParams {
  max_trace_len: usize,
  pub(crate) public_setup: PublicSetup,
  pub(crate) g1: [G1Affine; 2],
  pub(crate) g2: G2Affine,
  pub(crate) tau_g2: G2Affine,
}

fn valid_cap(cap: usize, setup: PublicSetup) -> bool {
  cap >= 2
    && cap.is_power_of_two()
    && cap.ilog2() <= 32
    && setup.max_degree >= cap - 1
    && setup.max_degree.checked_add(1).is_some()
}

impl VerifierParams {
  pub fn from_srs(srs: &Srs) -> Self {
    Self::with_max_trace_len(srs, srs.max_len())
  }

  pub fn with_max_trace_len(srs: &Srs, max_trace_len: usize) -> Self {
    assert!(srs.max_len() >= 2 && srs.max_len().is_power_of_two());
    assert!(srs.public_setup.max_degree >= srs.max_len() - 1);
    assert!(
      valid_cap(max_trace_len, srs.public_setup),
      "invalid public degree or trace cap"
    );
    Self {
      max_trace_len,
      public_setup: srs.public_setup,
      g1: [srs.g1[0], srs.g1[1]],
      g2: srs.g2,
      tau_g2: srs.tau_g2,
    }
  }

  pub fn max_trace_len(&self) -> usize {
    self.max_trace_len
  }

  pub fn public_setup(&self) -> PublicSetup {
    self.public_setup
  }

  pub fn to_bytes(&self) -> Result<Vec<u8>, SerializationError> {
    let mut out = vec![];
    4u64.serialize_compressed(&mut out)?;
    (self.max_trace_len as u64).serialize_compressed(&mut out)?;
    (self.public_setup.max_degree as u64).serialize_compressed(&mut out)?;
    self.public_setup.id.serialize_compressed(&mut out)?;
    for point in self.g1 {
      point.serialize_compressed(&mut out)?;
    }
    self.g2.serialize_compressed(&mut out)?;
    self.tau_g2.serialize_compressed(&mut out)?;
    Ok(out)
  }

  /// Validated point decoding and shape checks; provenance is authenticated separately.
  pub fn from_bytes(mut input: &[u8]) -> Result<Self, SerializationError> {
    if u64::deserialize_compressed(&mut input)? != 4 {
      return Err(SerializationError::InvalidData);
    }
    let max_trace_len =
      usize::try_from(u64::deserialize_compressed(&mut input)?)
        .map_err(|_error| SerializationError::InvalidData)?;
    let max_degree = usize::try_from(u64::deserialize_compressed(&mut input)?)
      .map_err(|_error| SerializationError::InvalidData)?;
    let public_setup = PublicSetup {
      max_degree,
      id: <[u8; 32]>::deserialize_compressed(&mut input)?,
    };
    if !valid_cap(max_trace_len, public_setup) {
      return Err(SerializationError::InvalidData);
    }
    let g1 = [
      G1Affine::deserialize_compressed(&mut input)?,
      G1Affine::deserialize_compressed(&mut input)?,
    ];
    let g2 = G2Affine::deserialize_compressed(&mut input)?;
    let tau_g2 = G2Affine::deserialize_compressed(&mut input)?;
    if !input.is_empty()
      || g1.iter().any(AffineRepr::is_zero)
      || g2.is_zero()
      || tau_g2.is_zero()
      || !ark_bls12_381::Bls12_381::multi_pairing([g1[1], -g1[0]], [g2, tau_g2])
        .is_zero()
    {
      return Err(SerializationError::InvalidData);
    }
    Ok(Self { max_trace_len, public_setup, g1, g2, tau_g2 })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn public_identity_and_degree_are_independent_of_loaded_prefix() {
    let prover = Srs::unsafe_dev_setup(64, b"verifier-params");
    let anchors = Srs::unsafe_dev_setup_prefix(2, 63, b"verifier-params");
    let params = VerifierParams::from_srs(&prover);
    let portable = VerifierParams::with_max_trace_len(&anchors, 64);
    assert_eq!(params.to_bytes().unwrap(), portable.to_bytes().unwrap());
    let decoded =
      VerifierParams::from_bytes(&params.to_bytes().unwrap()).unwrap();
    assert_eq!(decoded.max_trace_len(), 64);
    assert_eq!(decoded.public_setup(), prover.public_setup);
    assert_ne!(
      prover.public_setup,
      Srs::unsafe_dev_setup(32, b"verifier-params").public_setup
    );
    assert_ne!(
      prover.public_setup,
      Srs::unsafe_dev_setup(64, b"other").public_setup
    );
  }

  #[test]
  fn rejects_malformed_parameters() {
    let params =
      VerifierParams::from_srs(&Srs::unsafe_dev_setup(64, b"verifier-params"));
    let encoded = params.to_bytes().unwrap();
    assert!(VerifierParams::from_bytes(&encoded[..encoded.len() - 1]).is_err());
    let mut extra = encoded.clone();
    extra.push(0);
    assert!(VerifierParams::from_bytes(&extra).is_err());
    let mut unsupported_version = encoded;
    unsupported_version[..8].copy_from_slice(&0u64.to_le_bytes());
    assert!(VerifierParams::from_bytes(&unsupported_version).is_err());
    let mut bad = params.clone();
    bad.public_setup.max_degree = 31;
    assert!(VerifierParams::from_bytes(&bad.to_bytes().unwrap()).is_err());
    let mut bad = params;
    bad.g1[1] = bad.g1[0];
    assert!(VerifierParams::from_bytes(&bad.to_bytes().unwrap()).is_err());
  }
}
