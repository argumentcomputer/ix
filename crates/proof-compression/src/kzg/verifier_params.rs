//! Portable KZG anchors and the complete public degree allowance.
use super::curve::{Bn254, G1AffineOf, G2AffineOf, KzgCurve};
use super::{PublicSetup, Srs};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, SerializationError,
};

#[derive(Clone)]
pub struct VerifierParams<C: KzgCurve = Bn254> {
  max_trace_len: usize,
  pub(crate) public_setup: PublicSetup,
  pub(crate) g1: [G1AffineOf<C>; 2],
  pub(crate) g2: G2AffineOf<C>,
  pub(crate) tau_g2: G2AffineOf<C>,
}

fn valid_cap<C: KzgCurve>(cap: usize, setup: PublicSetup) -> bool {
  cap >= 2
    && cap.is_power_of_two()
    && cap.ilog2() as usize <= C::FR_TWO_ADICITY
    && setup.max_degree >= cap - 1
    && setup.max_degree.checked_add(1).is_some()
}

impl<C: KzgCurve> VerifierParams<C> {
  pub fn from_srs(srs: &Srs<C>) -> Self {
    Self::with_max_trace_len(srs, srs.max_len())
  }

  pub fn with_max_trace_len(srs: &Srs<C>, max_trace_len: usize) -> Self {
    assert!(srs.max_len() >= 2 && srs.max_len().is_power_of_two());
    assert!(srs.public_setup.max_degree >= srs.max_len() - 1);
    assert!(
      valid_cap::<C>(max_trace_len, srs.public_setup),
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
    C::VERIFIER_PARAMS_VERSION.serialize_compressed(&mut out)?;
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
    if u64::deserialize_compressed(&mut input)? != C::VERIFIER_PARAMS_VERSION {
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
    if !valid_cap::<C>(max_trace_len, public_setup) {
      return Err(SerializationError::InvalidData);
    }
    let g1 = [
      G1AffineOf::<C>::deserialize_compressed(&mut input)?,
      G1AffineOf::<C>::deserialize_compressed(&mut input)?,
    ];
    let g2 = G2AffineOf::<C>::deserialize_compressed(&mut input)?;
    let tau_g2 = G2AffineOf::<C>::deserialize_compressed(&mut input)?;
    if !input.is_empty()
      || g1.iter().any(AffineRepr::is_zero)
      || g2.is_zero()
      || tau_g2.is_zero()
      || !C::PairingCurve::multi_pairing([g1[1], -g1[0]], [g2, tau_g2])
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
  use crate::kzg::curve::Bls12381;

  fn check_verifier_params<C: KzgCurve>(expected_two_adicity: usize) {
    assert_eq!(C::FR_TWO_ADICITY, expected_two_adicity);
    if let Some(max_cap) =
      1usize.checked_shl(u32::try_from(C::FR_TWO_ADICITY).unwrap())
    {
      let anchors =
        Srs::<C>::unsafe_dev_setup_prefix(2, 2 * max_cap - 1, b"trace-cap");
      let params = VerifierParams::<C>::with_max_trace_len(&anchors, max_cap);
      assert_eq!(
        VerifierParams::<C>::from_bytes(&params.to_bytes().unwrap())
          .unwrap()
          .max_trace_len(),
        max_cap
      );
      let mut invalid = params;
      invalid.max_trace_len = 2 * max_cap;
      assert!(!valid_cap::<C>(invalid.max_trace_len, invalid.public_setup));
      assert!(
        VerifierParams::<C>::from_bytes(&invalid.to_bytes().unwrap()).is_err()
      );
    }

    let prover = Srs::<C>::unsafe_dev_setup(64, b"verifier-params");
    let anchors = Srs::<C>::unsafe_dev_setup_prefix(2, 63, b"verifier-params");
    let params = VerifierParams::<C>::from_srs(&prover);
    let portable = VerifierParams::<C>::with_max_trace_len(&anchors, 64);
    assert_eq!(params.to_bytes().unwrap(), portable.to_bytes().unwrap());
    let decoded =
      VerifierParams::<C>::from_bytes(&params.to_bytes().unwrap()).unwrap();
    assert_eq!(decoded.max_trace_len(), 64);
    assert_eq!(decoded.public_setup(), prover.public_setup);
    assert_ne!(
      prover.public_setup,
      Srs::<C>::unsafe_dev_setup(32, b"verifier-params").public_setup
    );
    assert_ne!(
      prover.public_setup,
      Srs::<C>::unsafe_dev_setup(64, b"other").public_setup
    );

    let encoded = params.to_bytes().unwrap();
    assert!(
      VerifierParams::<C>::from_bytes(&encoded[..encoded.len() - 1]).is_err()
    );
    let mut extra = encoded.clone();
    extra.push(0);
    assert!(VerifierParams::<C>::from_bytes(&extra).is_err());
    let mut unsupported_version = encoded;
    unsupported_version[..8].copy_from_slice(&0u64.to_le_bytes());
    assert!(VerifierParams::<C>::from_bytes(&unsupported_version).is_err());
    let mut bad = params.clone();
    bad.public_setup.max_degree = 31;
    assert!(VerifierParams::<C>::from_bytes(&bad.to_bytes().unwrap()).is_err());
    let mut bad = params;
    bad.g1[1] = bad.g1[0];
    assert!(VerifierParams::<C>::from_bytes(&bad.to_bytes().unwrap()).is_err());
  }

  #[test]
  fn verifier_params_round_trip_and_cross_curve_rejection() {
    check_verifier_params::<Bn254>(28);
    check_verifier_params::<Bls12381>(32);

    let bn = VerifierParams::<Bn254>::from_srs(
      &Srs::<Bn254>::unsafe_dev_setup(16, b"x"),
    )
    .to_bytes()
    .unwrap();
    let bls = VerifierParams::<Bls12381>::from_srs(
      &Srs::<Bls12381>::unsafe_dev_setup(16, b"x"),
    )
    .to_bytes()
    .unwrap();
    assert!(VerifierParams::<Bls12381>::from_bytes(&bn).is_err());
    assert!(VerifierParams::<Bn254>::from_bytes(&bls).is_err());
  }
}
