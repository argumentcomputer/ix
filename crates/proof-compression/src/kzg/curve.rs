//! Curve types and canonical encoding widths for the selected KZG backend.
//!
//! BN254 is the default backend; BLS12-381 is selected with
//! `--no-default-features --features bls12-381`. Encodings are arkworks canonical
//! encodings; these widths do not describe in-memory or EVM representations.

use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, Read, SerializationError,
};

#[cfg(not(feature = "bn254"))]
pub use ark_bls12_381::{
  Bls12_381 as PairingCurve, Fq, Fr, G1Affine, G1Projective, G2Affine,
  G2Projective,
};
#[cfg(feature = "bn254")]
pub use ark_bn254::{
  Bn254 as PairingCurve, Fq, Fr, G1Affine, G1Projective, G2Affine, G2Projective,
};

#[cfg(not(feature = "bn254"))]
pub const NAME: &str = "bls12-381";
#[cfg(feature = "bn254")]
pub const NAME: &str = "bn254";

#[cfg(not(feature = "bn254"))]
pub const G1_COMPRESSED_BYTES: usize = 48;
#[cfg(feature = "bn254")]
pub const G1_COMPRESSED_BYTES: usize = 32;

pub const G1_UNCOMPRESSED_BYTES: usize = G1_COMPRESSED_BYTES * 2;
pub const G2_COMPRESSED_BYTES: usize = G1_COMPRESSED_BYTES * 2;
pub const G2_UNCOMPRESSED_BYTES: usize = G2_COMPRESSED_BYTES * 2;

/// Decode one validated point with a unique compressed representation.
/// Arkworks' generic short-Weierstrass decoder ignores the x-coordinate
/// when the infinity flag is set, so validation alone permits aliases.
pub(crate) fn read_g1_compressed(
  input: &mut &[u8],
) -> Result<G1Affine, SerializationError> {
  let mut bytes = [0; G1_COMPRESSED_BYTES];
  input.read_exact(&mut bytes)?;
  let point = G1Affine::deserialize_compressed(bytes.as_slice())?;
  let mut canonical = [0; G1_COMPRESSED_BYTES];
  point.serialize_compressed(canonical.as_mut_slice())?;
  if bytes != canonical {
    return Err(SerializationError::InvalidData);
  }
  Ok(point)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::AffineRepr;

  #[test]
  fn canonical_point_widths_match_arkworks() {
    for point in [G1Affine::identity(), G1Affine::generator()] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), G1_COMPRESSED_BYTES);
      assert_eq!(G1Affine::deserialize_compressed(&*bytes).unwrap(), point);
      bytes.clear();
      point.serialize_uncompressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), G1_UNCOMPRESSED_BYTES);
      assert_eq!(G1Affine::deserialize_uncompressed(&*bytes).unwrap(), point);
    }
    for point in [G2Affine::identity(), G2Affine::generator()] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), G2_COMPRESSED_BYTES);
      assert_eq!(G2Affine::deserialize_compressed(&*bytes).unwrap(), point);
      bytes.clear();
      point.serialize_uncompressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), G2_UNCOMPRESSED_BYTES);
      assert_eq!(G2Affine::deserialize_uncompressed(&*bytes).unwrap(), point);
    }
  }

  #[test]
  fn canonical_point_reader_preserves_sign_and_consumes_one_point() {
    for point in
      [G1Affine::identity(), G1Affine::generator(), -G1Affine::generator()]
    {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      bytes.extend([0x12, 0x34]);
      let mut input = bytes.as_slice();
      assert_eq!(read_g1_compressed(&mut input).unwrap(), point);
      assert_eq!(input, &[0x12, 0x34]);
    }
  }

  #[test]
  fn canonical_point_reader_rejects_invalid_and_truncated_encodings() {
    let mut bytes = Vec::new();
    G1Affine::generator().serialize_compressed(&mut bytes).unwrap();
    assert!(
      read_g1_compressed(&mut &bytes[..G1_COMPRESSED_BYTES - 1]).is_err()
    );
    assert!(
      read_g1_compressed(&mut [0xff; G1_COMPRESSED_BYTES].as_slice()).is_err()
    );
  }

  #[cfg(feature = "bn254")]
  #[test]
  fn bn254_compressed_point_vectors() {
    let mut positive = [0; 32];
    positive[0] = 1;
    let mut negative = positive;
    negative[31] = 0x80;
    let mut infinity = [0; 32];
    infinity[31] = 0x40;
    for (point, expected) in [
      (G1Affine::generator(), positive),
      (-G1Affine::generator(), negative),
      (G1Affine::identity(), infinity),
    ] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      assert_eq!(bytes.as_slice(), expected.as_slice());
      assert_eq!(read_g1_compressed(&mut expected.as_slice()).unwrap(), point);
    }
  }

  #[cfg(feature = "bn254")]
  #[test]
  fn bn254_point_reader_rejects_infinity_alias_and_noncanonical_x() {
    use ark_ff::{BigInteger, PrimeField};

    let mut alias = [0; 32];
    alias[0] = 1;
    alias[31] = 0x40;
    assert_eq!(
      G1Affine::deserialize_compressed(alias.as_slice()).unwrap(),
      G1Affine::identity()
    );
    assert!(read_g1_compressed(&mut alias.as_slice()).is_err());
    assert!(
      read_g1_compressed(&mut Fq::MODULUS.to_bytes_le().as_slice()).is_err()
    );
  }
}
