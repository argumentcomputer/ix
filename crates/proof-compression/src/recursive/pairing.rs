//! Canonical public encoding of the two deferred KZG pairing operands.
//!
//! Each compressed point occupies two little-endian scalar limbs: 24 bytes
//! per limb for BLS12-381 and 16 for BN254. Both fit injectively in Fr.

use crate::kzg::{
  Scalar,
  curve::{Fr, G1_COMPRESSED_BYTES, G1Affine, read_g1_compressed},
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalSerialize, SerializationError};

pub const POINT_LIMB_BYTES: usize = G1_COMPRESSED_BYTES / 2;
pub const PUBLIC_VALUES: usize = 4;
const _: () = assert!(
  POINT_LIMB_BYTES.is_multiple_of(8)
    && G1_COMPRESSED_BYTES == 2 * POINT_LIMB_BYTES
    && POINT_LIMB_BYTES * 8 < Fr::MODULUS_BIT_SIZE as usize
);

pub fn encode(points: [G1Affine; 2]) -> [Scalar; PUBLIC_VALUES] {
  let mut bytes = [0; 2 * G1_COMPRESSED_BYTES];
  let mut output = bytes.as_mut_slice();
  for point in points {
    point.serialize_compressed(&mut output).expect("fixed point width");
  }
  std::array::from_fn(|i| {
    Scalar(Fr::from_le_bytes_mod_order(
      &bytes[i * POINT_LIMB_BYTES..(i + 1) * POINT_LIMB_BYTES],
    ))
  })
}

pub fn decode(values: &[Scalar]) -> Result<[G1Affine; 2], SerializationError> {
  if values.len() != PUBLIC_VALUES {
    return Err(SerializationError::InvalidData);
  }
  let mut bytes = [0; 2 * G1_COMPRESSED_BYTES];
  for (value, chunk) in
    values.iter().zip(bytes.as_chunks_mut::<POINT_LIMB_BYTES>().0)
  {
    let limbs = value.canonical_limbs_le();
    let scalar_bytes: [u8; 32] =
      std::array::from_fn(|i| limbs[i / 8].to_le_bytes()[i % 8]);
    if scalar_bytes[POINT_LIMB_BYTES..].iter().any(|&byte| byte != 0) {
      return Err(SerializationError::InvalidData);
    }
    chunk.copy_from_slice(&scalar_bytes[..POINT_LIMB_BYTES]);
  }
  let mut input = bytes.as_slice();
  Ok([read_g1_compressed(&mut input)?, read_g1_compressed(&mut input)?])
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::{AffineRepr, CurveGroup};
  use multi_stark::traits::Algebra;

  #[test]
  fn public_pairing_encoding_preserves_both_points_and_flags() {
    let generator = G1Affine::generator();
    let multiple = (generator * Fr::from(7u8)).into_affine();
    for points in [
      [generator, multiple],
      [-generator, -multiple],
      [G1Affine::identity(), generator],
      [G1Affine::identity(); 2],
    ] {
      assert_eq!(decode(&encode(points)).unwrap(), points);
    }
    let positive = encode([generator; 2]);
    let negative = encode([-generator; 2]);
    let identity = encode([G1Affine::identity(); 2]);
    assert_ne!(positive, negative);
    assert_ne!(positive, identity);
    #[cfg(feature = "bn254")]
    {
      assert_eq!(positive[0], Scalar::ONE);
      assert_eq!(positive[1], Scalar::ZERO);
      assert_eq!(identity[0], Scalar::ZERO);
      assert_eq!(identity[1], Scalar::from_limbs_le([0, 1 << 62, 0, 0]));
      assert_eq!(negative[1], Scalar::from_limbs_le([0, 1 << 63, 0, 0]));
    }
    #[cfg(not(feature = "bn254"))]
    assert_eq!(
      identity,
      [
        Scalar(Fr::from(0xc0u8)),
        Scalar::ZERO,
        Scalar(Fr::from(0xc0u8)),
        Scalar::ZERO
      ]
    );
  }

  #[test]
  fn public_pairing_encoding_rejects_wrong_lengths_and_limb_aliases() {
    let values = encode([G1Affine::generator(); 2]);
    assert!(decode(&values[..3]).is_err());
    assert!(decode(&[Scalar::ZERO; 5]).is_err());
    let mut overflow = [0; 4];
    overflow[POINT_LIMB_BYTES / 8] = 1;
    for i in 0..4 {
      let mut bad = values;
      bad[i] += Scalar::from_limbs_le(overflow);
      assert!(decode(&bad).is_err());
    }
  }

  #[cfg(feature = "bn254")]
  #[test]
  fn bn254_public_pairing_encoding_rejects_noncanonical_infinity() {
    let mut values = encode([G1Affine::identity(); 2]);
    values[0] = Scalar::ONE;
    assert!(decode(&values).is_err());
  }
}
