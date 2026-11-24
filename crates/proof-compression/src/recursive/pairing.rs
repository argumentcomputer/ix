//! Canonical public encoding of the two deferred KZG pairing operands.
//!
//! Each compressed point occupies two little-endian scalar limbs: 24 bytes
//! per limb for BLS12-381 and 16 for BN254. Both fit injectively in Fr.

use crate::kzg::{
  curve::{Bls12381, Bn254, G1AffineOf, KzgCurve, read_g1_compressed_for},
  field::CurveScalar,
};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalSerialize, SerializationError};

pub const POINT_LIMB_BYTES: usize = Bn254::POINT_LIMB_BYTES;
pub const PUBLIC_VALUES: usize = 4;

const _: () = {
  assert!(
    Bn254::POINT_LIMB_BYTES.is_multiple_of(8)
      && Bn254::G1_COMPRESSED_BYTES == 2 * Bn254::POINT_LIMB_BYTES
      && Bn254::POINT_LIMB_BYTES * 8
        < <ark_bn254::Fr as PrimeField>::MODULUS_BIT_SIZE as usize
  );
  assert!(
    Bls12381::POINT_LIMB_BYTES.is_multiple_of(8)
      && Bls12381::G1_COMPRESSED_BYTES == 2 * Bls12381::POINT_LIMB_BYTES
      && Bls12381::POINT_LIMB_BYTES * 8
        < <ark_bls12_381::Fr as PrimeField>::MODULUS_BIT_SIZE as usize
  );
};

pub fn encode<C: KzgCurve>(
  points: [G1AffineOf<C>; 2],
) -> [CurveScalar<C>; PUBLIC_VALUES] {
  let width = C::G1_COMPRESSED_BYTES;
  let limb_bytes = C::POINT_LIMB_BYTES;
  let mut buf = [0u8; 96];
  let bytes = &mut buf[..2 * width];
  {
    let mut output = &mut bytes[..];
    for point in points {
      point.serialize_compressed(&mut output).expect("fixed point width");
    }
  }
  std::array::from_fn(|i| {
    CurveScalar::<C>(C::Fr::from_le_bytes_mod_order(
      &bytes[i * limb_bytes..(i + 1) * limb_bytes],
    ))
  })
}

pub fn decode<C: KzgCurve>(
  values: &[CurveScalar<C>],
) -> Result<[G1AffineOf<C>; 2], SerializationError> {
  if values.len() != PUBLIC_VALUES {
    return Err(SerializationError::InvalidData);
  }
  let width = C::G1_COMPRESSED_BYTES;
  let limb_bytes = C::POINT_LIMB_BYTES;
  let mut buf = [0u8; 96];
  let bytes = &mut buf[..2 * width];
  for (value, chunk) in values.iter().zip(bytes.chunks_exact_mut(limb_bytes)) {
    let limbs = value.canonical_limbs_le();
    let scalar_bytes: [u8; 32] =
      std::array::from_fn(|i| limbs[i / 8].to_le_bytes()[i % 8]);
    if scalar_bytes[limb_bytes..].iter().any(|&byte| byte != 0) {
      return Err(SerializationError::InvalidData);
    }
    chunk.copy_from_slice(&scalar_bytes[..limb_bytes]);
  }
  let mut input = &bytes[..];
  Ok([
    read_g1_compressed_for::<C>(&mut input)?,
    read_g1_compressed_for::<C>(&mut input)?,
  ])
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::{AffineRepr, CurveGroup};
  use multi_stark::traits::Algebra;

  fn test_roundtrip<C: KzgCurve>() {
    let generator = G1AffineOf::<C>::generator();
    let multiple = (generator * C::Fr::from(7u8)).into_affine();
    for points in [
      [generator, multiple],
      [-generator, -multiple],
      [G1AffineOf::<C>::identity(), generator],
      [G1AffineOf::<C>::identity(); 2],
    ] {
      assert_eq!(decode::<C>(&encode::<C>(points)).unwrap(), points);
    }
    let positive = encode::<C>([generator; 2]);
    let negative = encode::<C>([-generator; 2]);
    let identity = encode::<C>([G1AffineOf::<C>::identity(); 2]);
    assert_ne!(positive, negative);
    assert_ne!(positive, identity);
  }

  #[test]
  fn public_pairing_encoding_preserves_both_points_and_flags() {
    test_roundtrip::<Bn254>();
    test_roundtrip::<Bls12381>();

    let bn_gen = G1AffineOf::<Bn254>::generator();
    let bn_pos = encode::<Bn254>([bn_gen; 2]);
    let bn_neg = encode::<Bn254>([-bn_gen; 2]);
    let bn_id = encode::<Bn254>([G1AffineOf::<Bn254>::identity(); 2]);
    assert_eq!(bn_pos[0], CurveScalar::<Bn254>::ONE);
    assert_eq!(bn_pos[1], CurveScalar::<Bn254>::ZERO);
    assert_eq!(bn_id[0], CurveScalar::<Bn254>::ZERO);
    assert_eq!(
      bn_id[1],
      CurveScalar::<Bn254>::from_limbs_le([0, 1 << 62, 0, 0])
    );
    assert_eq!(
      bn_neg[1],
      CurveScalar::<Bn254>::from_limbs_le([0, 1 << 63, 0, 0])
    );

    let bls_id = encode::<Bls12381>([G1AffineOf::<Bls12381>::identity(); 2]);
    assert_eq!(
      bls_id,
      [
        CurveScalar::<Bls12381>(ark_bls12_381::Fr::from(0xc0u8)),
        CurveScalar::<Bls12381>::ZERO,
        CurveScalar::<Bls12381>(ark_bls12_381::Fr::from(0xc0u8)),
        CurveScalar::<Bls12381>::ZERO,
      ]
    );
  }

  fn test_rejects_lengths_and_aliases<C: KzgCurve>() {
    let values = encode::<C>([G1AffineOf::<C>::generator(); 2]);
    assert!(decode::<C>(&values[..3]).is_err());
    assert!(decode::<C>(&[CurveScalar::<C>::ZERO; 5]).is_err());
    let mut overflow = [0; 4];
    overflow[C::POINT_LIMB_BYTES / 8] = 1;
    for i in 0..4 {
      let mut bad = values;
      bad[i] += CurveScalar::<C>::from_limbs_le(overflow);
      assert!(decode::<C>(&bad).is_err());
    }
  }

  #[test]
  fn public_pairing_encoding_rejects_wrong_lengths_and_limb_aliases() {
    test_rejects_lengths_and_aliases::<Bn254>();
    test_rejects_lengths_and_aliases::<Bls12381>();
  }

  #[test]
  fn public_pairing_encoding_rejects_noncanonical_infinity_both_curves() {
    let mut bn_values = encode::<Bn254>([G1AffineOf::<Bn254>::identity(); 2]);
    bn_values[0] = CurveScalar::<Bn254>::ONE;
    assert!(decode::<Bn254>(&bn_values).is_err());

    let mut bls_values =
      encode::<Bls12381>([G1AffineOf::<Bls12381>::identity(); 2]);
    bls_values[1] = CurveScalar::<Bls12381>::ONE;
    assert!(decode::<Bls12381>(&bls_values).is_err());
  }
}
