use crate::kzg::{curve::KzgCurve, field::CurveScalar};
use crate::recursive::{
  native_curve::PointInput,
  native_field::{Builder, FqVar, W, integer, modulus},
};
use ark_ff::{BigInteger, PrimeField};
use multi_stark::{
  plonkish::{
    Bool, Value,
    gadgets::{ByteGadgets, ByteValue, blake3_xof},
  },
  traits::{Algebra, Field},
};
use num_bigint::BigUint;

/// Final borrow of bound - bytes (both unsigned little endian).
fn greater_than<C: KzgCurve>(
  b: &mut Builder<C>,
  bytes: &ByteGadgets,
  input: &[ByteValue],
  bound: &[u8],
) -> Bool {
  assert_eq!(input.len(), bound.len());
  let mut borrow = b.constant(CurveScalar::<C>::ZERO);
  for (&value, &limit) in input.iter().zip(bound) {
    let out = b.hint_many_pure::<2>(
      "byte subtraction",
      &[value.value(), borrow],
      move |v| {
        let x = i64::try_from(v[0].canonical_limbs_le()[0])
          .map_err(|e| e.to_string())?;
        let d = i64::from(limit)
          - x
          - i64::try_from(v[1].canonical_limbs_le()[0])
            .map_err(|e| e.to_string())?;
        Ok([
          CurveScalar::<C>::from_u64(d.rem_euclid(256) as u64),
          CurveScalar::<C>::from_u8(u8::from(d < 0)),
        ])
      },
    );
    let diff = bytes.constrain_byte(b, out[0]);
    b.assert_bool(out[1]);
    let eq = b.linear_combination(
      &[
        (CurveScalar::<C>::NEG_ONE, value.value()),
        (CurveScalar::<C>::NEG_ONE, borrow),
        (CurveScalar::<C>::from_u16(256), out[1]),
        (CurveScalar::<C>::NEG_ONE, diff.value()),
      ],
      CurveScalar::<C>::from_u8(limit),
    );
    b.assert_zero(eq);
    borrow = out[1];
  }
  b.assert_bool(borrow)
}

pub fn scalar_bytes<C: KzgCurve>(
  b: &mut Builder<C>,
  bytes: &ByteGadgets,
  v: Value,
) -> [ByteValue; 32] {
  let raw = b.hint_many::<32>("scalar bytes", &[v], |v| {
    let data: Vec<_> = v[0]
      .canonical_limbs_le()
      .into_iter()
      .flat_map(u64::to_le_bytes)
      .collect();
    Ok(std::array::from_fn(|i| CurveScalar::<C>::from_u8(data[i])))
  });
  constrain_scalar_bytes(b, bytes, v, &raw)
}

fn constrain_scalar_bytes<C: KzgCurve>(
  b: &mut Builder<C>,
  bytes: &ByteGadgets,
  v: Value,
  raw: &[Value; 32],
) -> [ByteValue; 32] {
  let result = std::array::from_fn(|i| bytes.constrain_byte(b, raw[i]));
  let mut coeff = CurveScalar::<C>::ONE;
  let terms: Vec<_> = raw
    .iter()
    .copied()
    .map(|v| {
      let term = (coeff, v);
      coeff *= CurveScalar::<C>::from_u16(256);
      term
    })
    .collect();
  let packed = b.linear_combination(&terms, CurveScalar::<C>::ZERO);
  b.assert_equal(packed, v);
  let modulus = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le()) - 1u8;
  let mut bound = modulus.to_bytes_le();
  bound.resize(32, 0);
  let invalid = greater_than(b, bytes, &result, &bound);
  b.assert_zero(invalid.value());
  result
}

pub fn fq_bytes<C: KzgCurve>(
  b: &mut Builder<C>,
  bytes: &ByteGadgets,
  v: FqVar<C>,
) -> Vec<ByteValue> {
  let width = C::G1_COMPRESSED_BYTES;
  let mut result = Vec::with_capacity(width);
  for (i, &limb) in v.limbs().iter().enumerate() {
    let raw = b.hint_many_pure::<{ W / 8 }>("Fq limb bytes", &[limb], |v| {
      let mut data = integer(v[0]).to_bytes_le();
      data.resize(W / 8, 0);
      Ok(std::array::from_fn(|i| CurveScalar::<C>::from_u8(data[i])))
    });
    let values = raw.map(|v| bytes.constrain_byte(b, v));
    let mut coeff = CurveScalar::<C>::ONE;
    let terms: Vec<_> = raw
      .into_iter()
      .map(|v| {
        let term = (coeff, v);
        coeff *= CurveScalar::<C>::from_u16(256);
        term
      })
      .collect();
    let packed = b.linear_combination(&terms, CurveScalar::<C>::ZERO);
    b.assert_equal(packed, limb);
    let used = (width - i * (W / 8)).min(W / 8);
    for &unused in &raw[used..] {
      b.assert_zero(unused);
    }
    result.extend_from_slice(&values[..used]);
  }
  assert_eq!(result.len(), width);
  result
}

/// The point must have canonical coordinates, with zero coordinates at infinity.
pub fn point_bytes<C: KzgCurve>(
  b: &mut Builder<C>,
  bytes: &ByteGadgets,
  p: PointInput<C>,
) -> Vec<ByteValue> {
  let width = C::G1_COMPRESSED_BYTES;
  let x = fq_bytes(b, bytes, p.point.x);
  let y = fq_bytes(b, bytes, p.point.y);
  let mut half = ((modulus::<C>() - 1u8) / 2u8).to_bytes_le();
  half.resize(width, 0);
  let sign = greater_than(b, bytes, &y, &half);
  let flagged = b.linear_combination(
    &[
      (CurveScalar::<C>::ONE, x[width - 1].value()),
      (CurveScalar::<C>::from_u8(64), p.infinity.value()),
      (CurveScalar::<C>::from_u8(C::COMPRESSED_SIGN_MASK), sign.value()),
    ],
    CurveScalar::<C>::from_u8(C::COMPRESSED_FLAG_MASK),
  );
  let flagged = bytes.constrain_byte(b, flagged);
  if C::COMPRESSED_BIG_ENDIAN {
    (0..width)
      .map(|i| if i == 0 { flagged } else { x[width - 1 - i] })
      .collect()
  } else {
    (0..width).map(|i| if i == width - 1 { flagged } else { x[i] }).collect()
  }
}

pub struct Transcript {
  state: [ByteValue; 32],
  buffer: Vec<ByteValue>,
}
impl Transcript {
  pub fn new<C: KzgCurve>(
    b: &mut Builder<C>,
    bytes: &ByteGadgets,
    seed: &[u8],
  ) -> Self {
    Self {
      state: [bytes.constant(b, 0); 32],
      buffer: seed.iter().map(|&v| bytes.constant(b, v)).collect(),
    }
  }
  pub fn observe(&mut self, values: &[ByteValue]) {
    self.buffer.extend_from_slice(values);
  }
  pub fn constant<C: KzgCurve>(
    &mut self,
    b: &mut Builder<C>,
    bytes: &ByteGadgets,
    data: &[u8],
  ) {
    self.buffer.extend(data.iter().map(|&v| bytes.constant(b, v)));
  }
  #[cfg(test)]
  pub fn scalar<C: KzgCurve>(
    &mut self,
    b: &mut Builder<C>,
    bytes: &ByteGadgets,
    v: Value,
  ) {
    self.observe(&scalar_bytes(b, bytes, v));
  }
  pub fn sample<C: KzgCurve>(
    &mut self,
    b: &mut Builder<C>,
    bytes: &ByteGadgets,
  ) -> Value {
    let mut input = self.state.to_vec();
    input.append(&mut self.buffer);
    let out = blake3_xof(b, bytes, &input, 96);
    self.state.copy_from_slice(&out[64..]);
    let mut coeff = CurveScalar::<C>::ONE;
    let terms: Vec<_> = out[..64]
      .iter()
      .map(|v| {
        let term = (coeff, v.value());
        coeff *= CurveScalar::<C>::from_u16(256);
        term
      })
      .collect();
    b.linear_combination(&terms, CurveScalar::<C>::ZERO)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::{
    Blake3Transcript,
    curve::{Bls12381, Bn254, G1AffineOf},
  };
  use crate::recursive::{
    native_curve::PointInput,
    native_field::{FqGadget, limb_count, scalar},
  };
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_serialize::CanonicalSerialize;
  use multi_stark::traits::Transcript as _;

  fn test_transcript_and_point_encoding<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    let p = PointInput::<C>::new(&mut b, &f, "point");
    let encoded = point_bytes(&mut b, &bytes, p);
    let v = b.input("scalar");
    let mut t = Transcript::new(&mut b, &bytes, b"test");
    t.observe(&encoded);
    t.scalar(&mut b, &bytes, v);
    let first = t.sample(&mut b, &bytes);
    let second = t.sample(&mut b, &bytes);
    let c = b.finish();
    let g = G1AffineOf::<C>::generator();
    for (n, pval) in [
      G1AffineOf::<C>::identity(),
      g,
      -g,
      (g * C::Fr::from(2u8)).into_affine(),
      (g * C::Fr::from(17u8)).into_affine(),
      (g * C::Fr::from(u64::MAX)).into_affine(),
    ]
    .into_iter()
    .enumerate()
    {
      let scalar_val = CurveScalar::<C>(-C::Fr::from(n as u64 + 1));
      let mut w = c.witness();
      for (v, n) in p.inputs(pval) {
        w.set(v, n).unwrap();
      }
      w.set(v, scalar_val).unwrap();
      let a = w.generate().unwrap();
      let mut expected = vec![];
      pval.serialize_compressed(&mut expected).unwrap();
      assert_eq!(expected.len(), encoded.len());
      for (v, &n) in encoded.iter().zip(&expected) {
        assert_eq!(a.value(v.value()).unwrap(), CurveScalar::<C>::from_u8(n));
      }
      let mut t = Blake3Transcript::<C>::new();
      t.observe_bytes(b"test");
      t.observe_bytes(&expected);
      t.observe_field(scalar_val);
      assert_eq!(a.value(first).unwrap(), t.sample_challenge());
      assert_eq!(a.value(second).unwrap(), t.sample_challenge());
    }
  }

  #[test]
  fn transcript_and_point_encoding_match_native() {
    test_transcript_and_point_encoding::<Bn254>();
    test_transcript_and_point_encoding::<Bls12381>();
  }

  fn test_scalar_encoding_rejects_modulus_aliases<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let bytes = ByteGadgets::new(&mut b);
    let v = b.input("scalar");
    let encoded = scalar_bytes(&mut b, &bytes, v);
    let supplied = std::array::from_fn(|i| b.input(format!("byte{i}")));
    constrain_scalar_bytes(&mut b, &bytes, v, &supplied);
    let c = b.finish();
    let modulus = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le());
    for integer in [
      BigUint::from(0u8),
      BigUint::from(1u8),
      BigUint::from(1u8) << (C::Fr::MODULUS_BIT_SIZE - 1),
      &modulus - 1u8,
      modulus.clone(),
      &modulus + 1u8,
      (BigUint::from(1u8) << 256) - 1u8,
    ] {
      let mut data = integer.to_bytes_le();
      data.resize(32, 0);
      let mut w = c.witness();
      w.set(v, CurveScalar::<C>(C::Fr::from_le_bytes_mod_order(&data)))
        .unwrap();
      for (handle, &byte) in supplied.iter().zip(&data) {
        w.set(*handle, CurveScalar::<C>::from_u8(byte)).unwrap();
      }
      if integer < modulus {
        let a = w.generate().unwrap();
        for (handle, &byte) in encoded.iter().zip(&data) {
          assert_eq!(
            a.value(handle.value()).unwrap(),
            CurveScalar::<C>::from_u8(byte)
          );
        }
      } else {
        assert!(w.generate().is_err());
      }
    }
  }

  #[test]
  fn scalar_encoding_rejects_modulus_aliases() {
    test_scalar_encoding_rejects_modulus_aliases::<Bn254>();
    test_scalar_encoding_rejects_modulus_aliases::<Bls12381>();
  }

  fn test_coordinate_bytes_reject_truncation<C: KzgCurve>() {
    let l = limb_count::<C>();
    let mut b = Builder::<C>::new();
    let bytes = ByteGadgets::new(&mut b);
    let coordinate = FqVar::<C>::from_fn(|i| b.input(format!("limb{i}")));
    fq_bytes(&mut b, &bytes, coordinate);
    let c = b.finish();
    for changed in 0..l {
      let mut w = c.witness();
      let bits = (C::G1_COMPRESSED_BYTES * 8 - W * changed).min(W);
      for (i, &handle) in coordinate.limbs().iter().enumerate() {
        let value = if i == changed {
          scalar::<C>(&(BigUint::from(1u8) << bits))
        } else {
          CurveScalar::<C>::ZERO
        };
        w.set(handle, value).unwrap();
      }
      assert!(w.generate().is_err());
    }
  }

  #[test]
  fn coordinate_bytes_reject_truncation() {
    test_coordinate_bytes_reject_truncation::<Bn254>();
    test_coordinate_bytes_reject_truncation::<Bls12381>();
  }
}
