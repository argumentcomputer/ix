use crate::kzg::{
  Scalar,
  curve::{Fr, G1_COMPRESSED_BYTES},
};
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
fn greater_than(
  b: &mut Builder,
  bytes: &ByteGadgets,
  input: &[ByteValue],
  bound: &[u8],
) -> Bool {
  assert_eq!(input.len(), bound.len());
  let mut borrow = b.constant(Scalar::ZERO);
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
          Scalar::from_u64(d.rem_euclid(256) as u64),
          Scalar::from_u8(u8::from(d < 0)),
        ])
      },
    );
    let diff = bytes.constrain_byte(b, out[0]);
    b.assert_bool(out[1]);
    let eq = b.linear_combination(
      &[
        (Scalar::NEG_ONE, value.value()),
        (Scalar::NEG_ONE, borrow),
        (Scalar::from_u16(256), out[1]),
        (Scalar::NEG_ONE, diff.value()),
      ],
      Scalar::from_u8(limit),
    );
    b.assert_zero(eq);
    borrow = out[1];
  }
  b.assert_bool(borrow)
}

pub fn scalar_bytes(
  b: &mut Builder,
  bytes: &ByteGadgets,
  v: Value,
) -> [ByteValue; 32] {
  let raw = b.hint_many::<32>("scalar bytes", &[v], |v| {
    let data: Vec<_> = v[0]
      .canonical_limbs_le()
      .into_iter()
      .flat_map(u64::to_le_bytes)
      .collect();
    Ok(std::array::from_fn(|i| Scalar::from_u8(data[i])))
  });
  constrain_scalar_bytes(b, bytes, v, &raw)
}

fn constrain_scalar_bytes(
  b: &mut Builder,
  bytes: &ByteGadgets,
  v: Value,
  raw: &[Value; 32],
) -> [ByteValue; 32] {
  let result = std::array::from_fn(|i| bytes.constrain_byte(b, raw[i]));
  let mut coeff = Scalar::ONE;
  let terms: Vec<_> = raw
    .iter()
    .copied()
    .map(|v| {
      let term = (coeff, v);
      coeff *= Scalar::from_u16(256);
      term
    })
    .collect();
  let packed = b.linear_combination(&terms, Scalar::ZERO);
  b.assert_equal(packed, v);
  let modulus = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le()) - 1u8;
  let mut bound = modulus.to_bytes_le();
  bound.resize(32, 0);
  let invalid = greater_than(b, bytes, &result, &bound);
  b.assert_zero(invalid.value());
  result
}

pub fn fq_bytes(
  b: &mut Builder,
  bytes: &ByteGadgets,
  v: FqVar,
) -> [ByteValue; G1_COMPRESSED_BYTES] {
  let mut result = Vec::new();
  for (i, &limb) in v.0.iter().enumerate() {
    let raw = b.hint_many_pure::<{ W / 8 }>("Fq limb bytes", &[limb], |v| {
      let mut data = integer(v[0]).to_bytes_le();
      data.resize(W / 8, 0);
      Ok(std::array::from_fn(|i| Scalar::from_u8(data[i])))
    });
    let values = raw.map(|v| bytes.constrain_byte(b, v));
    let mut coeff = Scalar::ONE;
    let terms: Vec<_> = raw
      .into_iter()
      .map(|v| {
        let term = (coeff, v);
        coeff *= Scalar::from_u16(256);
        term
      })
      .collect();
    let packed = b.linear_combination(&terms, Scalar::ZERO);
    b.assert_equal(packed, limb);
    let used = (G1_COMPRESSED_BYTES - i * (W / 8)).min(W / 8);
    for &unused in &raw[used..] {
      b.assert_zero(unused);
    }
    result.extend_from_slice(&values[..used]);
  }
  result.try_into().unwrap()
}

/// The point must have canonical coordinates, with zero coordinates at infinity.
pub fn point_bytes(
  b: &mut Builder,
  bytes: &ByteGadgets,
  p: PointInput,
) -> [ByteValue; G1_COMPRESSED_BYTES] {
  let x = fq_bytes(b, bytes, p.point.x);
  let y = fq_bytes(b, bytes, p.point.y);
  let mut half = ((modulus() - 1u8) / 2u8).to_bytes_le();
  half.resize(G1_COMPRESSED_BYTES, 0);
  let sign = greater_than(b, bytes, &y, &half);
  #[cfg(not(feature = "bn254"))]
  let (sign_mask, compressed_mask) = (32, 128);
  #[cfg(feature = "bn254")]
  let (sign_mask, compressed_mask) = (128, 0);
  let flagged = b.linear_combination(
    &[
      (Scalar::ONE, x[G1_COMPRESSED_BYTES - 1].value()),
      (Scalar::from_u8(64), p.infinity.value()),
      (Scalar::from_u8(sign_mask), sign.value()),
    ],
    Scalar::from_u8(compressed_mask),
  );
  let flagged = bytes.constrain_byte(b, flagged);
  #[cfg(not(feature = "bn254"))]
  let result = std::array::from_fn(|i| {
    if i == 0 { flagged } else { x[G1_COMPRESSED_BYTES - 1 - i] }
  });
  #[cfg(feature = "bn254")]
  let result = std::array::from_fn(|i| {
    if i == G1_COMPRESSED_BYTES - 1 { flagged } else { x[i] }
  });
  result
}

pub struct Transcript {
  state: [ByteValue; 32],
  buffer: Vec<ByteValue>,
}
impl Transcript {
  pub fn new(b: &mut Builder, bytes: &ByteGadgets, seed: &[u8]) -> Self {
    Self {
      state: [bytes.constant(b, 0); 32],
      buffer: seed.iter().map(|&v| bytes.constant(b, v)).collect(),
    }
  }
  pub fn observe(&mut self, values: &[ByteValue]) {
    self.buffer.extend_from_slice(values);
  }
  pub fn constant(
    &mut self,
    b: &mut Builder,
    bytes: &ByteGadgets,
    data: &[u8],
  ) {
    self.buffer.extend(data.iter().map(|&v| bytes.constant(b, v)));
  }
  #[cfg(test)]
  pub fn scalar(&mut self, b: &mut Builder, bytes: &ByteGadgets, v: Value) {
    self.observe(&scalar_bytes(b, bytes, v));
  }
  pub fn sample(&mut self, b: &mut Builder, bytes: &ByteGadgets) -> Value {
    let mut input = self.state.to_vec();
    input.append(&mut self.buffer);
    let out = blake3_xof(b, bytes, &input, 96);
    self.state.copy_from_slice(&out[64..]);
    let mut coeff = Scalar::ONE;
    let terms: Vec<_> = out[..64]
      .iter()
      .map(|v| {
        let term = (coeff, v.value());
        coeff *= Scalar::from_u16(256);
        term
      })
      .collect();
    b.linear_combination(&terms, Scalar::ZERO)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::Blake3Transcript;
  use crate::kzg::curve::G1Affine;
  use crate::recursive::{native_curve::PointInput, native_field::FqGadget};
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_serialize::CanonicalSerialize;
  use multi_stark::traits::Transcript as _;
  #[test]
  fn transcript_and_point_encoding_match_native() {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    let p = PointInput::new(&mut b, &f, "point");
    let encoded = point_bytes(&mut b, &bytes, p);
    let v = b.input("scalar");
    let mut t = Transcript::new(&mut b, &bytes, b"test");
    t.observe(&encoded);
    t.scalar(&mut b, &bytes, v);
    let first = t.sample(&mut b, &bytes);
    let second = t.sample(&mut b, &bytes);
    let c = b.finish();
    let g = G1Affine::generator();
    for (n, pval) in [
      G1Affine::identity(),
      g,
      -g,
      (g * Fr::from(2u8)).into_affine(),
      (g * Fr::from(17u8)).into_affine(),
      (g * Fr::from(u64::MAX)).into_affine(),
    ]
    .into_iter()
    .enumerate()
    {
      let scalar = Scalar(-Fr::from(n as u64 + 1));
      let mut w = c.witness();
      for (v, n) in p.inputs(pval) {
        w.set(v, n).unwrap();
      }
      w.set(v, scalar).unwrap();
      let a = w.generate().unwrap();
      let mut expected = vec![];
      pval.serialize_compressed(&mut expected).unwrap();
      assert_eq!(expected.len(), encoded.len());
      for (v, &n) in encoded.iter().zip(&expected) {
        assert_eq!(a.value(v.value()).unwrap(), Scalar::from_u8(n));
      }
      let mut t = Blake3Transcript::new();
      t.observe_bytes(b"test");
      t.observe_bytes(&expected);
      t.observe_field(scalar);
      assert_eq!(a.value(first).unwrap(), t.sample_challenge());
      assert_eq!(a.value(second).unwrap(), t.sample_challenge());
    }
  }

  #[test]
  fn scalar_encoding_rejects_modulus_aliases() {
    let mut b = Builder::new();
    let bytes = ByteGadgets::new(&mut b);
    let v = b.input("scalar");
    let encoded = scalar_bytes(&mut b, &bytes, v);
    let supplied = std::array::from_fn(|i| b.input(format!("byte{i}")));
    constrain_scalar_bytes(&mut b, &bytes, v, &supplied);
    let c = b.finish();
    let modulus = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    for integer in [
      BigUint::from(0u8),
      BigUint::from(1u8),
      BigUint::from(1u8) << (Fr::MODULUS_BIT_SIZE - 1),
      &modulus - 1u8,
      modulus.clone(),
      &modulus + 1u8,
      (BigUint::from(1u8) << 256) - 1u8,
    ] {
      let mut data = integer.to_bytes_le();
      data.resize(32, 0);
      let mut w = c.witness();
      w.set(v, Scalar(Fr::from_le_bytes_mod_order(&data))).unwrap();
      for (handle, &byte) in supplied.iter().zip(&data) {
        w.set(*handle, Scalar::from_u8(byte)).unwrap();
      }
      if integer < modulus {
        let a = w.generate().unwrap();
        for (handle, &byte) in encoded.iter().zip(&data) {
          assert_eq!(a.value(handle.value()).unwrap(), Scalar::from_u8(byte));
        }
      } else {
        assert!(w.generate().is_err());
      }
    }
  }

  #[test]
  fn coordinate_bytes_reject_truncation() {
    use crate::recursive::native_field::{L, scalar};

    let mut b = Builder::new();
    let bytes = ByteGadgets::new(&mut b);
    let coordinate =
      FqVar(std::array::from_fn(|i| b.input(format!("limb{i}"))));
    fq_bytes(&mut b, &bytes, coordinate);
    let c = b.finish();
    for changed in 0..L {
      let mut w = c.witness();
      let bits = (G1_COMPRESSED_BYTES * 8 - W * changed).min(W);
      for (i, handle) in coordinate.0.into_iter().enumerate() {
        let value = if i == changed {
          scalar(&(BigUint::from(1u8) << bits))
        } else {
          Scalar::ZERO
        };
        w.set(handle, value).unwrap();
      }
      assert!(w.generate().is_err());
    }
  }
}
