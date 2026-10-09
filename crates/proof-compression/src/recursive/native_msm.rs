use crate::kzg::Scalar;
use crate::recursive::native_curve::Affine;
use crate::recursive::native_curve::PointInput;
use crate::recursive::native_field::Builder;
use crate::recursive::native_field::FqGadget;
use crate::recursive::native_transcript::scalar_bytes;
use ark_bls12_381::{Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use multi_stark::plonkish::Bool;
use multi_stark::plonkish::Value;
use multi_stark::plonkish::gadgets::ByteGadgets;
use multi_stark::traits::Algebra;

pub struct Base {
  pub point: PointInput,
  pub fixed: Option<G1Affine>,
  table: Option<[Affine; 16]>,
}
impl Base {
  pub fn new(point: PointInput, fixed: Option<G1Affine>) -> Self {
    Self { point, fixed, table: None }
  }
  fn table(&mut self, b: &mut Builder, f: &FqGadget) -> [Affine; 16] {
    if let Some(table) = self.table {
      return table;
    }
    let p = self.point.nonzero(b, f);
    let mut table = [p; 16];
    if let Some(point) = self.fixed {
      let point = if point.infinity { G1Affine::generator() } else { point };
      table = std::array::from_fn(|i| {
        Affine::constant(b, f, (point * Fr::from((i + 1) as u64)).into_affine())
      });
    } else {
      for n in 2..=16 {
        table[n - 1] = if n % 2 == 0 {
          table[n / 2 - 1].double(b, f)
        } else {
          table[n - 2].add(b, f, p)
        };
      }
    }
    self.table = Some(table);
    table
  }
}
fn select(b: &mut Builder, table: &[Affine; 16], bits: &[Bool]) -> Affine {
  let mut layer = table.to_vec();
  for &bit in bits {
    layer = layer
      .as_chunks::<2>()
      .0
      .iter()
      .map(|pair| Affine::select(b, bit, pair[1], pair[0]))
      .collect();
  }
  layer[0]
}
fn constant_mul(b: &mut Builder, f: &FqGadget, p: Affine, n: Fr) -> Affine {
  let bits = n.into_bigint().to_bits_be();
  let first = bits.iter().position(|&v| v).expect("nonzero multiplier");
  let mut acc = p;
  for &bit in &bits[first + 1..] {
    acc = acc.double(b, f);
    if bit {
      acc = acc.add(b, f, p);
    }
  }
  acc
}
pub fn negate(b: &mut Builder, f: &FqGadget, p: Affine) -> Affine {
  let y = f.hint(b, "negative y", &[p.y], |v| Ok(-v[0]));
  f.relation(b, &[], &[(1, p.y), (1, y)], 0);
  Affine { x: p.x, y }
}

/// Fixed-shape four-bit Straus MSM. Offsets avoid zero digits; constrained
/// inverses reject exceptional intermediate sums, never bypass them.
pub fn msm(
  b: &mut Builder,
  f: &FqGadget,
  bytes: &ByteGadgets,
  bases: &mut [Base],
  terms: &[(usize, Value)],
  tag: &str,
) -> Affine {
  assert!(!terms.is_empty());
  let mut wide = [0; 64];
  blake3::Hasher::new()
    .update(b"kzg-wrap/msm-offset/v1")
    .update(tag.as_bytes())
    .finalize_xof()
    .fill(&mut wide);
  let h =
    (G1Affine::generator() * Fr::from_le_bytes_mod_order(&wide)).into_affine();
  let mut sum = Affine::constant(b, f, h);
  let mut tables = Vec::new();
  let mut digits = Vec::new();
  for &(id, scalar) in terms {
    let base = &mut bases[id];
    let zero = b.constant(Scalar::ZERO);
    let scalar = b.select(base.point.infinity, zero, scalar);
    let enc = scalar_bytes(b, bytes, scalar);
    digits
      .push(enc.into_iter().flat_map(|v| bytes.bits(b, v)).collect::<Vec<_>>());
    let table = base.table(b, f);
    sum = sum.add(b, f, table[0]);
    tables.push(table);
  }
  let mut acc = Affine::constant(b, f, h);
  for window in (0..64).rev() {
    for _ in 0..4 {
      acc = acc.double(b, f);
    }
    for (table, bits) in tables.iter().zip(&digits) {
      let p = select(b, table, &bits[4 * window..4 * window + 4]);
      acc = acc.add(b, f, p);
    }
  }
  let mut k = Fr::from(0u8);
  let mut power = Fr::from(1u8);
  for _ in 0..64 {
    k += power;
    power *= Fr::from(16u8);
  }
  let ks = constant_mul(b, f, sum, k);
  let correction = Affine::constant(b, f, (h * (power - k)).into_affine());
  let correction = ks.add(b, f, correction);
  let neg = negate(b, f, correction);
  acc.add(b, f, neg)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::recursive::native_field::fq_value;
  #[test]
  fn msm_matches_native_with_zero_scalars_and_identity() {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    let points: Vec<_> =
      (0..3).map(|i| PointInput::new(&mut b, &f, &format!("p{i}"))).collect();
    let mut bases: Vec<_> =
      points.iter().map(|&p| Base::new(p, None)).collect();
    let scalars: Vec<_> = (0..3).map(|i| b.input(format!("s{i}"))).collect();
    let terms: Vec<_> =
      scalars.iter().enumerate().map(|(i, &v)| (i, v)).collect();
    let result = msm(&mut b, &f, &bytes, &mut bases, &terms, "test");
    let c = b.finish();
    for (ns, ss) in [([2u64, 3, 7], [11u64, 0, 17]), ([0, 9, 11], [17, 91, 0])]
    {
      let mut w = c.witness();
      let mut expected = ark_bls12_381::G1Projective::default();
      for i in 0..3 {
        let p = (G1Affine::generator() * Fr::from(ns[i])).into_affine();
        let s = Fr::from(ss[i]);
        expected += p * s;
        for (v, n) in points[i].inputs(p) {
          w.set(v, n).unwrap();
        }
        w.set(scalars[i], Scalar(s)).unwrap();
      }
      let a = w.generate().unwrap();
      let actual = G1Affine::new_unchecked(
        fq_value(&result.x.0.map(|v| a.value(v).unwrap())),
        fq_value(&result.y.0.map(|v| a.value(v).unwrap())),
      );
      assert_eq!(actual, expected.into_affine());
    }
  }
}
