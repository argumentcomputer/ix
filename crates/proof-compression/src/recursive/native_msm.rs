use crate::kzg::Scalar;
use crate::recursive::{
  native_curve::{Affine, PointInput},
  native_field::{Builder, FqGadget, FqVar, fq_value},
  native_transcript::scalar_bytes,
};
use ark_bls12_381::{Fr, G1Affine, G1Projective};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use multi_stark::{
  plonkish::{Bool, Value, gadgets::ByteGadgets},
  traits::Algebra,
};

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
  let y = f.hint_pure(b, "negative y", &[p.y], |v| Ok(-v[0]));
  f.relation(b, &[], &[(1, p.y), (1, y)], 0);
  Affine { x: p.x, y }
}

fn correction_coefficients() -> (Fr, Fr) {
  let mut k = Fr::from(0u8);
  let mut power = Fr::from(1u8);
  for _ in 0..64 {
    k += power;
    power *= Fr::from(16u8);
  }
  let c = power - k;
  assert!(!k.is_zero() && !c.is_zero() && k != c && !power.is_zero());
  (k, c)
}

fn add_without_exception(lhs: &mut G1Projective, rhs: &G1Projective) -> bool {
  if lhs.is_zero()
    || rhs.is_zero()
    || lhs.x * rhs.z.square() == rhs.x * lhs.z.square()
  {
    return false;
  }
  *lhs += rhs;
  true
}

fn offset_is_safe(
  h: G1Projective,
  tables: &[[G1Projective; 16]],
  digits: &[[usize; 64]],
) -> bool {
  if h.is_zero() {
    return false;
  }
  let mut sum = h;
  for table in tables {
    if !add_without_exception(&mut sum, &table[0]) {
      return false;
    }
  }
  let mut acc = h;
  for window in (0..64).rev() {
    for _ in 0..4 {
      acc.double_in_place();
    }
    for (table, digit) in tables.iter().zip(digits) {
      if !add_without_exception(&mut acc, &table[digit[window]]) {
        return false;
      }
    }
  }
  let (k, c) = correction_coefficients();
  let mut correction = sum * k;
  add_without_exception(&mut correction, &(h * c))
}

fn choose_offset(
  points: &[G1Affine],
  scalars: &[Fr],
  first: Fr,
) -> Result<(G1Affine, usize), String> {
  let tables: Vec<_> = points
    .iter()
    .map(|p| {
      let p = G1Projective::from(*p);
      let mut table = [p; 16];
      for n in 2..=16 {
        table[n - 1] =
          if n % 2 == 0 { table[n / 2 - 1].double() } else { table[n - 2] + p };
      }
      table
    })
    .collect();
  let digits: Vec<_> = scalars
    .iter()
    .map(|s| {
      let limbs = s.into_bigint();
      std::array::from_fn(|window| {
        ((limbs.as_ref()[window / 16] >> (4 * (window % 16))) & 15) as usize
      })
    })
    .collect();
  let attempts = points
    .len()
    .checked_mul(130)
    .and_then(|n| n.checked_add(4))
    .ok_or("MSM term count overflow")?;
  let generator = G1Affine::generator();
  let mut h = generator * first;
  for attempt in 1..=attempts {
    if offset_is_safe(h, &tables, &digits) {
      return Ok((h.into_affine(), attempt));
    }
    h += generator;
  }
  Err("no valid affine MSM offset".into())
}

fn witness_offset(
  b: &mut Builder,
  f: &FqGadget,
  bases: &[Base],
  terms: &[(usize, Value)],
  tag: &str,
) -> Affine {
  let mut wide = [0; 64];
  blake3::Hasher::new()
    .update(b"kzg-wrap/msm-offset/v1")
    .update(tag.as_bytes())
    .finalize_xof()
    .fill(&mut wide);
  let first = Fr::from_le_bytes_mod_order(&wide);
  let deps: Vec<_> = terms
    .iter()
    .flat_map(|&(id, scalar)| {
      let point = bases[id].point;
      point
        .point
        .x
        .0
        .into_iter()
        .chain(point.point.y.0)
        .chain([point.infinity.value(), scalar])
    })
    .collect();
  let limbs = b.hint_many::<10>("nonexceptional MSM offset", &deps, move |v| {
    let mut points = Vec::with_capacity(v.len() / 12);
    let mut scalars = Vec::with_capacity(v.len() / 12);
    for values in v.as_chunks::<12>().0 {
      let infinity = values[10] == Scalar::ONE;
      if values[10] != Scalar::ZERO && !infinity {
        return Err("invalid point infinity flag".into());
      }
      let point = if infinity {
        G1Affine::generator()
      } else {
        G1Affine::new_unchecked(
          fq_value(&values[..5]),
          fq_value(&values[5..10]),
        )
      };
      if !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err("invalid MSM point".into());
      }
      points.push(point);
      scalars.push(if infinity { Fr::from(0u8) } else { values[11].0 });
    }
    let (offset, _) = choose_offset(&points, &scalars, first)?;
    let x = FqGadget::witness_values(offset.x);
    let y = FqGadget::witness_values(offset.y);
    Ok(std::array::from_fn(|i| if i < 5 { x[i] } else { y[i - 5] }))
  });
  let h = Affine {
    x: FqVar(limbs[..5].try_into().unwrap()),
    y: FqVar(limbs[5..].try_into().unwrap()),
  };
  for coordinate in [h.x, h.y] {
    f.bound(b, coordinate);
    f.canonical(b, coordinate);
  }
  h.on_curve(b, f);
  h.subgroup(b, f);
  h
}

/// Fixed-shape four-bit Straus MSM with a constrained, witness-selected offset.
/// For n bases, at most 130n + 3 subgroup offsets are excluded: each of the
/// 65n affine additions against a fixed multiple excludes at most two offsets,
/// the correction addition excludes two, and the identity excludes one. Every
/// intermediate is aH+B with nonzero a, so advancing H by the generator finds
/// a valid offset within 130n + 4 attempts. Constant multiplications use scalar
/// prefixes strictly below the subgroup order and introduce no further poles.
/// All inverse constraints remain enforced; the retry hint cannot bypass them.
pub fn msm(
  b: &mut Builder,
  f: &FqGadget,
  bytes: &ByteGadgets,
  bases: &mut [Base],
  terms: &[(usize, Value)],
  tag: &str,
) -> PointInput {
  assert!(!terms.is_empty());
  let offset = witness_offset(b, f, bases, terms, tag);
  msm_with_offset(b, f, bytes, bases, terms, offset)
}

fn msm_with_offset(
  b: &mut Builder,
  f: &FqGadget,
  bytes: &ByteGadgets,
  bases: &mut [Base],
  terms: &[(usize, Value)],
  h: Affine,
) -> PointInput {
  let mut sum = h;
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
  let mut acc = h;
  for window in (0..64).rev() {
    for _ in 0..4 {
      acc = acc.double(b, f);
    }
    for (table, bits) in tables.iter().zip(&digits) {
      let p = select(b, table, &bits[4 * window..4 * window + 4]);
      acc = acc.add(b, f, p);
    }
  }
  let (k, c) = correction_coefficients();
  // Digit offsets give acc = 16^64 H + sum((s_i + k) P_i).
  // Since sum = H + sum(P_i) and c = 16^64 - k, the correction
  // k*sum + c*H cancels every offset for any constrained subgroup H.
  let ks = constant_mul(b, f, sum, k);
  let correction = constant_mul(b, f, h, c);
  let correction = ks.add(b, f, correction);
  let neg = negate(b, f, correction);
  acc.add_complete(b, f, neg)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::recursive::native_field::fq_value;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::traits::Field as _;

  fn fr(n: i64) -> Fr {
    let value = Fr::from(n.unsigned_abs());
    if n < 0 { -value } else { value }
  }

  fn rejects_changed_gate(
    circuit: &multi_stark::plonkish::Circuit<Scalar>,
    assignment: &multi_stark::plonkish::Assignment<Scalar>,
    changed: Value,
    delta: Scalar,
  ) -> bool {
    circuit.gates().iter().any(|g| {
      let [a, b, c] = g.wires.map(|v| {
        assignment.value(v).unwrap()
          + if v == changed { delta } else { Scalar::ZERO }
      });
      let [qm, qa, qb, qc, k] = g.coefficients;
      qm * a * b + qa * a + qb * b + qc * c + k != Scalar::ZERO
    })
  }

  #[test]
  fn msm_matches_native_with_zero_identity_duplicate_and_negated_terms() {
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
    let result = result.canonical(&mut b, &f);
    let encoded =
      crate::recursive::native_transcript::point_bytes(&mut b, &bytes, result);
    let c = b.finish();
    for (ns, ss) in [
      ([2, 3, 7], [11, 0, 17]),
      ([0, 9, 11], [17, 91, 0]),
      ([2, 3, 7], [0, 0, 0]),
      ([0, 0, 0], [1, 7, 11]),
      ([2, 2, 2], [1, 0, -1]),
      ([2, -2, 7], [1, 1, 0]),
      ([2, 2, -2], [1, 1, 2]),
      ([-2, 2, -7], [-1, 2, 3]),
    ] {
      let mut w = c.witness();
      let mut expected = G1Projective::default();
      for i in 0..3 {
        let p = (G1Affine::generator() * fr(ns[i])).into_affine();
        let s = fr(ss[i]);
        expected += p * s;
        for (v, n) in points[i].inputs(p) {
          w.set(v, n).unwrap();
        }
        w.set(scalars[i], Scalar(s)).unwrap();
      }
      let a = w.generate().unwrap();
      let x = fq_value(&result.point.x.0.map(|v| a.value(v).unwrap()));
      let y = fq_value(&result.point.y.0.map(|v| a.value(v).unwrap()));
      let infinity = a.value(result.infinity.value()).unwrap() == Scalar::ONE;
      let actual = if infinity {
        assert!(x.is_zero() && y.is_zero());
        G1Affine::identity()
      } else {
        G1Affine::new_unchecked(x, y)
      };
      assert_eq!(actual, expected.into_affine());
      let mut expected_bytes = vec![];
      actual.serialize_compressed(&mut expected_bytes).unwrap();
      assert_eq!(
        encoded.map(|v| u8::try_from(
          a.value(v.value()).unwrap().0.into_bigint().as_ref()[0]
        )
        .unwrap()),
        expected_bytes.as_slice(),
      );
      assert!(rejects_changed_gate(
        &c,
        &a,
        result.infinity.value(),
        if infinity { Scalar::NEG_ONE } else { Scalar::ONE },
      ));
      assert!(rejects_changed_gate(&c, &a, result.point.x.0[0], Scalar::ONE));
    }
  }

  #[test]
  fn offset_retry_and_constraints_reject_a_deliberate_collision() {
    let p = (G1Affine::generator() * fr(2)).into_affine();
    let (good, attempts) = choose_offset(&[p], &[fr(0)], fr(-2)).unwrap();
    assert!(attempts > 1 && attempts <= 134);
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    let point = PointInput::new(&mut b, &f, "point");
    let offset = PointInput::new(&mut b, &f, "offset");
    let h = offset.nonzero(&mut b, &f);
    let mut bases = [Base::new(point, None)];
    let scalar = b.constant(Scalar::ZERO);
    let result =
      msm_with_offset(&mut b, &f, &bytes, &mut bases, &[(0, scalar)], h);
    let c = b.finish();
    let run = |h| {
      let mut w = c.witness();
      for (v, n) in point.inputs(p).into_iter().chain(offset.inputs(h)) {
        w.set(v, n).unwrap();
      }
      w.generate()
    };
    assert!(run(-p).is_err());
    let a = run(good).unwrap();
    assert_eq!(a.value(result.infinity.value()).unwrap(), Scalar::ONE);
    assert!(rejects_changed_gate(&c, &a, offset.point.x.0[0], Scalar::ONE));
    assert!(rejects_changed_gate(&c, &a, result.point.y.0[0], Scalar::ONE));
  }
}
