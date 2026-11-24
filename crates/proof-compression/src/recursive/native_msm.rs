use crate::kzg::{
  curve::{Bn254, G1AffineOf, G1ProjectiveOf, KzgCurve},
  field::CurveScalar,
};
use crate::recursive::{
  native_curve::{Affine, PointInput},
  native_field::{Builder, FqGadget, FqVar, fq_value, limb_count},
  native_transcript::scalar_bytes,
};
use ark_ec::{AdditiveGroup, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField, Zero};
use multi_stark::{
  plonkish::{Bool, Value, gadgets::ByteGadgets},
  traits::Algebra,
};

pub struct Base<C: KzgCurve = Bn254> {
  pub point: PointInput<C>,
  pub fixed: Option<G1AffineOf<C>>,
  table: Option<[Affine<C>; 16]>,
}
impl<C: KzgCurve> Base<C> {
  pub fn new(point: PointInput<C>, fixed: Option<G1AffineOf<C>>) -> Self {
    Self { point, fixed, table: None }
  }
  fn table(&mut self, b: &mut Builder<C>, f: &FqGadget<C>) -> [Affine<C>; 16] {
    if let Some(table) = self.table {
      return table;
    }
    let p = self.point.nonzero(b, f);
    let mut table = [p; 16];
    if let Some(point) = self.fixed {
      let point =
        if point.infinity { G1AffineOf::<C>::generator() } else { point };
      table = std::array::from_fn(|i| {
        Affine::constant(
          b,
          f,
          (point * C::Fr::from((i + 1) as u64)).into_affine(),
        )
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
fn select<C: KzgCurve>(
  b: &mut Builder<C>,
  table: &[Affine<C>; 16],
  bits: &[Bool],
) -> Affine<C> {
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
fn constant_mul<C: KzgCurve>(
  b: &mut Builder<C>,
  f: &FqGadget<C>,
  p: Affine<C>,
  n: C::Fr,
) -> Affine<C> {
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
pub fn negate<C: KzgCurve>(
  b: &mut Builder<C>,
  f: &FqGadget<C>,
  p: Affine<C>,
) -> Affine<C> {
  let y = f.hint_pure(b, "negative y", &[p.y], |v| Ok(-v[0]));
  f.relation(b, &[], &[(1, p.y), (1, y)], 0);
  Affine { x: p.x, y }
}

fn correction_coefficients<C: KzgCurve>() -> (C::Fr, C::Fr) {
  let mut k = C::Fr::from(0u8);
  let mut power = C::Fr::from(1u8);
  for _ in 0..64 {
    k += power;
    power *= C::Fr::from(16u8);
  }
  let c = power - k;
  assert!(!k.is_zero() && !c.is_zero() && k != c && !power.is_zero());
  (k, c)
}

fn add_without_exception<C: KzgCurve>(
  lhs: &mut G1ProjectiveOf<C>,
  rhs: &G1ProjectiveOf<C>,
) -> bool {
  if lhs.is_zero()
    || rhs.is_zero()
    || lhs.x * rhs.z.square() == rhs.x * lhs.z.square()
  {
    return false;
  }
  *lhs += rhs;
  true
}

fn offset_is_safe<C: KzgCurve>(
  h: G1ProjectiveOf<C>,
  tables: &[[G1ProjectiveOf<C>; 16]],
  digits: &[[usize; 64]],
) -> bool {
  if h.is_zero() {
    return false;
  }
  let mut sum = h;
  for table in tables {
    if !add_without_exception::<C>(&mut sum, &table[0]) {
      return false;
    }
  }
  let mut acc = h;
  for window in (0..64).rev() {
    for _ in 0..4 {
      acc.double_in_place();
    }
    for (table, digit) in tables.iter().zip(digits) {
      if !add_without_exception::<C>(&mut acc, &table[digit[window]]) {
        return false;
      }
    }
  }
  let (k, c) = correction_coefficients::<C>();
  let mut correction = sum * k;
  add_without_exception::<C>(&mut correction, &(h * c))
}

fn choose_offset<C: KzgCurve>(
  points: &[G1AffineOf<C>],
  scalars: &[C::Fr],
  first: C::Fr,
) -> Result<(G1AffineOf<C>, usize), String> {
  let tables: Vec<_> = points
    .iter()
    .map(|p| {
      let p = G1ProjectiveOf::<C>::from(*p);
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
  let generator = G1AffineOf::<C>::generator();
  let mut h = generator * first;
  for attempt in 1..=attempts {
    if offset_is_safe::<C>(h, &tables, &digits) {
      return Ok((h.into_affine(), attempt));
    }
    h += generator;
  }
  Err("no valid affine MSM offset".into())
}

fn witness_offset<C: KzgCurve>(
  b: &mut Builder<C>,
  f: &FqGadget<C>,
  bases: &[Base<C>],
  terms: &[(usize, Value)],
  tag: &str,
) -> Affine<C> {
  let l = limb_count::<C>();
  let mut wide = [0; 64];
  blake3::Hasher::new()
    .update(b"kzg-wrap/msm-offset/v1")
    .update(tag.as_bytes())
    .finalize_xof()
    .fill(&mut wide);
  let first = C::Fr::from_le_bytes_mod_order(&wide);
  let deps: Vec<_> = terms
    .iter()
    .flat_map(|&(id, scalar)| {
      let point = bases[id].point;
      point
        .point
        .x
        .limbs()
        .iter()
        .copied()
        .chain(point.point.y.limbs().iter().copied())
        .chain([point.infinity.value(), scalar])
        .collect::<Vec<_>>()
    })
    .collect();
  let compute =
    move |v: &[CurveScalar<C>]| -> Result<Vec<CurveScalar<C>>, String> {
      let stride = 2 * l + 2;
      let mut points = Vec::with_capacity(v.len() / stride);
      let mut scalars = Vec::with_capacity(v.len() / stride);
      for values in v.chunks_exact(stride) {
        let infinity = values[2 * l] == CurveScalar::<C>::ONE;
        if values[2 * l] != CurveScalar::<C>::ZERO && !infinity {
          return Err("invalid point infinity flag".into());
        }
        let point = if infinity {
          G1AffineOf::<C>::generator()
        } else {
          G1AffineOf::<C>::new_unchecked(
            fq_value::<C>(&values[..l]),
            fq_value::<C>(&values[l..2 * l]),
          )
        };
        if !point.is_on_curve()
          || !point.is_in_correct_subgroup_assuming_on_curve()
        {
          return Err("invalid MSM point".into());
        }
        points.push(point);
        scalars.push(if infinity {
          C::Fr::from(0u8)
        } else {
          values[2 * l + 1].0
        });
      }
      let (offset, _) = choose_offset::<C>(&points, &scalars, first)?;
      let mut out = FqGadget::<C>::witness_values(offset.x);
      out.extend(FqGadget::<C>::witness_values(offset.y));
      Ok(out)
    };
  let limbs: Vec<Value> = match l {
    4 => b
      .hint_many::<8>("nonexceptional MSM offset", &deps, move |v| {
        let out = compute(v)?;
        Ok(std::array::from_fn(|i| out[i]))
      })
      .to_vec(),
    5 => b
      .hint_many::<10>("nonexceptional MSM offset", &deps, move |v| {
        let out = compute(v)?;
        Ok(std::array::from_fn(|i| out[i]))
      })
      .to_vec(),
    other => panic!("unsupported Fq limb count {other}"),
  };
  let h = Affine {
    x: FqVar::from_slice(&limbs[..l]),
    y: FqVar::from_slice(&limbs[l..]),
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
pub fn msm<C: KzgCurve>(
  b: &mut Builder<C>,
  f: &FqGadget<C>,
  bytes: &ByteGadgets,
  bases: &mut [Base<C>],
  terms: &[(usize, Value)],
  tag: &str,
) -> PointInput<C> {
  assert!(!terms.is_empty());
  let offset = witness_offset(b, f, bases, terms, tag);
  msm_with_offset(b, f, bytes, bases, terms, offset)
}

fn msm_with_offset<C: KzgCurve>(
  b: &mut Builder<C>,
  f: &FqGadget<C>,
  bytes: &ByteGadgets,
  bases: &mut [Base<C>],
  terms: &[(usize, Value)],
  h: Affine<C>,
) -> PointInput<C> {
  let mut sum = h;
  let mut tables = Vec::new();
  let mut digits = Vec::new();
  for &(id, scalar) in terms {
    let base = &mut bases[id];
    let zero = b.constant(CurveScalar::<C>::ZERO);
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
  let (k, c) = correction_coefficients::<C>();
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
  use crate::kzg::curve::Bls12381;
  use crate::recursive::native_field::fq_value;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::traits::Field as _;

  fn fr<C: KzgCurve>(n: i64) -> C::Fr {
    let value = C::Fr::from(n.unsigned_abs());
    if n < 0 { -value } else { value }
  }

  fn rejects_changed_gate<C: KzgCurve>(
    circuit: &multi_stark::plonkish::Circuit<CurveScalar<C>>,
    assignment: &multi_stark::plonkish::Assignment<CurveScalar<C>>,
    changed: Value,
    delta: CurveScalar<C>,
  ) -> bool {
    circuit.gates().iter().any(|g| {
      let [a, b, c] = g.wires.map(|v| {
        assignment.value(v).unwrap()
          + if v == changed { delta } else { CurveScalar::<C>::ZERO }
      });
      let [qm, qa, qb, qc, k] = g.coefficients;
      qm * a * b + qa * a + qb * b + qc * c + k != CurveScalar::<C>::ZERO
    })
  }

  fn test_msm<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    let points: Vec<_> = (0..3)
      .map(|i| PointInput::<C>::new(&mut b, &f, &format!("p{i}")))
      .collect();
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
    let mut cases: Vec<_> = [
      ([2, 3, 7], [11, 0, 17]),
      ([0, 9, 11], [17, 91, 0]),
      ([2, 3, 7], [0, 0, 0]),
      ([0, 0, 0], [1, 7, 11]),
      ([2, 2, 2], [1, 0, -1]),
      ([2, -2, 7], [1, 1, 0]),
      ([2, 2, -2], [1, 1, 2]),
      ([-2, 2, -7], [-1, 2, 3]),
    ]
    .into_iter()
    .map(|(ns, ss)| (ns.map(fr::<C>), ss.map(fr::<C>)))
    .collect();
    cases.push((
      [fr::<C>(2), fr::<C>(3), fr::<C>(7)],
      [
        C::Fr::from(2u8).pow([u64::from(C::Fr::MODULUS_BIT_SIZE - 1)]),
        -C::Fr::ONE,
        C::Fr::ONE,
      ],
    ));
    for (ns, ss) in cases {
      let mut w = c.witness();
      let mut expected = G1ProjectiveOf::<C>::default();
      for i in 0..3 {
        let p = (G1AffineOf::<C>::generator() * ns[i]).into_affine();
        let s = ss[i];
        expected += p * s;
        for (v, n) in points[i].inputs(p) {
          w.set(v, n).unwrap();
        }
        w.set(scalars[i], CurveScalar::<C>(s)).unwrap();
      }
      let a = w.generate().unwrap();
      let xs: Vec<_> =
        result.point.x.limbs().iter().map(|&v| a.value(v).unwrap()).collect();
      let ys: Vec<_> =
        result.point.y.limbs().iter().map(|&v| a.value(v).unwrap()).collect();
      let x = fq_value::<C>(&xs);
      let y = fq_value::<C>(&ys);
      let infinity =
        a.value(result.infinity.value()).unwrap() == CurveScalar::<C>::ONE;
      let actual = if infinity {
        assert!(x.is_zero() && y.is_zero());
        G1AffineOf::<C>::identity()
      } else {
        G1AffineOf::<C>::new_unchecked(x, y)
      };
      assert_eq!(actual, expected.into_affine());
      let mut expected_bytes = vec![];
      actual.serialize_compressed(&mut expected_bytes).unwrap();
      let actual_bytes: Vec<u8> = encoded
        .iter()
        .map(|v| {
          u8::try_from(a.value(v.value()).unwrap().0.into_bigint().as_ref()[0])
            .unwrap()
        })
        .collect();
      assert_eq!(actual_bytes, expected_bytes);
      assert!(rejects_changed_gate(
        &c,
        &a,
        result.infinity.value(),
        if infinity {
          CurveScalar::<C>::NEG_ONE
        } else {
          CurveScalar::<C>::ONE
        },
      ));
      assert!(rejects_changed_gate(
        &c,
        &a,
        result.point.x.limbs()[0],
        CurveScalar::<C>::ONE,
      ));
    }
  }

  #[test]
  fn msm_matches_native_with_zero_identity_duplicate_and_negated_terms() {
    test_msm::<Bn254>();
    test_msm::<Bls12381>();
  }

  fn test_offset_retry<C: KzgCurve>() {
    let p = (G1AffineOf::<C>::generator() * fr::<C>(2)).into_affine();
    let (good, attempts) =
      choose_offset::<C>(&[p], &[fr::<C>(0)], fr::<C>(-2)).unwrap();
    assert!(attempts > 1 && attempts <= 134);
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let bytes = ByteGadgets::new(&mut b);
    let point = PointInput::<C>::new(&mut b, &f, "point");
    let offset = PointInput::<C>::new(&mut b, &f, "offset");
    let h = offset.nonzero(&mut b, &f);
    let mut bases = [Base::new(point, None)];
    let scalar = b.constant(CurveScalar::<C>::ZERO);
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
    assert_eq!(
      a.value(result.infinity.value()).unwrap(),
      CurveScalar::<C>::ONE
    );
    assert!(rejects_changed_gate(
      &c,
      &a,
      offset.point.x.limbs()[0],
      CurveScalar::<C>::ONE,
    ));
    assert!(rejects_changed_gate(
      &c,
      &a,
      result.point.y.limbs()[0],
      CurveScalar::<C>::ONE,
    ));
  }

  #[test]
  fn offset_retry_and_constraints_reject_a_deliberate_collision() {
    test_offset_retry::<Bn254>();
    test_offset_retry::<Bls12381>();
  }
}
