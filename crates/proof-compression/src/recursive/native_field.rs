//! Bounded Fq arithmetic in a native Fr Plonkish circuit.
use crate::kzg::{
  curve::{Bls12381, Bn254, KzgCurve},
  field::CurveScalar,
};
use ark_ff::{BigInteger, PrimeField};
use multi_stark::{
  plonkish::{CircuitBuilder, Table, Value},
  traits::{Algebra, Field},
};
use num_bigint::{BigInt, BigUint, Sign};
use std::{collections::BTreeMap, marker::PhantomData};

pub type Builder<C = Bn254> = CircuitBuilder<CurveScalar<C>>;
pub(super) const W: usize = 80;
/// Width of the range-check lookup limbs; the table has `2^RANGE_BITS` rows.
pub(super) const RANGE_BITS: usize = 20;
pub(super) const MAX_L: usize = 5;
const CARRY_BITS: usize = 89;
const CARRY_BIAS_BITS: usize = CARRY_BITS - 1;

const _: () = {
  const BN_BITS: usize =
    <ark_bn254::Fq as PrimeField>::MODULUS_BIT_SIZE as usize;
  const BN_L: usize = BN_BITS.div_ceil(W);
  assert!(BN_L == Bn254::FQ_GADGET_LIMBS);
  assert!(BN_L <= MAX_L);
  assert!(BN_BITS - W * (BN_L - 1) <= W);
  assert!(BN_BITS + 3 - W * (BN_L - 1) <= W);

  const BLS_BITS: usize =
    <ark_bls12_381::Fq as PrimeField>::MODULUS_BIT_SIZE as usize;
  const BLS_L: usize = BLS_BITS.div_ceil(W);
  assert!(BLS_L == Bls12381::FQ_GADGET_LIMBS);
  assert!(BLS_L <= MAX_L);
  assert!(BLS_BITS - W * (BLS_L - 1) <= W);
  assert!(BLS_BITS + 3 - W * (BLS_L - 1) <= W);
};

#[inline]
pub(super) const fn field_bits<C: KzgCurve>() -> usize {
  C::Fq::MODULUS_BIT_SIZE as usize
}

#[inline]
pub(super) const fn limb_count<C: KzgCurve>() -> usize {
  C::FQ_GADGET_LIMBS
}

#[inline]
const fn top_limb_bits<C: KzgCurve>() -> usize {
  field_bits::<C>() - W * (limb_count::<C>() - 1)
}

#[inline]
pub(super) const fn quotient_bits<C: KzgCurve>() -> usize {
  field_bits::<C>() + 3
}

#[inline]
pub(super) const fn quotient_bias_bits<C: KzgCurve>() -> usize {
  quotient_bits::<C>() - 1
}

#[inline]
const fn quotient_top_bits<C: KzgCurve>() -> usize {
  quotient_bits::<C>() - W * (limb_count::<C>() - 1)
}

#[inline]
pub(super) const fn relation_advice_len<C: KzgCurve>() -> usize {
  2 * limb_count::<C>() - 1
}

mod advice;

#[derive(Debug)]
pub struct FqVar<C: KzgCurve = Bn254> {
  limbs: [Value; MAX_L],
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Clone for FqVar<C> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<C: KzgCurve> Copy for FqVar<C> {}

impl<C: KzgCurve> FqVar<C> {
  pub fn from_slice(slice: &[Value]) -> Self {
    assert_eq!(slice.len(), limb_count::<C>());
    let mut limbs = [slice[0]; MAX_L];
    limbs[..slice.len()].copy_from_slice(slice);
    Self { limbs, _curve: PhantomData }
  }

  pub fn from_fn(mut f: impl FnMut(usize) -> Value) -> Self {
    let first = f(0);
    let mut limbs = [first; MAX_L];
    for (i, limb) in limbs[..limb_count::<C>()].iter_mut().enumerate().skip(1) {
      *limb = f(i);
    }
    Self { limbs, _curve: PhantomData }
  }

  #[inline]
  pub fn limbs(&self) -> &[Value] {
    &self.limbs[..limb_count::<C>()]
  }
}

pub struct FqGadget<C: KzgCurve = Bn254> {
  range: Table,
  _curve: PhantomData<C>,
}

pub fn integer<C: KzgCurve>(v: CurveScalar<C>) -> BigUint {
  let mut bytes = [0; 32];
  for (output, word) in
    bytes.as_chunks_mut::<8>().0.iter_mut().zip(v.canonical_limbs_le())
  {
    *output = word.to_le_bytes();
  }
  BigUint::from_bytes_le(&bytes)
}
pub fn scalar<C: KzgCurve>(v: &BigUint) -> CurveScalar<C> {
  let digits = v.to_u64_digits();
  let mut limbs = [0; 4];
  assert!(digits.len() <= 4);
  limbs[..digits.len()].copy_from_slice(&digits);
  CurveScalar::<C>::from_limbs_le(limbs)
}
fn signed<C: KzgCurve>(v: &BigInt) -> CurveScalar<C> {
  let (sign, n) = v.clone().into_parts();
  let f = scalar::<C>(&n);
  if sign == Sign::Minus { -f } else { f }
}
pub fn modulus<C: KzgCurve>() -> BigUint {
  BigUint::from_bytes_le(&C::Fq::MODULUS.to_bytes_le())
}
fn digits<C: KzgCurve>(v: &BigUint) -> Vec<BigUint> {
  let mask = (BigUint::from(1u8) << W) - 1u8;
  (0..limb_count::<C>()).map(|i| (v >> (W * i)) & &mask).collect()
}
pub fn fq_value<C: KzgCurve>(values: &[CurveScalar<C>]) -> C::Fq {
  let n = values
    .iter()
    .rev()
    .fold(BigUint::from(0u8), |acc, &v| (acc << W) + integer(v));
  C::Fq::from_le_bytes_mod_order(&n.to_bytes_le())
}

impl<C: KzgCurve> FqGadget<C> {
  pub fn new(b: &mut Builder<C>) -> Self {
    Self {
      range: b.fixed_table(
        "Fq range",
        (0..1u64 << RANGE_BITS)
          .map(|v| vec![CurveScalar::<C>::from_u64(v)])
          .collect(),
      ),
      _curve: PhantomData,
    }
  }
  pub fn range(&self, b: &mut Builder<C>, value: Value, bits: usize) {
    match bits.div_ceil(RANGE_BITS) {
      1 => self.range_n::<1>(b, value, bits),
      2 => self.range_n::<2>(b, value, bits),
      3 => self.range_n::<3>(b, value, bits),
      4 => self.range_n::<4>(b, value, bits),
      5 => self.range_n::<5>(b, value, bits),
      6 => self.range_n::<6>(b, value, bits),
      _ => panic!("unsupported range width"),
    }
  }
  fn range_n<const N: usize>(
    &self,
    b: &mut Builder<C>,
    value: Value,
    bits: usize,
  ) {
    assert!(bits > 0 && bits <= N * RANGE_BITS);
    let limbs = b.hint_many_pure::<N>("bounded integer", &[value], move |v| {
      Ok(advice::range_limbs(v[0]))
    });
    for &limb in &limbs {
      b.lookup(self.range, &[limb]);
    }
    if !bits.is_multiple_of(RANGE_BITS) {
      let top = b.scale(
        limbs[N - 1],
        CurveScalar::<C>::from_u64(1 << (RANGE_BITS - bits % RANGE_BITS)),
      );
      b.lookup(self.range, &[top]);
    }
    let terms: Vec<_> = limbs
      .iter()
      .enumerate()
      .map(|(i, &v)| {
        (scalar::<C>(&(BigUint::from(1u8) << (RANGE_BITS * i))), v)
      })
      .collect();
    let packed = b.linear_combination(&terms, CurveScalar::<C>::ZERO);
    b.assert_equal(packed, value);
  }
  pub fn constant(&self, b: &mut Builder<C>, value: C::Fq) -> FqVar<C> {
    let ds =
      digits::<C>(&BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()));
    FqVar::from_fn(|i| b.constant(scalar::<C>(&ds[i])))
  }
  pub fn input(&self, b: &mut Builder<C>, name: &str) -> FqVar<C> {
    let result = FqVar::from_fn(|i| b.input(format!("{name}.{i}")));
    self.bound(b, result);
    self.canonical(b, result);
    result
  }
  pub fn witness_values(value: C::Fq) -> Vec<CurveScalar<C>> {
    digits::<C>(&BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()))
      .into_iter()
      .map(|n| scalar::<C>(&n))
      .collect()
  }
  /// The callback's values and errors must depend only on its arguments and
  /// immutable captures, with no observable effects from execution order.
  /// Invalid arguments must return an error rather than panic. Independent
  /// callbacks may execute even when an earlier point block fails.
  pub fn hint_pure(
    &self,
    b: &mut Builder<C>,
    name: &str,
    inputs: &[FqVar<C>],
    f: impl Fn(&[C::Fq]) -> Result<C::Fq, String> + Send + Sync + 'static,
  ) -> FqVar<C> {
    let deps: Vec<_> =
      inputs.iter().flat_map(|v| v.limbs().iter().copied()).collect();
    let result = match limb_count::<C>() {
      4 => {
        let out = b.hint_many_pure::<4>(name, &deps, move |v| {
          let args: Vec<_> =
            v.as_chunks::<4>().0.iter().map(|c| fq_value::<C>(c)).collect();
          let vals = Self::witness_values(f(&args)?);
          Ok(std::array::from_fn(|i| vals[i]))
        });
        FqVar::from_slice(&out)
      },
      5 => {
        let out = b.hint_many_pure::<5>(name, &deps, move |v| {
          let args: Vec<_> =
            v.as_chunks::<5>().0.iter().map(|c| fq_value::<C>(c)).collect();
          let vals = Self::witness_values(f(&args)?);
          Ok(std::array::from_fn(|i| vals[i]))
        });
        FqVar::from_slice(&out)
      },
      other => panic!("unsupported Fq limb count {other}"),
    };
    self.bound(b, result);
    result
  }
  pub fn bound(&self, b: &mut Builder<C>, v: FqVar<C>) {
    let l = limb_count::<C>();
    for (i, &limb) in v.limbs().iter().enumerate() {
      self.range(b, limb, if i == l - 1 { top_limb_bits::<C>() } else { W });
    }
  }
  pub fn canonical(&self, b: &mut Builder<C>, v: FqVar<C>) {
    let l = limb_count::<C>();
    let p = digits::<C>(&(modulus::<C>() - 1u8));
    let p_hint = p.clone();
    let compute = move |values: &[CurveScalar<C>]| -> Vec<CurveScalar<C>> {
      let mut borrow = BigInt::from(0u8);
      let radix = BigInt::from(1u8) << W;
      let mut out = vec![CurveScalar::<C>::ZERO; 2 * l];
      for i in 0..l {
        let mut d = BigInt::from(p_hint[i].clone())
          - BigInt::from(integer(values[i]))
          - &borrow;
        borrow = BigInt::from(u8::from(d.sign() == Sign::Minus));
        if d.sign() == Sign::Minus {
          d += &radix;
        }
        out[i] = signed::<C>(&d);
        out[l + i] = signed::<C>(&borrow);
      }
      out
    };
    let advice: Vec<Value> = match l {
      4 => b
        .hint_many_pure::<8>(
          "Fq canonical subtraction",
          v.limbs(),
          move |vals| {
            let out = compute(vals);
            Ok(std::array::from_fn(|i| out[i]))
          },
        )
        .to_vec(),
      5 => b
        .hint_many_pure::<10>(
          "Fq canonical subtraction",
          v.limbs(),
          move |vals| {
            let out = compute(vals);
            Ok(std::array::from_fn(|i| out[i]))
          },
        )
        .to_vec(),
      other => panic!("unsupported Fq limb count {other}"),
    };
    let radix = scalar::<C>(&(BigUint::from(1u8) << W));
    let mut borrow = b.constant(CurveScalar::<C>::ZERO);
    let v_limbs = v.limbs();
    for i in 0..l {
      self.range(b, advice[i], W);
      b.assert_bool(advice[l + i]);
      let eq = b.linear_combination(
        &[
          (CurveScalar::<C>::NEG_ONE, v_limbs[i]),
          (CurveScalar::<C>::NEG_ONE, borrow),
          (radix, advice[l + i]),
          (CurveScalar::<C>::NEG_ONE, advice[i]),
        ],
        scalar::<C>(&p[i]),
      );
      b.assert_zero(eq);
      borrow = advice[l + i];
    }
    b.assert_zero(borrow);
  }
  /// Sum of bounded quadratic and linear terms is zero modulo Fq.
  /// Each sign has total product and linear weight at most three. For
  /// n-bit representatives, |quotient| < 2^(n+2) for either supported Fq;
  /// biasing by 2^(n+2) therefore requires n+3 bits. Carries are biased by
  /// 2^88 and range-checked to 89 bits. With B=2^80, each polynomial
  /// coefficient has magnitude below A=4*L*B^2+3*B+4. Pairing coefficients
  /// bounds an integer equality by (B+1)*A+(B^2+1)*2^88 < Fr, so a zero
  /// field equation is also an integer equality. The integer-bound test
  /// checks these inequalities against both BN254's and BLS12-381's exact moduli.
  pub fn relation(
    &self,
    b: &mut Builder<C>,
    products: &[(i8, FqVar<C>, FqVar<C>)],
    linear: &[(i8, FqVar<C>)],
    constant: i8,
  ) {
    let l = limb_count::<C>();
    for sign in [-1i8, 1] {
      assert!(
        products
          .iter()
          .filter(|(c, _, _)| c.signum() == sign)
          .map(|(c, _, _)| usize::from(c.unsigned_abs()))
          .sum::<usize>()
          <= 3
      );
      assert!(
        linear
          .iter()
          .filter(|(c, _)| c.signum() == sign)
          .map(|(c, _)| usize::from(c.unsigned_abs()))
          .sum::<usize>()
          <= 3
      );
    }
    assert!(constant.unsigned_abs() <= 4);
    let deps: Vec<_> = products
      .iter()
      .flat_map(|(_, a, c)| a.limbs().iter().chain(c.limbs()).copied())
      .chain(linear.iter().flat_map(|(_, a)| a.limbs().iter().copied()))
      .collect();
    let pc: Vec<_> = products.iter().map(|(c, _, _)| *c).collect();
    let lc: Vec<_> = linear.iter().map(|(c, _)| *c).collect();
    let p = &advice::constants::<C>().modulus_digits;
    let advice: Vec<Value> = match relation_advice_len::<C>() {
      7 => b
        .hint_many_pure::<7>("Fq quotient and carries", &deps, move |values| {
          advice::relation_array::<C, 7>(values, &pc, &lc, constant)
        })
        .to_vec(),
      9 => b
        .hint_many_pure::<9>("Fq quotient and carries", &deps, move |values| {
          advice::relation_array::<C, 9>(values, &pc, &lc, constant)
        })
        .to_vec(),
      other => panic!("unsupported Fq relation advice length {other}"),
    };
    for (i, &v) in advice[..l].iter().enumerate() {
      self.range(b, v, if i == l - 1 { quotient_top_bits::<C>() } else { W });
    }
    for &v in &advice[l..] {
      self.range(b, v, CARRY_BITS);
    }
    let mut terms: Vec<Vec<(CurveScalar<C>, Value)>> = vec![vec![]; 2 * l];
    let mut cached = BTreeMap::new();
    for &(c, a, d) in products {
      let a_limbs = a.limbs();
      let d_limbs = d.limbs();
      for i in 0..l {
        for j in 0..l {
          let key = (
            a_limbs[i].index().min(d_limbs[j].index()),
            a_limbs[i].index().max(d_limbs[j].index()),
          );
          let v =
            *cached.entry(key).or_insert_with(|| b.mul(a_limbs[i], d_limbs[j]));
          terms[i + j].push((signed::<C>(&BigInt::from(c)), v));
        }
      }
    }
    for &(c, a) in linear {
      for (terms, &v) in terms.iter_mut().zip(a.limbs()) {
        terms.push((signed::<C>(&BigInt::from(c)), v));
      }
    }
    let bias = digits::<C>(&(BigUint::from(1u8) << quotient_bias_bits::<C>()));
    let mut constants = vec![BigInt::from(0u8); 2 * l];
    constants[0] += constant;
    for i in 0..l {
      for j in 0..l {
        terms[i + j].push((-scalar::<C>(&p[i]), advice[j]));
        constants[i + j] += BigInt::from(&p[i] * &bias[j]);
      }
    }
    let radix = scalar::<C>(&(BigUint::from(1u8) << W));
    let block = radix * radix;
    let carry_bias = scalar::<C>(&(BigUint::from(1u8) << CARRY_BIAS_BITS));
    for j in 0..l {
      let mut equation = terms[2 * j].clone();
      equation.extend(terms[2 * j + 1].iter().map(|&(c, v)| (c * radix, v)));
      let mut constant = signed::<C>(&constants[2 * j])
        + radix * signed::<C>(&constants[2 * j + 1]);
      if j > 0 {
        equation.push((CurveScalar::<C>::ONE, advice[l + j - 1]));
        constant -= carry_bias;
      }
      if j < l - 1 {
        equation.push((-block, advice[l + j]));
        constant += block * carry_bias;
      }
      let value = b.linear_combination(&equation, constant);
      b.assert_zero(value);
    }
  }
  pub fn mul(&self, b: &mut Builder<C>, x: FqVar<C>, y: FqVar<C>) -> FqVar<C> {
    let result = self.hint_pure(b, "Fq product", &[x, y], |v| Ok(v[0] * v[1]));
    self.relation(b, &[(1, x, y)], &[(-1, result)], 0);
    result
  }
  pub fn equal(&self, b: &mut Builder<C>, x: FqVar<C>, y: FqVar<C>) {
    self.relation(b, &[], &[(1, x), (-1, y)], 0);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::plonkish::{Assignment, Circuit};
  use std::collections::{HashMap, HashSet};

  pub(super) fn check_mutations<C: KzgCurve>(
    c: &Circuit<CurveScalar<C>>,
    a: &Assignment<CurveScalar<C>>,
  ) {
    let handles: HashMap<_, _> = c
      .gates()
      .iter()
      .flat_map(|g| g.wires)
      .chain(c.lookups().iter().flat_map(|l| l.values.iter().copied()))
      .map(|v| (v.index(), v))
      .collect();
    let tables: Vec<HashSet<_>> =
      c.tables().iter().map(|t| t.rows().iter().cloned().collect()).collect();
    let satisfied = |changed: Option<usize>| {
      let value = |v: Value| {
        a.value(v).unwrap()
          + if changed == Some(v.index()) {
            CurveScalar::<C>::ONE
          } else {
            CurveScalar::<C>::ZERO
          }
      };
      c.gates().iter().all(|g| {
        let [a, b, c] = g.wires.map(value);
        let [qm, qa, qb, qc, k] = g.coefficients;
        qm * a * b + qa * a + qb * b + qc * c + k == CurveScalar::<C>::ZERO
      }) && c.lookups().iter().all(|l| {
        tables[l.table.index()]
          .contains(&l.values.iter().copied().map(value).collect::<Vec<_>>())
      })
    };
    assert!(satisfied(None));
    for &index in handles.keys() {
      assert!(!satisfied(Some(index)), "unconstrained value {index}");
    }
  }

  fn test_products_and_adversarial_assignments<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let x = f.input(&mut b, "x");
    let y = f.input(&mut b, "y");
    let out = f.mul(&mut b, x, y);
    let c = b.finish();
    let cases = [
      (C::Fq::from(0u8), C::Fq::from(1u8)),
      (-C::Fq::from(1u8), -C::Fq::from(1u8)),
      (C::Fq::from(42u8), C::Fq::from(999u64)),
    ];
    for (xv, yv) in cases {
      let mut w = c.witness();
      for (&v, n) in x
        .limbs()
        .iter()
        .zip(FqGadget::<C>::witness_values(xv))
        .chain(y.limbs().iter().zip(FqGadget::<C>::witness_values(yv)))
      {
        w.set(v, n).unwrap();
      }
      let a = w.generate().unwrap();
      let vals: Vec<_> =
        out.limbs().iter().map(|&v| a.value(v).unwrap()).collect();
      assert_eq!(fq_value::<C>(&vals), xv * yv);
      check_mutations::<C>(&c, &a);
    }
  }

  #[test]
  fn products_and_adversarial_assignments() {
    test_products_and_adversarial_assignments::<Bn254>();
    test_products_and_adversarial_assignments::<Bls12381>();
  }

  fn test_rejects_noncanonical_and_out_of_range<C: KzgCurve>() {
    let l = limb_count::<C>();
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let x = f.input(&mut b, "x");
    let c = b.finish();
    for n in [
      modulus::<C>(),
      modulus::<C>() + 1u8,
      (BigUint::from(1u8) << field_bits::<C>()) - 1u8,
    ] {
      let mut w = c.witness();
      for (&v, n) in x.limbs().iter().zip(digits::<C>(&n)) {
        w.set(v, scalar::<C>(&n)).unwrap();
      }
      assert!(w.generate().is_err());
    }
    for i in 0..l {
      let mut w = c.witness();
      for (j, &v) in x.limbs().iter().enumerate() {
        w.set(
          v,
          if i == j {
            scalar::<C>(
              &(BigUint::from(1u8)
                << if i == l - 1 { top_limb_bits::<C>() } else { W }),
            )
          } else {
            CurveScalar::<C>::ZERO
          },
        )
        .unwrap();
      }
      assert!(w.generate().is_err());
    }
  }

  #[test]
  fn rejects_noncanonical_and_out_of_range() {
    test_rejects_noncanonical_and_out_of_range::<Bn254>();
    test_rejects_noncanonical_and_out_of_range::<Bls12381>();
  }

  fn test_bounded_relations_accept_redundant_representatives<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let x = FqVar::<C>::from_fn(|i| b.input(format!("x{i}")));
    f.bound(&mut b, x);
    let z = f.constant(&mut b, C::Fq::from(0u8));
    f.equal(&mut b, x, z);
    // Exercise the maximum permitted quadratic weight and negative quotient.
    f.relation(&mut b, &[(-3, x, x)], &[(3, x)], 0);
    let c = b.finish();
    let mut w = c.witness();
    for (&v, n) in x.limbs().iter().zip(digits::<C>(&modulus::<C>())) {
      w.set(v, scalar::<C>(&n)).unwrap();
    }
    check_mutations::<C>(&c, &w.generate().unwrap());
  }

  #[test]
  fn bounded_relations_accept_redundant_representatives() {
    test_bounded_relations_accept_redundant_representatives::<Bn254>();
    test_bounded_relations_accept_redundant_representatives::<Bls12381>();
  }

  fn test_maximal_representatives_support_both_quotient_signs<C: KzgCurve>() {
    let max = (BigUint::from(1u8) << field_bits::<C>()) - 1u8;
    let total = 3u8 * &max * &max + 3u8 * &max + 4u8;
    let residue =
      C::Fq::from_le_bytes_mod_order(&(&total % modulus::<C>()).to_bytes_le());
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let x = FqVar::<C>::from_fn(|i| b.input(format!("x{i}")));
    f.bound(&mut b, x);
    let residue = f.constant(&mut b, residue);
    f.relation(&mut b, &[(3, x, x)], &[(3, x), (-1, residue)], 4);
    f.relation(&mut b, &[(-3, x, x)], &[(-3, x), (1, residue)], -4);
    let c = b.finish();
    let mut w = c.witness();
    for (&v, n) in x.limbs().iter().zip(digits::<C>(&max)) {
      w.set(v, scalar::<C>(&n)).unwrap();
    }
    check_mutations::<C>(&c, &w.generate().unwrap());
  }

  #[test]
  fn maximal_representatives_support_both_quotient_signs() {
    test_maximal_representatives_support_both_quotient_signs::<Bn254>();
    test_maximal_representatives_support_both_quotient_signs::<Bls12381>();
  }

  fn test_range_checks_reject_boundary_overflow_and_negative_integers<
    C: KzgCurve,
  >() {
    for bits in [top_limb_bits::<C>(), quotient_top_bits::<C>(), W, CARRY_BITS]
    {
      let mut b = Builder::<C>::new();
      let f = FqGadget::<C>::new(&mut b);
      let x = b.input("x");
      f.range(&mut b, x, bits);
      let c = b.finish();
      let limit = BigUint::from(1u8) << bits;
      for (value, accepted) in [
        (scalar::<C>(&(&limit - 1u8)), true),
        (scalar::<C>(&limit), false),
        (CurveScalar::<C>::NEG_ONE, false),
      ] {
        let mut w = c.witness();
        w.set(x, value).unwrap();
        assert_eq!(w.generate().is_ok(), accepted, "range width {bits}");
      }
    }
  }

  #[test]
  fn range_checks_reject_boundary_overflow_and_negative_integers() {
    test_range_checks_reject_boundary_overflow_and_negative_integers::<Bn254>();
    test_range_checks_reject_boundary_overflow_and_negative_integers::<Bls12381>(
    );
  }

  fn test_integer_bounds_do_not_wrap_fr<C: KzgCurve>() {
    let l = limb_count::<C>();
    let one = BigUint::from(1u8);
    let radix = &one << W;
    let max = (&one << field_bits::<C>()) - 1u8;
    let max_expression = 3u8 * &max * &max + 3u8 * &max + 4u8;
    assert!(
      max_expression / modulus::<C>() < (&one << quotient_bias_bits::<C>())
    );
    // Each coefficient has at most 3*L product terms of either sign,
    // L modulus times unbiased-quotient terms, and three linear terms.
    let coefficient_bound = (4 * l) * &radix * &radix + 3u8 * &radix + 4u8;
    let carry_bound = &one << CARRY_BIAS_BITS;
    let equation_bound: BigUint = (&radix + 1u8) * &coefficient_bound
      + (&radix * &radix + 1u8) * &carry_bound;
    let fr = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le());
    assert!(equation_bound < fr);
    assert!(
      ((&radix + 1u8) * coefficient_bound + &carry_bound) / (&radix * &radix)
        < carry_bound
    );
  }

  #[test]
  fn integer_bounds_do_not_wrap_fr() {
    test_integer_bounds_do_not_wrap_fr::<Bn254>();
    test_integer_bounds_do_not_wrap_fr::<Bls12381>();
  }
}
