//! Bounded Fq arithmetic in a native Fr Plonkish circuit.
use crate::kzg::Scalar;
use ark_bls12_381::Fq;
use ark_ff::{BigInteger, PrimeField};
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Table;
use multi_stark::plonkish::Value;
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;
use num_bigint::{BigInt, BigUint, Sign};
use std::collections::BTreeMap;

pub type Builder = CircuitBuilder<Scalar>;
const W: usize = 80;
const L: usize = 5;
const CARRY_BITS: usize = 89;

#[derive(Clone, Copy, Debug)]
pub struct FqVar(pub [Value; L]);

pub struct FqGadget {
  range: Table,
}

pub fn integer(v: Scalar) -> BigUint {
  BigUint::from_bytes_le(
    &v.canonical_limbs_le()
      .into_iter()
      .flat_map(u64::to_le_bytes)
      .collect::<Vec<_>>(),
  )
}
pub fn scalar(v: &BigUint) -> Scalar {
  let digits = v.to_u64_digits();
  let mut limbs = [0; 4];
  assert!(digits.len() <= 4);
  limbs[..digits.len()].copy_from_slice(&digits);
  Scalar::from_limbs_le(limbs)
}
fn signed(v: &BigInt) -> Scalar {
  let (sign, n) = v.clone().into_parts();
  let f = scalar(&n);
  if sign == Sign::Minus { -f } else { f }
}
pub fn modulus() -> BigUint {
  BigUint::from_bytes_le(&Fq::MODULUS.to_bytes_le())
}
fn digits(v: &BigUint) -> [BigUint; L] {
  let mask = (BigUint::from(1u8) << W) - 1u8;
  std::array::from_fn(|i| (v >> (W * i)) & &mask)
}
pub fn fq_value(values: &[Scalar]) -> Fq {
  let n = values
    .iter()
    .rev()
    .fold(BigUint::from(0u8), |acc, &v| (acc << W) + integer(v));
  Fq::from_le_bytes_mod_order(&n.to_bytes_le())
}

impl FqGadget {
  pub fn new(b: &mut Builder) -> Self {
    Self {
      range: b.fixed_table(
        "Fq u16",
        (0..=u16::MAX).map(|v| vec![Scalar::from_u16(v)]).collect(),
      ),
    }
  }
  pub fn range(&self, b: &mut Builder, value: Value, bits: usize) {
    match bits.div_ceil(16) {
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
    b: &mut Builder,
    value: Value,
    bits: usize,
  ) {
    assert!(bits > 0 && bits <= N * 16);
    let limbs = b.hint_many::<N>("bounded integer", &[value], |v| {
      let n = integer(v[0]);
      Ok(std::array::from_fn(|i| {
        scalar(&((&n >> (16 * i)) & BigUint::from(65535u32)))
      }))
    });
    for &limb in &limbs {
      b.lookup(self.range, &[limb]);
    }
    if !bits.is_multiple_of(16) {
      let top = b.scale(limbs[N - 1], Scalar::from_u64(1 << (16 - bits % 16)));
      b.lookup(self.range, &[top]);
    }
    let terms: Vec<_> = limbs
      .iter()
      .enumerate()
      .map(|(i, &v)| (scalar(&(BigUint::from(1u8) << (16 * i))), v))
      .collect();
    let packed = b.linear_combination(&terms, Scalar::ZERO);
    b.assert_equal(packed, value);
  }
  pub fn constant(&self, b: &mut Builder, value: Fq) -> FqVar {
    FqVar(
      digits(&BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()))
        .map(|n| b.constant(scalar(&n))),
    )
  }
  pub fn input(&self, b: &mut Builder, name: &str) -> FqVar {
    let result = FqVar(std::array::from_fn(|i| b.input(format!("{name}.{i}"))));
    self.bound(b, result);
    self.canonical(b, result);
    result
  }
  pub fn witness_values(value: Fq) -> [Scalar; L] {
    digits(&BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()))
      .map(|n| scalar(&n))
  }
  pub fn hint(
    &self,
    b: &mut Builder,
    name: &str,
    inputs: &[FqVar],
    f: impl Fn(&[Fq]) -> Result<Fq, String> + Send + Sync + 'static,
  ) -> FqVar {
    let deps: Vec<_> = inputs.iter().flat_map(|v| v.0).collect();
    let result = FqVar(b.hint_many(name, &deps, move |v| {
      let args: Vec<_> =
        v.as_chunks::<L>().0.iter().map(|v| fq_value(v)).collect();
      Ok(Self::witness_values(f(&args)?))
    }));
    self.bound(b, result);
    result
  }
  pub fn bound(&self, b: &mut Builder, v: FqVar) {
    for (i, &limb) in v.0.iter().enumerate() {
      self.range(b, limb, if i == L - 1 { 61 } else { W });
    }
  }
  pub fn canonical(&self, b: &mut Builder, v: FqVar) {
    let p = digits(&(modulus() - 1u8));
    let p_hint = p.clone();
    let advice =
      b.hint_many::<10>("Fq canonical subtraction", &v.0, move |values| {
        let mut borrow = BigInt::from(0u8);
        let radix = BigInt::from(1u8) << W;
        let mut out = [Scalar::ZERO; 10];
        for i in 0..L {
          let mut d = BigInt::from(p_hint[i].clone())
            - BigInt::from(integer(values[i]))
            - &borrow;
          borrow = BigInt::from(u8::from(d.sign() == Sign::Minus));
          if d.sign() == Sign::Minus {
            d += &radix;
          }
          out[i] = signed(&d);
          out[L + i] = signed(&borrow);
        }
        Ok(out)
      });
    let radix = scalar(&(BigUint::from(1u8) << W));
    let mut borrow = b.constant(Scalar::ZERO);
    for i in 0..L {
      self.range(b, advice[i], W);
      b.assert_bool(advice[L + i]);
      let eq = b.linear_combination(
        &[
          (Scalar::NEG_ONE, v.0[i]),
          (Scalar::NEG_ONE, borrow),
          (radix, advice[L + i]),
          (Scalar::NEG_ONE, advice[i]),
        ],
        scalar(&p[i]),
      );
      b.assert_zero(eq);
      borrow = advice[L + i];
    }
    b.assert_zero(borrow);
  }
  /// Sum of bounded quadratic and linear terms is zero modulo Fq.
  /// Each side has at most three unit-weight products. Limbs are <2^80,
  /// field representatives <2^381, quotient+2^383 <2^384. Four signed
  /// carries are biased by 2^88 and range-checked to 89 bits. Pairing two
  /// radix-2^80 coefficients keeps every integer equality below 2^251 < Fr.
  pub fn relation(
    &self,
    b: &mut Builder,
    products: &[(i8, FqVar, FqVar)],
    linear: &[(i8, FqVar)],
    constant: i8,
  ) {
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
      .flat_map(|(_, a, c)| a.0.into_iter().chain(c.0))
      .chain(linear.iter().flat_map(|(_, a)| a.0))
      .collect();
    let pc: Vec<_> = products.iter().map(|(c, _, _)| *c).collect();
    let lc: Vec<_> = linear.iter().map(|(c, _)| *c).collect();
    let p = digits(&modulus());
    let p_hint = p.clone();
    let advice =
      b.hint_many::<9>("Fq quotient and carries", &deps, move |values| {
        let mut t = vec![BigInt::from(0u8); 10];
        let mut at = 0;
        for &c in &pc {
          for i in 0..L {
            for j in 0..L {
              t[i + j] += BigInt::from(c)
                * BigInt::from(integer(values[at + i]))
                * BigInt::from(integer(values[at + L + j]));
            }
          }
          at += 2 * L;
        }
        for &c in &lc {
          for i in 0..L {
            t[i] += BigInt::from(c) * BigInt::from(integer(values[at + i]));
          }
          at += L;
        }
        t[0] += constant;
        let total = t.iter().rev().fold(BigInt::from(0u8), |a, c| (a << W) + c);
        let prime = BigInt::from(modulus());
        if &total % &prime != BigInt::from(0u8) {
          return Err("nonzero Fq relation".into());
        }
        let q: BigInt = total / prime + (BigInt::from(1u8) << 383usize);
        let q = q.to_biguint().ok_or("negative biased quotient")?;
        if q.bits() > 384 {
          return Err("Fq quotient overflow".into());
        }
        let q = digits(&q);
        let bias = digits(&(BigUint::from(1u8) << 383));
        for i in 0..L {
          for j in 0..L {
            t[i + j] -= BigInt::from(p_hint[i].clone())
              * (BigInt::from(q[j].clone()) - BigInt::from(bias[j].clone()));
          }
        }
        let mut out = [Scalar::ZERO; 9];
        for i in 0..L {
          out[i] = scalar(&q[i]);
        }
        let radix = BigInt::from(1u8) << W;
        let block_radix = &radix * &radix;
        let mut carry = BigInt::from(0u8);
        for j in 0..5 {
          carry += &t[2 * j] + &radix * &t[2 * j + 1];
          if &carry % &block_radix != BigInt::from(0u8) {
            return Err("nonintegral Fq carry".into());
          }
          carry /= &block_radix;
          if j < 4 {
            let biased: BigInt = &carry + (BigInt::from(1u8) << 88usize);
            let v = biased.to_biguint().ok_or("negative biased carry")?;
            if v.bits() > CARRY_BITS as u64 {
              return Err("Fq carry overflow".into());
            }
            out[L + j] = scalar(&v);
          }
        }
        if carry != BigInt::from(0u8) {
          return Err("nonzero final Fq carry".into());
        }
        Ok(out)
      });
    for (i, &v) in advice[..L].iter().enumerate() {
      self.range(b, v, if i == L - 1 { 64 } else { W });
    }
    for &v in &advice[L..] {
      self.range(b, v, CARRY_BITS);
    }
    let mut terms: Vec<Vec<(Scalar, Value)>> = vec![vec![]; 10];
    let mut cached = BTreeMap::new();
    for &(c, a, d) in products {
      for i in 0..L {
        for j in 0..L {
          let key = (
            a.0[i].index().min(d.0[j].index()),
            a.0[i].index().max(d.0[j].index()),
          );
          let v = *cached.entry(key).or_insert_with(|| b.mul(a.0[i], d.0[j]));
          terms[i + j].push((signed(&BigInt::from(c)), v));
        }
      }
    }
    for &(c, a) in linear {
      for (terms, v) in terms.iter_mut().zip(a.0) {
        terms.push((signed(&BigInt::from(c)), v));
      }
    }
    let bias = digits(&(BigUint::from(1u8) << 383));
    let mut constants = vec![BigInt::from(0u8); 10];
    constants[0] += constant;
    for i in 0..L {
      for j in 0..L {
        terms[i + j].push((-scalar(&p[i]), advice[j]));
        constants[i + j] += BigInt::from(&p[i] * &bias[j]);
      }
    }
    let radix = scalar(&(BigUint::from(1u8) << W));
    let block = radix * radix;
    let carry_bias = scalar(&(BigUint::from(1u8) << 88));
    for j in 0..5 {
      let mut equation = terms[2 * j].clone();
      equation.extend(terms[2 * j + 1].iter().map(|&(c, v)| (c * radix, v)));
      let mut constant =
        signed(&constants[2 * j]) + radix * signed(&constants[2 * j + 1]);
      if j > 0 {
        equation.push((Scalar::ONE, advice[L + j - 1]));
        constant -= carry_bias;
      }
      if j < 4 {
        equation.push((-block, advice[L + j]));
        constant += block * carry_bias;
      }
      let value = b.linear_combination(&equation, constant);
      b.assert_zero(value);
    }
  }
  pub fn mul(&self, b: &mut Builder, x: FqVar, y: FqVar) -> FqVar {
    let result = self.hint(b, "Fq product", &[x, y], |v| Ok(v[0] * v[1]));
    self.relation(b, &[(1, x, y)], &[(-1, result)], 0);
    result
  }
  pub fn equal(&self, b: &mut Builder, x: FqVar, y: FqVar) {
    self.relation(b, &[], &[(1, x), (-1, y)], 0);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::plonkish::Assignment;
  use multi_stark::plonkish::Circuit;
  use std::collections::{HashMap, HashSet};

  pub(super) fn check_mutations(c: &Circuit<Scalar>, a: &Assignment<Scalar>) {
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
          + if changed == Some(v.index()) { Scalar::ONE } else { Scalar::ZERO }
      };
      c.gates().iter().all(|g| {
        let [a, b, c] = g.wires.map(value);
        let [qm, qa, qb, qc, k] = g.coefficients;
        qm * a * b + qa * a + qb * b + qc * c + k == Scalar::ZERO
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

  #[test]
  fn products_and_adversarial_assignments() {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let x = f.input(&mut b, "x");
    let y = f.input(&mut b, "y");
    let out = f.mul(&mut b, x, y);
    let c = b.finish();
    let cases = [
      (Fq::from(0u8), Fq::from(1u8)),
      (-Fq::from(1u8), -Fq::from(1u8)),
      (Fq::from(42u8), Fq::from(999u64)),
    ];
    for (xv, yv) in cases {
      let mut w = c.witness();
      for (v, n) in x
        .0
        .into_iter()
        .zip(FqGadget::witness_values(xv))
        .chain(y.0.into_iter().zip(FqGadget::witness_values(yv)))
      {
        w.set(v, n).unwrap();
      }
      let a = w.generate().unwrap();
      assert_eq!(fq_value(&out.0.map(|v| a.value(v).unwrap())), xv * yv);
      check_mutations(&c, &a);
    }
  }

  #[test]
  fn rejects_noncanonical_and_out_of_range() {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let x = f.input(&mut b, "x");
    let c = b.finish();
    for n in [modulus(), modulus() + 1u8, (BigUint::from(1u8) << 381) - 1u8] {
      let mut w = c.witness();
      for (v, n) in x.0.into_iter().zip(digits(&n)) {
        w.set(v, scalar(&n)).unwrap();
      }
      assert!(w.generate().is_err());
    }
    for i in 0..L {
      let mut w = c.witness();
      for (j, v) in x.0.into_iter().enumerate() {
        w.set(
          v,
          if i == j {
            scalar(&(BigUint::from(1u8) << if i == 4 { 61 } else { 80 }))
          } else {
            Scalar::ZERO
          },
        )
        .unwrap();
      }
      assert!(w.generate().is_err());
    }
  }

  #[test]
  fn bounded_relations_accept_redundant_representatives() {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let x = FqVar(std::array::from_fn(|i| b.input(format!("x{i}"))));
    f.bound(&mut b, x);
    let z = f.constant(&mut b, Fq::from(0u8));
    f.equal(&mut b, x, z);
    // Exercise the maximum permitted quadratic weight and negative quotient.
    f.relation(&mut b, &[(-3, x, x)], &[(3, x)], 0);
    let c = b.finish();
    let mut w = c.witness();
    for (v, n) in x.0.into_iter().zip(digits(&modulus())) {
      w.set(v, scalar(&n)).unwrap();
    }
    check_mutations(&c, &w.generate().unwrap());
  }

  #[test]
  fn integer_bounds_do_not_wrap_fr() {
    use ark_bls12_381::Fr;
    let one = BigUint::from(1u8);
    let radix = &one << 80;
    let max = (&one << 381) - 1u8;
    let max_expression = 3u8 * &max * &max + 3u8 * &max + 4u8;
    assert!(max_expression / modulus() < (&one << 383));
    // Up to 15 products on either side of a coefficient, plus five
    // quotient*modulus terms, three linear limbs, and a constant.
    let coefficient_bound = 20u8 * &radix * &radix + 3u8 * &radix + 4u8;
    let carry_bound = &one << 88;
    let equation_bound: BigUint = (&radix + 1u8) * &coefficient_bound
      + (&radix * &radix + 1u8) * &carry_bound;
    let fr = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    assert!(equation_bound < fr);
    assert!(
      ((&radix + 1u8) * coefficient_bound + &carry_bound) / (&radix * &radix)
        < carry_bound
    );
  }
}
