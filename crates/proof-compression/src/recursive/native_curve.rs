//! Affine arithmetic with constrained denominators and a complete final addition.
use crate::kzg::{
  curve::{Bn254, G1AffineOf, KzgCurve},
  field::CurveScalar,
};
use crate::recursive::native_field::{
  Builder, FqGadget, FqVar, fq_value, limb_count,
};
use ark_ec::{AdditiveGroup, AffineRepr};
use ark_ff::Field;
use multi_stark::{
  plonkish::{Bool, Value},
  traits::{Algebra, Field as NativeField},
};

pub struct Affine<C: KzgCurve = Bn254> {
  pub x: FqVar<C>,
  pub y: FqVar<C>,
}

impl<C: KzgCurve> Clone for Affine<C> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<C: KzgCurve> Copy for Affine<C> {}

pub struct PointInput<C: KzgCurve = Bn254> {
  pub point: Affine<C>,
  pub infinity: Bool,
}

impl<C: KzgCurve> Clone for PointInput<C> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<C: KzgCurve> Copy for PointInput<C> {}

impl<C: KzgCurve> Affine<C> {
  pub fn constant(
    b: &mut Builder<C>,
    f: &FqGadget<C>,
    p: G1AffineOf<C>,
  ) -> Self {
    assert!(!p.infinity);
    Self { x: f.constant(b, p.x), y: f.constant(b, p.y) }
  }
  pub fn select(b: &mut Builder<C>, bit: Bool, yes: Self, no: Self) -> Self {
    let yes_x = yes.x.limbs();
    let no_x = no.x.limbs();
    let yes_y = yes.y.limbs();
    let no_y = no.y.limbs();
    Self {
      x: FqVar::from_fn(|i| b.select(bit, yes_x[i], no_x[i])),
      y: FqVar::from_fn(|i| b.select(bit, yes_y[i], no_y[i])),
    }
  }
  pub fn on_curve(self, b: &mut Builder<C>, f: &FqGadget<C>) {
    let xx = f.mul(b, self.x, self.x);
    let coefficient = i8::try_from(C::CURVE_B).expect("small curve b");
    f.relation(b, &[(1, xx, self.x), (-1, self.y, self.y)], &[], coefficient);
  }
  pub fn double(self, b: &mut Builder<C>, f: &FqGadget<C>) -> Self {
    let slope = f.hint_pure(b, "doubling slope", &[self.x, self.y], |v| {
      Ok(
        v[0].square()
          * C::Fq::from(3u8)
          * (v[1].double().inverse().ok_or("zero doubling denominator")?),
      )
    });
    f.relation(b, &[(2, self.y, slope), (-3, self.x, self.x)], &[], 0);
    // For an on-curve input y=0 implies x != 0, so the slope equation
    // itself rejects the only possible zero denominator.
    let x = f.hint_pure(b, "double x", &[slope, self.x], |v| {
      Ok(v[0].square() - v[1].double())
    });
    f.relation(b, &[(1, slope, slope)], &[(-2, self.x), (-1, x)], 0);
    let y = f.hint_pure(b, "double y", &[slope, self.x, x, self.y], |v| {
      Ok(v[0] * (v[1] - v[2]) - v[3])
    });
    f.relation(
      b,
      &[(1, slope, self.x), (-1, slope, x)],
      &[(-1, self.y), (-1, y)],
      0,
    );
    Self { x, y }
  }
  pub fn add(self, b: &mut Builder<C>, f: &FqGadget<C>, rhs: Self) -> Self {
    let inv = f.hint_pure(b, "addition inverse", &[rhs.x, self.x], |v| {
      (v[0] - v[1]).inverse().ok_or("exceptional affine addition".into())
    });
    f.relation(b, &[(1, rhs.x, inv), (-1, self.x, inv)], &[], -1);
    let slope = f.hint_pure(b, "addition slope", &[rhs.y, self.y, inv], |v| {
      Ok((v[0] - v[1]) * v[2])
    });
    f.relation(
      b,
      &[(1, slope, rhs.x), (-1, slope, self.x)],
      &[(-1, rhs.y), (1, self.y)],
      0,
    );
    let x = f.hint_pure(b, "sum x", &[slope, self.x, rhs.x], |v| {
      Ok(v[0].square() - v[1] - v[2])
    });
    f.relation(
      b,
      &[(1, slope, slope)],
      &[(-1, self.x), (-1, rhs.x), (-1, x)],
      0,
    );
    let y = f.hint_pure(b, "sum y", &[slope, self.x, x, self.y], |v| {
      Ok(v[0] * (v[1] - v[2]) - v[3])
    });
    f.relation(
      b,
      &[(1, slope, self.x), (-1, slope, x)],
      &[(-1, self.y), (-1, y)],
      0,
    );
    Self { x, y }
  }

  /// Complete addition of nonidentity prime-order inputs. The ordinary affine
  /// branch receives fixed, distinct points when its denominator would vanish.
  /// Equal inputs use doubling; opposite inputs have canonical zero coordinates.
  pub fn add_complete(
    self,
    b: &mut Builder<C>,
    f: &FqGadget<C>,
    rhs: Self,
  ) -> PointInput<C> {
    let same_x = equal_flag(b, f, self.x, rhs.x);
    let same_y = equal_flag(b, f, self.y, rhs.y);
    let g = G1AffineOf::<C>::generator();
    let fallback_left = Self::constant(b, f, g);
    let fallback_right = Self::constant(b, f, (g + g).into());
    let left = Self::select(b, same_x, fallback_left, self);
    let right = Self::select(b, same_x, fallback_right, rhs);
    let ordinary = left.add(b, f, right);
    let doubled = self.double(b, f);
    let zero = f.constant(b, C::Fq::from(0u8));
    let exceptional =
      Self::select(b, same_y, doubled, Self { x: zero, y: zero });
    let point = Self::select(b, same_x, exceptional, ordinary);
    let different_y = b.affine(
      [same_y.value(), same_y.value()],
      [CurveScalar::<C>::NEG_ONE, CurveScalar::<C>::ZERO],
      CurveScalar::<C>::ONE,
    );
    let infinity = b.mul(same_x.value(), different_y);
    PointInput { point, infinity: b.assert_bool(infinity) }
  }
  pub fn constant_mul(
    self,
    b: &mut Builder<C>,
    f: &FqGadget<C>,
    n: u64,
  ) -> Self {
    assert!(n > 0);
    let mut acc = self;
    for i in (0..63 - n.leading_zeros()).rev() {
      acc = acc.double(b, f);
      if n & (1u64 << i) != 0 {
        acc = acc.add(b, f, self);
      }
    }
    acc
  }
  pub fn equal(self, b: &mut Builder<C>, f: &FqGadget<C>, rhs: Self) {
    f.equal(b, self.x, rhs.x);
    f.equal(b, self.y, rhs.y);
  }

  /// Subgroup membership check. BN254 G1 has cofactor one so `on_curve`
  /// suffices; BLS12-381 enforces the endomorphism criterion matching
  /// `ark-bls12-381`'s native checker.
  pub fn subgroup(self, b: &mut Builder<C>, f: &FqGadget<C>) {
    if !C::HAS_COFACTOR {
      return;
    }
    let xp = self.constant_mul(b, f, C::SUBGROUP_CHECK_SEED);
    let inv = f.hint_pure(
      b,
      "reject exceptional subgroup point",
      &[xp.x, self.x],
      |v| (v[0] - v[1]).inverse().ok_or("exceptional subgroup point".into()),
    );
    f.relation(b, &[(1, xp.x, inv), (-1, self.x, inv)], &[], -1);
    let x2p = xp.constant_mul(b, f, C::SUBGROUP_CHECK_SEED);
    let beta =
      f.constant(b, C::endo_beta().expect("cofactor curve has endo beta"));
    f.relation(b, &[(1, beta, self.x)], &[(-1, x2p.x)], 0);
    f.relation(b, &[], &[(1, self.y), (1, x2p.y)], 0);
  }
}

fn equal_flag<C: KzgCurve>(
  b: &mut Builder<C>,
  f: &FqGadget<C>,
  lhs: FqVar<C>,
  rhs: FqVar<C>,
) -> Bool {
  let l = limb_count::<C>();
  let deps: Vec<_> = lhs.limbs().iter().chain(rhs.limbs()).copied().collect();
  let equal = b.hint("Fq equality", &deps, move |v| {
    Ok(CurveScalar::<C>::from_bool(
      fq_value::<C>(&v[..l]) == fq_value::<C>(&v[l..]),
    ))
  });
  let flag = b.assert_bool(equal);
  let zero = b.constant(CurveScalar::<C>::ZERO);
  let flag_fq = FqVar::from_fn(|i| if i == 0 { equal } else { zero });
  let inverse = f.hint_pure(b, "Fq equality inverse", &[lhs, rhs], |v| {
    Ok((v[0] - v[1]).inverse().unwrap_or(C::Fq::from(0u8)))
  });
  f.relation(b, &[(1, lhs, inverse), (-1, rhs, inverse)], &[(1, flag_fq)], -1);
  f.relation(b, &[(1, lhs, flag_fq), (-1, rhs, flag_fq)], &[], 0);
  f.relation(b, &[(1, inverse, flag_fq)], &[], 0);
  flag
}

impl<C: KzgCurve> PointInput<C> {
  pub fn new(b: &mut Builder<C>, f: &FqGadget<C>, name: &str) -> Self {
    let point = Affine {
      x: f.input(b, &format!("{name}.x")),
      y: f.input(b, &format!("{name}.y")),
    };
    let flag = b.input(format!("{name}.infinity"));
    let infinity = b.assert_bool(flag);
    for &v in point.x.limbs().iter().chain(point.y.limbs()) {
      let zero = b.mul(v, flag);
      b.assert_zero(zero);
    }
    let result = Self { point, infinity };
    let p = result.nonzero(b, f);
    p.on_curve(b, f);
    p.subgroup(b, f);
    result
  }
  pub fn nonzero(self, b: &mut Builder<C>, f: &FqGadget<C>) -> Affine<C> {
    let g = Affine::constant(b, f, G1AffineOf::<C>::generator());
    Affine::select(b, self.infinity, g, self.point)
  }
  pub fn canonical(self, b: &mut Builder<C>, f: &FqGadget<C>) -> Self {
    let x = f.hint_pure(b, "output x", &[self.point.x], |v| Ok(v[0]));
    f.equal(b, x, self.point.x);
    f.canonical(b, x);
    let y = f.hint_pure(b, "output y", &[self.point.y], |v| Ok(v[0]));
    f.equal(b, y, self.point.y);
    f.canonical(b, y);
    Self { point: Affine { x, y }, infinity: self.infinity }
  }
  pub fn inputs(self, p: G1AffineOf<C>) -> Vec<(Value, CurveScalar<C>)> {
    let (x, y) = if p.infinity {
      (C::Fq::from(0u8), C::Fq::from(0u8))
    } else {
      (p.x, p.y)
    };
    self
      .point
      .x
      .limbs()
      .iter()
      .copied()
      .zip(FqGadget::<C>::witness_values(x))
      .chain(
        self
          .point
          .y
          .limbs()
          .iter()
          .copied()
          .zip(FqGadget::<C>::witness_values(y)),
      )
      .chain([(
        self.infinity.value(),
        CurveScalar::<C>::from_u8(u8::from(p.infinity)),
      )])
      .collect()
  }
}

#[cfg(test)]
fn check_operation<C: KzgCurve>(
  operation: &str,
) -> Result<(), Box<dyn std::error::Error>> {
  use ark_ec::CurveGroup;
  let mut b = Builder::<C>::new();
  let f = FqGadget::<C>::new(&mut b);
  let p = PointInput::<C>::new(&mut b, &f, "point");
  let g = G1AffineOf::<C>::generator();
  let a = p.nonzero(&mut b, &f);
  match operation {
    "native-subgroup" => {},
    "native-double" => {
      let out = a.double(&mut b, &f);
      let expected =
        Affine::constant(&mut b, &f, (g * C::Fr::from(2u8)).into_affine());
      out.equal(&mut b, &f, expected);
    },
    "native-add" => {
      let rhs =
        Affine::constant(&mut b, &f, (g * C::Fr::from(7u8)).into_affine());
      let out = a.add(&mut b, &f, rhs);
      let expected =
        Affine::constant(&mut b, &f, (g * C::Fr::from(8u8)).into_affine());
      out.equal(&mut b, &f, expected);
    },
    _ => return Err("unknown native operation".into()),
  }
  let c = b.finish();
  let mut w = c.witness();
  for (v, n) in p.inputs(g) {
    w.set(v, n)?;
  }
  let _a = w.generate()?;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::Bls12381;
  use ark_ec::CurveGroup;

  fn test_subgroup_infinity_and_reject_invalid_points<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let p = PointInput::<C>::new(&mut b, &f, "p");
    let c = b.finish();
    let run = |point| {
      let mut w = c.witness();
      for (v, n) in p.inputs(point) {
        w.set(v, n).unwrap();
      }
      w.generate()
    };
    for n in [0u64, 1, 2, 123456789, u64::MAX] {
      let point = (G1AffineOf::<C>::generator() * C::Fr::from(n)).into_affine();
      run(point).unwrap();
      run(-point).unwrap();
    }
    if C::HAS_COFACTOR {
      let torsion =
        G1AffineOf::<C>::new_unchecked(C::Fq::from(0u8), C::Fq::from(2u8));
      assert!(torsion.is_on_curve());
      assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());
      assert!(run(torsion).is_err());
      let mut checked = 0;
      for x in 1..100u64 {
        if let Some(point) =
          G1AffineOf::<C>::get_point_from_x_unchecked(C::Fq::from(x), false)
          && !point.is_in_correct_subgroup_assuming_on_curve()
        {
          assert!(run(point).is_err());
          checked += 1;
          if checked == 8 {
            break;
          }
        }
      }
      assert_eq!(checked, 8);
    }
    assert!(
      run(G1AffineOf::<C>::new_unchecked(C::Fq::from(7u8), C::Fq::from(9u8)))
        .is_err()
    );
  }

  #[test]
  fn subgroup_infinity_and_reject_invalid_points() {
    test_subgroup_infinity_and_reject_invalid_points::<Bn254>();
    test_subgroup_infinity_and_reject_invalid_points::<Bls12381>();
  }

  fn test_rejects_coordinate_aliases_and_invalid_infinity<C: KzgCurve>() {
    use crate::recursive::native_field::{W, modulus, scalar};
    use ark_ff::{BigInteger, PrimeField};
    use num_bigint::BigUint;

    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let p = PointInput::<C>::new(&mut b, &f, "p");
    let c = b.finish();
    let generator = G1AffineOf::<C>::generator();
    let radix_mask = (BigUint::from(1u8) << W) - 1u8;
    for coordinate in [p.point.x, p.point.y] {
      let value = if coordinate.limbs()[0] == p.point.x.limbs()[0] {
        generator.x
      } else {
        generator.y
      };
      let alias = modulus::<C>()
        + BigUint::from_bytes_le(&value.into_bigint().to_bytes_le());
      let mut w = c.witness();
      for (handle, mut value) in p.inputs(generator) {
        if let Some(i) = coordinate.limbs().iter().position(|&v| v == handle) {
          value = scalar::<C>(&((&alias >> (W * i)) & &radix_mask));
        }
        w.set(handle, value).unwrap();
      }
      assert!(w.generate().is_err());
    }
    for (point, flag) in [
      (generator, CurveScalar::<C>::ONE),
      (generator, CurveScalar::<C>::TWO),
      (G1AffineOf::<C>::identity(), CurveScalar::<C>::ZERO),
    ] {
      let mut w = c.witness();
      for (handle, value) in p.inputs(point) {
        w.set(handle, if handle == p.infinity.value() { flag } else { value })
          .unwrap();
      }
      assert!(w.generate().is_err());
    }
  }

  #[test]
  fn rejects_coordinate_aliases_and_invalid_infinity() {
    test_rejects_coordinate_aliases_and_invalid_infinity::<Bn254>();
    test_rejects_coordinate_aliases_and_invalid_infinity::<Bls12381>();
  }

  #[test]
  fn affine_operations() {
    for operation in ["native-subgroup", "native-add", "native-double"] {
      check_operation::<Bn254>(operation).unwrap();
      check_operation::<Bls12381>(operation).unwrap();
    }
  }

  fn test_complete_add<C: KzgCurve>() {
    let mut b = Builder::<C>::new();
    let f = FqGadget::<C>::new(&mut b);
    let left = PointInput::<C>::new(&mut b, &f, "left");
    let right = PointInput::<C>::new(&mut b, &f, "right");
    let lhs = left.nonzero(&mut b, &f);
    let rhs = right.nonzero(&mut b, &f);
    let result = lhs.add_complete(&mut b, &f, rhs);
    let result = result.canonical(&mut b, &f);
    let c = b.finish();
    let p = G1AffineOf::<C>::generator();
    for q in [p, -p, (p * C::Fr::from(7u8)).into_affine()] {
      let mut w = c.witness();
      for (v, n) in left.inputs(p).into_iter().chain(right.inputs(q)) {
        w.set(v, n).unwrap();
      }
      let a = w.generate().unwrap();
      let xs: Vec<_> =
        result.point.x.limbs().iter().map(|&v| a.value(v).unwrap()).collect();
      let ys: Vec<_> =
        result.point.y.limbs().iter().map(|&v| a.value(v).unwrap()).collect();
      let x = fq_value::<C>(&xs);
      let y = fq_value::<C>(&ys);
      let actual =
        if a.value(result.infinity.value()).unwrap() == CurveScalar::<C>::ONE {
          assert_eq!(x, C::Fq::from(0u8));
          assert_eq!(y, C::Fq::from(0u8));
          G1AffineOf::<C>::identity()
        } else {
          G1AffineOf::<C>::new_unchecked(x, y)
        };
      assert_eq!(actual, (p + q).into_affine());
    }
  }

  #[test]
  fn complete_add_equal_opposite_and_distinct_points() {
    test_complete_add::<Bn254>();
    test_complete_add::<Bls12381>();
  }
}
