//! Affine arithmetic with constrained denominators; exceptional sums reject.
use crate::kzg::Scalar;
use crate::recursive::native_field::Builder;
use crate::recursive::native_field::FqGadget;
use crate::recursive::native_field::FqVar;
use ark_bls12_381::{Fq, G1Affine};
use ark_ec::{AdditiveGroup, AffineRepr};
use ark_ff::Field;
use multi_stark::plonkish::Bool;
use multi_stark::plonkish::Value;
use multi_stark::traits::Field as NativeField;

#[derive(Clone, Copy)]
pub struct Affine {
  pub x: FqVar,
  pub y: FqVar,
}
#[derive(Clone, Copy)]
pub struct PointInput {
  pub point: Affine,
  pub infinity: Bool,
}

impl Affine {
  pub fn constant(b: &mut Builder, f: &FqGadget, p: G1Affine) -> Self {
    assert!(!p.infinity);
    Self { x: f.constant(b, p.x), y: f.constant(b, p.y) }
  }
  pub fn select(b: &mut Builder, bit: Bool, yes: Self, no: Self) -> Self {
    Self {
      x: FqVar(std::array::from_fn(|i| b.select(bit, yes.x.0[i], no.x.0[i]))),
      y: FqVar(std::array::from_fn(|i| b.select(bit, yes.y.0[i], no.y.0[i]))),
    }
  }
  pub fn on_curve(self, b: &mut Builder, f: &FqGadget) {
    let xx = f.mul(b, self.x, self.x);
    f.relation(b, &[(1, xx, self.x), (-1, self.y, self.y)], &[], 4);
  }
  pub fn double(self, b: &mut Builder, f: &FqGadget) -> Self {
    let slope = f.hint(b, "doubling slope", &[self.x, self.y], |v| {
      Ok(
        v[0].square()
          * Fq::from(3u8)
          * (v[1].double().inverse().ok_or("zero doubling denominator")?),
      )
    });
    f.relation(b, &[(2, self.y, slope), (-3, self.x, self.x)], &[], 0);
    // For an on-curve input y=0 implies x != 0, so the slope equation
    // itself rejects the only possible zero denominator.
    let x = f.hint(b, "double x", &[slope, self.x], |v| {
      Ok(v[0].square() - v[1].double())
    });
    f.relation(b, &[(1, slope, slope)], &[(-2, self.x), (-1, x)], 0);
    let y = f.hint(b, "double y", &[slope, self.x, x, self.y], |v| {
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
  pub fn add(self, b: &mut Builder, f: &FqGadget, rhs: Self) -> Self {
    let inv = f.hint(b, "addition inverse", &[rhs.x, self.x], |v| {
      (v[0] - v[1]).inverse().ok_or("exceptional affine addition".into())
    });
    f.relation(b, &[(1, rhs.x, inv), (-1, self.x, inv)], &[], -1);
    let slope = f.hint(b, "addition slope", &[rhs.y, self.y, inv], |v| {
      Ok((v[0] - v[1]) * v[2])
    });
    f.relation(
      b,
      &[(1, slope, rhs.x), (-1, slope, self.x)],
      &[(-1, rhs.y), (1, self.y)],
      0,
    );
    let x = f.hint(b, "sum x", &[slope, self.x, rhs.x], |v| {
      Ok(v[0].square() - v[1] - v[2])
    });
    f.relation(
      b,
      &[(1, slope, slope)],
      &[(-1, self.x), (-1, rhs.x), (-1, x)],
      0,
    );
    let y = f.hint(b, "sum y", &[slope, self.x, x, self.y], |v| {
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
  pub fn constant_mul(self, b: &mut Builder, f: &FqGadget, n: u64) -> Self {
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
  pub fn equal(self, b: &mut Builder, f: &FqGadget, rhs: Self) {
    f.equal(b, self.x, rhs.x);
    f.equal(b, self.y, rhs.y);
  }
  pub fn subgroup(self, b: &mut Builder, f: &FqGadget) {
    // Same endomorphism criterion as ark-bls12-381's native checker.
    let xp = self.constant_mul(b, f, 0xd201000000010000);
    let inv =
      f.hint(b, "reject exceptional subgroup point", &[xp.x, self.x], |v| {
        (v[0] - v[1]).inverse().ok_or("exceptional subgroup point".into())
      });
    f.relation(b, &[(1, xp.x, inv), (-1, self.x, inv)], &[], -1);
    let x2p = xp.constant_mul(b, f, 0xd201000000010000);
    let beta = f.constant(b, ark_bls12_381::g1::BETA);
    f.relation(b, &[(1, beta, self.x)], &[(-1, x2p.x)], 0);
    f.relation(b, &[], &[(1, self.y), (1, x2p.y)], 0);
  }
}
impl PointInput {
  pub fn new(b: &mut Builder, f: &FqGadget, name: &str) -> Self {
    let point = Affine {
      x: f.input(b, &format!("{name}.x")),
      y: f.input(b, &format!("{name}.y")),
    };
    let flag = b.input(format!("{name}.infinity"));
    let infinity = b.assert_bool(flag);
    for v in point.x.0.into_iter().chain(point.y.0) {
      let zero = b.mul(v, flag);
      b.assert_zero(zero);
    }
    let result = Self { point, infinity };
    let p = result.nonzero(b, f);
    p.on_curve(b, f);
    p.subgroup(b, f);
    result
  }
  pub fn nonzero(self, b: &mut Builder, f: &FqGadget) -> Affine {
    let g = Affine::constant(b, f, G1Affine::generator());
    Affine::select(b, self.infinity, g, self.point)
  }
  pub fn inputs(self, p: G1Affine) -> Vec<(Value, Scalar)> {
    let (x, y) =
      if p.infinity { (Fq::from(0u8), Fq::from(0u8)) } else { (p.x, p.y) };
    self
      .point
      .x
      .0
      .into_iter()
      .zip(FqGadget::witness_values(x))
      .chain(self.point.y.0.into_iter().zip(FqGadget::witness_values(y)))
      .chain([(self.infinity.value(), Scalar::from_u8(u8::from(p.infinity)))])
      .collect()
  }
}

pub fn measure(
  operation: &str,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
  use ark_ec::CurveGroup;
  let start = std::time::Instant::now();
  let mut b = Builder::new();
  let f = FqGadget::new(&mut b);
  let p = PointInput::new(&mut b, &f, "point");
  let g = G1Affine::generator();
  let before = b.stats();
  let a = p.nonzero(&mut b, &f);
  match operation {
    "native-subgroup" => {},
    "native-double" => {
      let out = a.double(&mut b, &f);
      let expected = Affine::constant(
        &mut b,
        &f,
        (g * ark_bls12_381::Fr::from(2u8)).into_affine(),
      );
      out.equal(&mut b, &f, expected);
    },
    "native-add" => {
      let rhs = Affine::constant(
        &mut b,
        &f,
        (g * ark_bls12_381::Fr::from(7u8)).into_affine(),
      );
      let out = a.add(&mut b, &f, rhs);
      let expected = Affine::constant(
        &mut b,
        &f,
        (g * ark_bls12_381::Fr::from(8u8)).into_affine(),
      );
      out.equal(&mut b, &f, expected);
    },
    _ => return Err("unknown native operation".into()),
  }
  let stats = b.stats();
  let c = b.finish();
  let mut w = c.witness();
  for (v, n) in p.inputs(g) {
    w.set(v, n)?;
  }
  let _a = w.generate()?;
  Ok(
    serde_json::json!({"operation":operation,"gates":stats.gates,"lookups":stats.lookups,"values":stats.values,"additional_gates":stats.gates-before.gates,"additional_lookups":stats.lookups-before.lookups,"seconds":start.elapsed().as_secs_f64(),"satisfied":true,"scope":"Native Plonkish curve primitive; not a complete recursive verifier"}),
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::CurveGroup;
  #[test]
  fn subgroup_infinity_and_reject_wrong_subgroup() {
    let mut b = Builder::new();
    let f = FqGadget::new(&mut b);
    let p = PointInput::new(&mut b, &f, "p");
    let c = b.finish();
    let run = |point| {
      let mut w = c.witness();
      for (v, n) in p.inputs(point) {
        w.set(v, n).unwrap();
      }
      w.generate()
    };
    for n in [0u64, 1, 2, 123456789, u64::MAX] {
      run((G1Affine::generator() * ark_bls12_381::Fr::from(n)).into_affine())
        .unwrap();
    }
    let torsion = G1Affine::new_unchecked(Fq::from(0u8), Fq::from(2u8));
    assert!(torsion.is_on_curve());
    assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());
    assert!(run(torsion).is_err());
    let mut checked = 0;
    for x in 1..100u64 {
      if let Some(point) =
        G1Affine::get_point_from_x_unchecked(Fq::from(x), false)
      {
        assert!(!point.is_in_correct_subgroup_assuming_on_curve());
        assert!(run(point).is_err());
        checked += 1;
        if checked == 8 {
          break;
        }
      }
    }
    assert_eq!(checked, 8);
    assert!(
      run(G1Affine::new_unchecked(Fq::from(7u8), Fq::from(9u8))).is_err()
    );
  }
  #[test]
  fn affine_operations() {
    for operation in ["native-add", "native-double"] {
      measure(operation).unwrap();
    }
  }
}
