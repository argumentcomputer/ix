use p3_field::{Field, PrimeCharacteristicRing};

use multi_stark::plonkish::Bool;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;

/// Coordinates `a + b*X + c*X²` in the Protocol v6 cubic trinomial extension
/// `F_p[X] / (X³ - X - 1)` (`X³ = X + 1`, `X⁴ = X² + X`).
/// Arithmetic uses native base-field constraints, not foreign-field emulation.
#[derive(Clone, Copy, Debug)]
pub struct CubicValue(pub [Value; 3]);

impl CubicValue {
  pub fn select<F: Field + multi_stark::traits::Field>(
    b: &mut CircuitBuilder<F>,
    bit: Bool,
    yes: Self,
    no: Self,
  ) -> Self {
    Self(std::array::from_fn(|i| b.select(bit, yes.0[i], no.0[i])))
  }

  pub fn mul_base<F: Field + multi_stark::traits::Field>(
    self,
    b: &mut CircuitBuilder<F>,
    value: Value,
  ) -> Self {
    Self(self.0.map(|coordinate| b.mul(coordinate, value)))
  }

  pub fn input<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    name: &str,
  ) -> Self {
    Self(std::array::from_fn(|i| builder.input(format!("{name}[{i}]"))))
  }

  pub fn constant<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    coordinates: [F; 3],
  ) -> Self {
    Self(coordinates.map(|c| builder.constant(c)))
  }

  pub fn from_base<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    value: Value,
  ) -> Self {
    let zero = builder.constant(<F as PrimeCharacteristicRing>::ZERO);
    Self([value, zero, zero])
  }

  pub fn add<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
    rhs: Self,
  ) -> Self {
    Self(std::array::from_fn(|i| builder.add(self.0[i], rhs.0[i])))
  }

  pub fn sub<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
    rhs: Self,
  ) -> Self {
    Self(std::array::from_fn(|i| builder.sub(self.0[i], rhs.0[i])))
  }

  pub fn neg<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
  ) -> Self {
    let zero = builder.constant(<F as PrimeCharacteristicRing>::ZERO);
    Self(self.0.map(|v| builder.sub(zero, v)))
  }

  pub fn scale<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
    scalar: F,
  ) -> Self {
    let scalar = builder.constant(scalar);
    Self(self.0.map(|v| builder.mul(v, scalar)))
  }

  /// Karatsuba multiplication modulo `X³ - X - 1` (6 base multiplications).
  pub fn mul<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
    rhs: Self,
  ) -> Self {
    let v0 = builder.mul(self.0[0], rhs.0[0]);
    let v1 = builder.mul(self.0[1], rhs.0[1]);
    let v2 = builder.mul(self.0[2], rhs.0[2]);
    let a01 = builder.add(self.0[0], self.0[1]);
    let b01 = builder.add(rhs.0[0], rhs.0[1]);
    let m01 = builder.mul(a01, b01);
    let m01 = builder.sub(m01, v0);
    let m01 = builder.sub(m01, v1);
    let a02 = builder.add(self.0[0], self.0[2]);
    let b02 = builder.add(rhs.0[0], rhs.0[2]);
    let m02 = builder.mul(a02, b02);
    let m02 = builder.sub(m02, v0);
    let m02 = builder.sub(m02, v2);
    let a12 = builder.add(self.0[1], self.0[2]);
    let b12 = builder.add(rhs.0[1], rhs.0[2]);
    let m12 = builder.mul(a12, b12);
    let m12 = builder.sub(m12, v1);
    let m12 = builder.sub(m12, v2);
    let c0 = builder.add(v0, m12);
    let t1 = builder.add(m01, m12);
    let c1 = builder.add(t1, v2);
    let t2 = builder.add(m02, v1);
    let c2 = builder.add(t2, v2);
    Self([c0, c1, c2])
  }

  /// Recombine `c0 + c1*X + c2*X²` in `F_p[X]/(X³ - X - 1)` using linear
  /// combinations only (`X³ = 1 + X`, `X⁴ = X + X²`).
  pub fn from_basis<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    c0: Self,
    c1: Self,
    c2: Self,
  ) -> Self {
    let one = <F as PrimeCharacteristicRing>::ONE;
    let zero = <F as PrimeCharacteristicRing>::ZERO;
    let r0 = builder.linear_combination(
      &[(one, c0.0[0]), (one, c1.0[2]), (one, c2.0[1])],
      zero,
    );
    let r1 = builder.linear_combination(
      &[
        (one, c0.0[1]),
        (one, c1.0[0]),
        (one, c1.0[2]),
        (one, c2.0[1]),
        (one, c2.0[2]),
      ],
      zero,
    );
    let r2 = builder.linear_combination(
      &[(one, c0.0[2]), (one, c1.0[1]), (one, c2.0[0]), (one, c2.0[2])],
      zero,
    );
    Self([r0, r1, r2])
  }

  /// Constrained multiplicative inverse in `F_p[X]/(X³ - X - 1)`.
  ///
  /// The witness hint computes the adjugate-norm inverse, and the circuit
  /// enforces `self * inv == 1`, rejecting zero and any forged hint with no
  /// soundness gap.
  pub fn inverse<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
  ) -> Self {
    let inv = Self(builder.hint_many("cubic inverse", &self.0, |v| {
      let [a0, a1, a2] = [v[0], v[1], v[2]];
      let s = a0 + a2;
      let d0 = s * s - a1 * (a1 + a2);
      let d1 = a2 * a2 - a0 * a1;
      let d2 = a1 * a1 - a2 * s;
      let norm = a0 * d0 + a2 * d1 + a1 * d2;
      let ninv = Field::try_inverse(&norm)
        .ok_or_else(|| "cubic extension inverse of zero".to_string())?;
      Ok([d0 * ninv, d1 * ninv, d2 * ninv])
    }));
    let one = Self::constant(
      builder,
      [
        <F as PrimeCharacteristicRing>::ONE,
        <F as PrimeCharacteristicRing>::ZERO,
        <F as PrimeCharacteristicRing>::ZERO,
      ],
    );
    self.mul(builder, inv).assert_equal(builder, one);
    inv
  }

  pub fn exp_power_of_2<F: Field + multi_stark::traits::Field>(
    mut self,
    builder: &mut CircuitBuilder<F>,
    log_power: usize,
  ) -> Self {
    for _ in 0..log_power {
      self = self.mul(builder, self);
    }
    self
  }

  pub fn assert_equal<F: Field + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
    rhs: Self,
  ) {
    for (a, b) in self.0.into_iter().zip(rhs.0) {
      builder.assert_equal(a, b);
    }
  }
}
