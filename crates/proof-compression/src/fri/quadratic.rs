use p3_field::Field;
use p3_field::extension::BinomiallyExtendable;

use multi_stark::plonkish::Bool;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;

/// Coordinates `a + b*X` in the configured quadratic extension, `X² = F::W`.
/// Arithmetic uses native base-field constraints, not foreign-field emulation.
#[derive(Clone, Copy, Debug)]
pub struct QuadraticValue(pub [Value; 2]);

impl QuadraticValue {
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
    coordinates: [F; 2],
  ) -> Self {
    Self(coordinates.map(|c| builder.constant(c)))
  }

  pub fn from_base<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    value: Value,
  ) -> Self {
    Self([
      value,
      builder.constant(<F as p3_field::PrimeCharacteristicRing>::ZERO),
    ])
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
    let zero = builder.constant(<F as p3_field::PrimeCharacteristicRing>::ZERO);
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

  pub fn mul<F: BinomiallyExtendable<2> + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
    rhs: Self,
  ) -> Self {
    let ac = builder.mul(self.0[0], rhs.0[0]);
    let bd = builder.mul(self.0[1], rhs.0[1]);
    let a_plus_b = builder.add(self.0[0], self.0[1]);
    let c_plus_d = builder.add(rhs.0[0], rhs.0[1]);
    let cross = builder.mul(a_plus_b, c_plus_d);
    let cross = builder.sub(cross, ac);
    let cross = builder.sub(cross, bd);
    let w = builder.constant(F::W);
    let w_bd = builder.mul(w, bd);
    Self([builder.add(ac, w_bd), cross])
  }

  /// Constrained inverse through the norm: `(a - bX)/(a² - W*b²)`.
  /// The base inverse relation rejects zero, including malicious hints.
  pub fn inverse<F: BinomiallyExtendable<2> + multi_stark::traits::Field>(
    self,
    builder: &mut CircuitBuilder<F>,
  ) -> Self {
    let aa = builder.mul(self.0[0], self.0[0]);
    let bb = builder.mul(self.0[1], self.0[1]);
    let w = builder.constant(F::W);
    let w_bb = builder.mul(w, bb);
    let norm = builder.sub(aa, w_bb);
    let inv_norm = builder.inverse(norm);
    let real = builder.mul(self.0[0], inv_norm);
    let imag = builder.mul(self.0[1], inv_norm);
    let zero = builder.constant(<F as p3_field::PrimeCharacteristicRing>::ZERO);
    Self([real, builder.sub(zero, imag)])
  }

  pub fn exp_power_of_2<
    F: BinomiallyExtendable<2> + multi_stark::traits::Field,
  >(
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
