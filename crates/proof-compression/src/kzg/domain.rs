//! The crate evaluation domain over [`Scalar`]: a multiplicative coset
//! `shift · H` of the order-`2^log_size` subgroup `H`.
//!
//! The selector formulas reproduce the p3 coset semantics the core's
//! constraint math was written against (unnormalized selectors; the
//! logUp boundary injection pre-absorbs the `n·g` normalization):
//! with `s` the shift, `g` the subgroup generator, and `u = X/s`,
//!
//! - vanishing:      `Z(X) = u^n − 1`
//! - first row:      `Z(X)/(u − 1)`
//! - last row:       `Z(X)/(u − g⁻¹)`
//! - transition:     `u − g⁻¹`

use multi_stark::traits::Algebra;
use multi_stark::traits::EvaluationDomain;
use multi_stark::traits::Field;
use multi_stark::traits::LagrangeSelectors;
use multi_stark::traits::TwoAdicField;
use multi_stark::traits::batch_inverse;

use super::field::Scalar;

const ONE: Scalar = <Scalar as Algebra<Scalar>>::ONE;

/// A coset `shift · H`, `|H| = 2^log_size`, over the BLS12-381 scalar
/// field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Radix2Coset {
  pub log_size: usize,
  pub shift: Scalar,
}

impl Radix2Coset {
  /// The subgroup generator `g`.
  #[inline]
  pub fn generator(&self) -> Scalar {
    Scalar::two_adic_generator(self.log_size)
  }

  /// The coset's points in natural order: `shift · g^i`.
  pub fn points(&self) -> Vec<Scalar> {
    self
      .generator()
      .powers()
      .take(self.size())
      .map(|x| x * self.shift)
      .collect()
  }
}

impl EvaluationDomain for Radix2Coset {
  type F = Scalar;
  type Challenge = Scalar;

  #[inline]
  fn size(&self) -> usize {
    1 << self.log_size
  }

  #[inline]
  fn first_point(&self) -> Scalar {
    self.shift
  }

  #[inline]
  fn next_point(&self, x: Scalar) -> Scalar {
    x * self.generator()
  }

  fn create_disjoint_domain(&self, min_size: usize) -> Self {
    // Multiplying the shift by the field's multiplicative generator
    // leaves the subgroup (and every subgroup coset reachable by
    // repeated application), exactly as in p3.
    Self {
      log_size: p3_util::log2_ceil_usize(min_size),
      shift: self.shift
        * Scalar(<ark_bls12_381::Fr as ark_ff::FftField>::GENERATOR),
    }
  }

  fn selectors_at_point(&self, point: Scalar) -> LagrangeSelectors<Scalar> {
    let unshifted = point * self.shift.inverse();
    let z_h = unshifted.exp_power_of_2(self.log_size) - ONE;
    let g_inv = self.generator().inverse();
    LagrangeSelectors {
      is_first_row: z_h * (unshifted - ONE).inverse(),
      is_last_row: z_h * (unshifted - g_inv).inverse(),
      is_transition: unshifted - g_inv,
      inv_vanishing: z_h.inverse(),
    }
  }

  fn selectors_on_coset(&self, coset: Self) -> LagrangeSelectors<Vec<Scalar>> {
    assert_eq!(self.shift, ONE, "selectors_on_coset needs the group itself");
    assert_ne!(coset.shift, ONE, "coset must be disjoint from the group");
    assert!(coset.log_size >= self.log_size);
    let rate_bits = coset.log_size - self.log_size;

    // Z_H(X) = X^n − 1 is periodic over the coset with period
    // 2^rate_bits: (s·w^j·h)^n = s^n·w^{jn} and h^n = 1.
    let s_pow_n = coset.shift.exp_power_of_2(self.log_size);
    let vanishing: Vec<Scalar> = Scalar::two_adic_generator(rate_bits)
      .powers()
      .take(1 << rate_bits)
      .map(|x| s_pow_n * x - ONE)
      .collect();

    let xs = coset.points();
    let single_point_selector = |i: u64| {
      let subgroup_point = self.generator().exp_u64(i);
      let denoms: Vec<Scalar> =
        xs.iter().map(|&x| x - subgroup_point).collect();
      let inverses = batch_inverse(&denoms);
      vanishing
        .iter()
        .cycle()
        .zip(inverses)
        .map(|(&z_h, inv)| z_h * inv)
        .collect()
    };

    let subgroup_last = self.generator().inverse();
    LagrangeSelectors {
      is_first_row: single_point_selector(0),
      is_last_row: single_point_selector(self.size() as u64 - 1),
      is_transition: xs.into_iter().map(|x| x - subgroup_last).collect(),
      inv_vanishing: batch_inverse(&vanishing)
        .into_iter()
        .cycle()
        .take(coset.size())
        .collect(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// `selectors_on_coset` must agree pointwise with `selectors_at_point`
  /// evaluated at each coset point.
  #[test]
  fn coset_selectors_match_pointwise() {
    for log_size in [0usize, 1, 3] {
      for extra_bits in [0usize, 1, 2] {
        let trace = Radix2Coset { log_size, shift: ONE };
        let coset = trace.create_disjoint_domain(1 << (log_size + extra_bits));
        let on_coset = trace.selectors_on_coset(coset);
        for (i, x) in coset.points().into_iter().enumerate() {
          let at_point = trace.selectors_at_point(x);
          assert_eq!(on_coset.is_first_row[i], at_point.is_first_row);
          assert_eq!(on_coset.is_last_row[i], at_point.is_last_row);
          assert_eq!(on_coset.is_transition[i], at_point.is_transition);
          assert_eq!(on_coset.inv_vanishing[i], at_point.inv_vanishing);
        }
      }
    }
  }

  /// The disjoint domain must be disjoint: the vanishing polynomial of
  /// the trace domain is nonzero on every coset point.
  #[test]
  fn disjoint_domain_is_disjoint() {
    let trace = Radix2Coset { log_size: 4, shift: ONE };
    let coset = trace.create_disjoint_domain(1 << 6);
    for x in coset.points() {
      assert!(!(x.exp_power_of_2(4) - ONE).is_zero());
    }
  }

  #[test]
  fn next_point_walks_the_domain() {
    let domain = Radix2Coset { log_size: 3, shift: ONE };
    let points = domain.points();
    for i in 0..points.len() - 1 {
      assert_eq!(domain.next_point(points[i]), points[i + 1]);
    }
  }
}
