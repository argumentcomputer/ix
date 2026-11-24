//! The crate evaluation domain over [`CurveScalar`]: a multiplicative coset
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

use super::{
  curve::{Bn254, KzgCurve},
  field::CurveScalar,
};

/// A coset `shift · H`, `|H| = 2^log_size`, over a KZG curve's scalar field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Radix2Coset<C: KzgCurve = Bn254> {
  pub log_size: usize,
  pub shift: CurveScalar<C>,
}

impl<C: KzgCurve> Radix2Coset<C> {
  /// The subgroup generator `g`.
  #[inline]
  pub fn generator(&self) -> CurveScalar<C> {
    CurveScalar::<C>::two_adic_generator(self.log_size)
  }

  /// The coset's points in natural order: `shift · g^i`.
  pub fn points(&self) -> Vec<CurveScalar<C>> {
    self
      .generator()
      .powers()
      .take(self.size())
      .map(|x| x * self.shift)
      .collect()
  }
}

impl<C: KzgCurve> EvaluationDomain for Radix2Coset<C> {
  type F = CurveScalar<C>;
  type Challenge = CurveScalar<C>;

  #[inline]
  fn size(&self) -> usize {
    assert!(
      self.log_size <= CurveScalar::<C>::TWO_ADICITY,
      "domain exceeds scalar two-adicity"
    );
    1 << self.log_size
  }

  #[inline]
  fn first_point(&self) -> CurveScalar<C> {
    self.shift
  }

  #[inline]
  fn next_point(&self, x: CurveScalar<C>) -> CurveScalar<C> {
    x * self.generator()
  }

  fn create_disjoint_domain(&self, min_size: usize) -> Self {
    let log_size = p3_util::log2_ceil_usize(min_size);
    assert!(
      log_size <= CurveScalar::<C>::TWO_ADICITY,
      "domain exceeds scalar two-adicity"
    );
    // Multiplying the shift by the field's multiplicative generator
    // leaves the subgroup (and every subgroup coset reachable by
    // repeated application), exactly as in p3.
    Self { log_size, shift: self.shift * CurveScalar(C::FR_GENERATOR) }
  }

  fn selectors_at_point(
    &self,
    point: CurveScalar<C>,
  ) -> LagrangeSelectors<CurveScalar<C>> {
    let one = <CurveScalar<C> as Algebra<CurveScalar<C>>>::ONE;
    let unshifted = point * self.shift.inverse();
    let z_h = unshifted.exp_power_of_2(self.log_size) - one;
    let g_inv = self.generator().inverse();
    LagrangeSelectors {
      is_first_row: z_h * (unshifted - one).inverse(),
      is_last_row: z_h * (unshifted - g_inv).inverse(),
      is_transition: unshifted - g_inv,
      inv_vanishing: z_h.inverse(),
    }
  }

  fn selectors_on_coset(
    &self,
    coset: Self,
  ) -> LagrangeSelectors<Vec<CurveScalar<C>>> {
    let one = <CurveScalar<C> as Algebra<CurveScalar<C>>>::ONE;
    assert_eq!(self.shift, one, "selectors_on_coset needs the group itself");
    assert_ne!(coset.shift, one, "coset must be disjoint from the group");
    assert!(coset.log_size >= self.log_size);
    let rate_bits = coset.log_size - self.log_size;

    // Z_H(X) = X^n − 1 is periodic over the coset with period
    // 2^rate_bits: (s·w^j·h)^n = s^n·w^{jn} and h^n = 1.
    let s_pow_n = coset.shift.exp_power_of_2(self.log_size);
    let vanishing: Vec<CurveScalar<C>> =
      CurveScalar::<C>::two_adic_generator(rate_bits)
        .powers()
        .take(1 << rate_bits)
        .map(|x| s_pow_n * x - one)
        .collect();

    let xs = coset.points();
    let single_point_selector = |i: u64| {
      let subgroup_point = self.generator().exp_u64(i);
      let denoms: Vec<CurveScalar<C>> =
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
  use crate::kzg::curve::Bls12381;

  fn check_domain_suite<C: KzgCurve>() {
    let one = <CurveScalar<C> as Algebra<CurveScalar<C>>>::ONE;
    for log_size in [0usize, 1, 3] {
      for extra_bits in [0usize, 1, 2] {
        let trace = Radix2Coset::<C> { log_size, shift: one };
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

    let trace = Radix2Coset::<C> { log_size: 4, shift: one };
    let coset = trace.create_disjoint_domain(1 << 6);
    for x in coset.points() {
      assert!(!(x.exp_power_of_2(4) - one).is_zero());
    }

    let domain = Radix2Coset::<C> { log_size: 3, shift: one };
    let points = domain.points();
    for i in 0..points.len() - 1 {
      assert_eq!(domain.next_point(points[i]), points[i + 1]);
    }

    let max =
      Radix2Coset::<C> { log_size: CurveScalar::<C>::TWO_ADICITY, shift: one };
    assert_eq!(max.size(), 1usize << CurveScalar::<C>::TWO_ADICITY);
    assert_eq!(
      max.generator().exp_power_of_2(CurveScalar::<C>::TWO_ADICITY),
      one
    );
    let max_coset = max.create_disjoint_domain(max.size());
    assert_ne!(
      max_coset.shift.exp_power_of_2(CurveScalar::<C>::TWO_ADICITY),
      one
    );
  }

  #[test]
  fn domain_properties_hold_for_both_curves() {
    check_domain_suite::<Bn254>();
    check_domain_suite::<Bls12381>();
  }

  #[test]
  #[should_panic(expected = "domain exceeds scalar two-adicity")]
  fn disjoint_domain_rejects_oversized_quotient() {
    let one = <CurveScalar<Bn254> as Algebra<CurveScalar<Bn254>>>::ONE;
    let trace = Radix2Coset::<Bn254> {
      log_size: CurveScalar::<Bn254>::TWO_ADICITY,
      shift: one,
    };
    trace.create_disjoint_domain(trace.size() + 1);
  }

  #[test]
  #[should_panic(expected = "domain exceeds scalar two-adicity")]
  fn rejects_oversized_domain() {
    let one = <CurveScalar<Bls12381> as Algebra<CurveScalar<Bls12381>>>::ONE;
    Radix2Coset::<Bls12381> {
      log_size: CurveScalar::<Bls12381>::TWO_ADICITY + 1,
      shift: one,
    }
    .size();
  }
}
