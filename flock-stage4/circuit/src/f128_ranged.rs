//! Exact small-range carry encoding for radix-32 integer convolution.
//! A carry is one Fr wire constrained by a vanishing polynomial with exactly
//! the admitted small integer roots. This is not a lookup or witness hint.

use super::*;

#[derive(Clone, Copy)]
struct RangeWire {
  variable: Variable,
  value: Fr,
}

impl RangeWire {
  fn shifted(self, offset: Fr) -> LinearCombination {
    LinearCombination::from_variable(self.variable).term(Variable::ONE, offset)
  }
}

fn product(
  builder: &mut R1csBuilder,
  left: RangeWire,
  left_offset: Fr,
  right: RangeWire,
  right_offset: Fr,
  phase: ConstraintPhase,
) -> Result<RangeWire, R1csError> {
  let value = (left.value + left_offset) * (right.value + right_offset);
  let variable = builder.alloc_private(value)?;
  builder.enforce(
    phase,
    left.shifted(left_offset),
    right.shifted(right_offset),
    LinearCombination::from_variable(variable),
  );
  builder.check_status()?;
  Ok(RangeWire { variable, value })
}

fn zero_product(
  builder: &mut R1csBuilder,
  left: RangeWire,
  left_offset: Fr,
  right: RangeWire,
  right_offset: Fr,
  phase: ConstraintPhase,
) {
  builder.enforce(
    phase,
    left.shifted(left_offset),
    right.shifted(right_offset),
    LinearCombination::zero(),
  );
}

/// Enforce c in {0,...,maximum}, maximum<=8. With p=c(c-maximum), each
/// p+i(maximum-i)=(c-i)(c-(maximum-i)). A repeated middle root for even
/// maxima 4,6,8 changes multiplicity only, not the allowed field values.
fn constrain_small_range(
  builder: &mut R1csBuilder,
  carry: RangeWire,
  maximum: usize,
  phase: ConstraintPhase,
) -> Result<(), R1csError> {
  builder.check_status()?;
  if maximum > 8 {
    return Err(R1csError::InternalShape);
  }
  if maximum == 0 {
    builder.enforce_zero(phase, carry.shifted(Fr::ZERO));
  } else if maximum == 1 {
    builder.enforce_boolean(phase, carry.variable);
  } else {
    let p = product(
      builder,
      carry,
      Fr::ZERO,
      carry,
      -Fr::from(maximum as u64),
      phase,
    )?;
    match maximum {
      2 => zero_product(builder, p, Fr::ZERO, carry, -Fr::ONE, phase),
      3 => zero_product(builder, p, Fr::ZERO, p, Fr::from(2u64), phase),
      4 | 5 => {
        let (a, b) = if maximum == 4 { (3u64, 4u64) } else { (4, 6) };
        let q = product(builder, p, Fr::ZERO, p, Fr::from(a), phase)?;
        zero_product(builder, q, Fr::ZERO, p, Fr::from(b), phase);
      },
      6 | 7 => {
        let (a, b, c) =
          if maximum == 6 { (9u64, 5u64, 8u64) } else { (12, 6, 10) };
        let q = product(builder, p, Fr::ZERO, p, Fr::from(a), phase)?;
        let r = product(builder, p, Fr::from(b), p, Fr::from(c), phase)?;
        zero_product(builder, q, Fr::ZERO, r, Fr::ZERO, phase);
      },
      8 => {
        let q = product(builder, p, Fr::ZERO, p, Fr::from(16u64), phase)?;
        let r = product(builder, p, Fr::from(7u64), p, Fr::from(15u64), phase)?;
        let s = product(builder, r, Fr::ZERO, p, Fr::from(12u64), phase)?;
        zero_product(builder, q, Fr::ZERO, s, Fr::ZERO, phase);
      },
      _ => unreachable!("checked small carry range"),
    }
  }
  builder.check_status()
}

/// Replace each coefficient's binary carry digits with one bounded carry.
/// Every radix-32 digit is b+2*c, with Boolean b and 0<=c<=floor(N/2)<=8.
/// Thus each digit is at most 17<32. Both packed sides remain below 2^160
/// and Fr's modulus, so equality fixes the exact integer convolution and
/// every characteristic-two coefficient without modular or carry aliases.
pub(super) fn packed_polynomial_product_ranged(
  builder: &mut R1csBuilder,
  left: &[BitWire],
  right: &[BitWire],
  packed_left: Variable,
  packed_right: Variable,
  phase: ConstraintPhase,
) -> Result<Vec<BitWire>, R1csError> {
  builder.check_status()?;
  if left.is_empty()
    || left.len() != right.len()
    || left.len() > PACKED_PRODUCT_BITS
  {
    return Err(R1csError::InternalShape);
  }
  let mut terms = Vec::new();
  let mut output = Vec::with_capacity(2 * left.len() - 1);
  let mut place = Fr::ONE;
  for degree in 0..2 * left.len() - 1 {
    let start = degree.saturating_sub(left.len() - 1);
    let end = degree.min(left.len() - 1);
    let coefficient = (start..=end)
      .filter(|&i| left[i].value && right[degree - i].value)
      .count();
    let bit = alloc_checked_bit(builder, coefficient % 2 == 1, phase)?;
    terms.extend(bit.expression.terms().iter().map(|&(v, c)| (v, c * place)));
    output.push(bit);
    let product_terms = end - start + 1;
    let maximum = product_terms / 2;
    if maximum != 0 {
      let value = Fr::from((coefficient / 2) as u64);
      let variable = builder.alloc_private(value)?;
      constrain_small_range(
        builder,
        RangeWire { variable, value },
        maximum,
        phase,
      )?;
      terms.push((variable, place.double()));
    }
    place *= Fr::from(1u64 << PACKED_COEFFICIENT_BITS);
  }
  builder.enforce(
    phase,
    LinearCombination::from_variable(packed_left),
    LinearCombination::from_variable(packed_right),
    LinearCombination::from_terms(terms),
  );
  builder.check_status()?;
  Ok(output)
}

#[cfg(test)]
#[path = "f128_ranged_tests.rs"]
mod tests;
