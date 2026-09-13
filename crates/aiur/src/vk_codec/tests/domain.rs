// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The actual pinned polynomial-space selectors, at all supported domain
//! sizes and on complete small cosets. Large domains are never enumerated.

use super::*;
use multi_stark::{
  p3_field::{
    BasedVectorSpace, Field, TwoAdicField, coset::TwoAdicMultiplicativeCoset,
  },
  types::ExtVal,
};
use p3_commit::PolynomialSpace;
use std::io;

fn nat(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn field(out: &mut Vec<u8>, value: Val) {
  out.extend(value.as_canonical_u64().to_le_bytes());
}

fn extension(out: &mut Vec<u8>, value: ExtVal) {
  for &coordinate in value.as_basis_coefficients_slice() {
    field(out, coordinate);
  }
}

fn selector_values(
  out: &mut Vec<u8>,
  values: &p3_commit::LagrangeSelectors<ExtVal>,
) {
  extension(out, values.is_first_row);
  extension(out, values.is_last_row);
  extension(out, values.is_transition);
  extension(out, values.inv_vanishing);
}

fn challenges(last: Val) -> Vec<ExtVal> {
  let mut values: Vec<_> = [
    Val::ZERO,
    Val::ONE,
    Val::NEG_ONE,
    last,
    Val::from_u64(7),
    Val::from_u64(1 << 32),
    Val::from_u64(1 << 63),
    Val::from_u64(Val::ORDER_U64 - 2),
  ]
  .into_iter()
  .map(ExtVal::from)
  .collect();
  let mut state = 0x04c9_bd65_a678_10fb_u64;
  let mut next = || {
    state ^= state << 13;
    state ^= state >> 7;
    state ^= state << 17;
    Val::from_u64(state)
  };
  for _ in 0..56 {
    values.push(ExtVal::new([next(), next()]));
  }
  values
}

#[test]
fn domain_snapshot() -> io::Result<()> {
  let mut out = b"Aiur trace domains v1\n".to_vec();
  assert_eq!(Val::TWO_ADICITY, 32);
  nat(&mut out, 33);
  for bits in 0..=32 {
    let domain =
      TwoAdicMultiplicativeCoset::<Val>::new(Val::ONE, bits).unwrap();
    let n = domain.size();
    let generator = domain.subgroup_generator();
    let last = generator.inverse();
    let normalizer = Val::from_usize(n) * generator;
    nat(&mut out, bits);
    nat(&mut out, n);
    field(&mut out, generator);
    field(&mut out, last);
    field(&mut out, normalizer);
    field(&mut out, normalizer.inverse());
    assert_eq!(domain.first_point(), Val::ONE);
    assert_eq!(generator.exp_power_of_2(bits), Val::ONE);
    if bits > 0 {
      assert_eq!(generator.exp_power_of_2(bits - 1), Val::NEG_ONE);
    }
    let mut indices: Vec<_> = (0..n.min(16)).collect();
    indices.extend([n / 2, n - 1, n.saturating_sub(2)]);
    for seed in 0..16_usize {
      indices.push(seed.wrapping_mul(0x0a37_51c9) % n);
    }
    indices.sort_unstable();
    indices.dedup();
    nat(&mut out, indices.len());
    for index in indices {
      let point = generator.exp_u64(u64::try_from(index).unwrap());
      let next = domain.next_point(ExtVal::from(point)).unwrap();
      nat(&mut out, index);
      field(&mut out, point);
      extension(&mut out, next);
      assert_eq!(next, ExtVal::from(point * generator));
      assert_eq!(
        next,
        ExtVal::from(
          generator.exp_u64(u64::try_from((index + 1) % n).unwrap())
        )
      );
      assert_eq!(
        domain.vanishing_poly_at_point(ExtVal::from(point)),
        ExtVal::ZERO
      );
    }
    let points = challenges(last);
    nat(&mut out, points.len());
    for point in points {
      let vanishing = domain.vanishing_poly_at_point(point);
      extension(&mut out, point);
      extension(&mut out, vanishing);
      out.push(u8::from(vanishing != ExtVal::ZERO));
      if vanishing != ExtVal::ZERO {
        selector_values(&mut out, &domain.selectors_at_point(point));
      }
    }
  }
  // Each complete coset is disjoint from the trace domain. The bulk native
  // algorithm and the single-point native algorithm must agree at every point.
  nat(&mut out, 9);
  for bits in 0..9 {
    let domain =
      TwoAdicMultiplicativeCoset::<Val>::new(Val::ONE, bits).unwrap();
    let coset =
      TwoAdicMultiplicativeCoset::<Val>::new(Val::GENERATOR, bits).unwrap();
    let bulk = domain.selectors_on_coset(coset);
    nat(&mut out, bits);
    nat(&mut out, coset.size());
    for (index, point) in coset.iter().enumerate() {
      let single = domain.selectors_at_point(ExtVal::from(point));
      assert_eq!(single.is_first_row, ExtVal::from(bulk.is_first_row[index]));
      assert_eq!(single.is_last_row, ExtVal::from(bulk.is_last_row[index]));
      assert_eq!(single.is_transition, ExtVal::from(bulk.is_transition[index]));
      assert_eq!(single.inv_vanishing, ExtVal::from(bulk.inv_vanishing[index]));
      field(&mut out, point);
      selector_values(&mut out, &single);
    }
  }
  for invalid in [33, 64, 255, 256, usize::MAX] {
    assert!(
      TwoAdicMultiplicativeCoset::<Val>::new(Val::ONE, invalid).is_none()
    );
  }
  if let Some(path) = std::env::var_os("IX_DOMAIN_SNAPSHOT") {
    std::fs::write(path, &out)?;
  }
  Ok(())
}

fn extensions(out: &mut Vec<u8>, values: &[ExtVal]) {
  nat(out, values.len());
  for &value in values {
    extension(out, value);
  }
}

// This reproduces the verifier's private recombination helper with native
// basis elements, power iterator and field operations. Domain selector calls
// above and below invoke PolynomialSpace's actual implementation directly.
fn quotient_value(point: ExtVal, bits: usize, row: &[ExtVal]) -> ExtVal {
  row
    .as_chunks::<2>()
    .0
    .iter()
    .zip(point.exp_power_of_2(bits).powers())
    .map(|(chunk, power)| {
      let coefficient = chunk
        .iter()
        .enumerate()
        .map(|(index, value)| {
          *value
            * <ExtVal as BasedVectorSpace<Val>>::ith_basis_element(index)
              .unwrap()
        })
        .sum::<ExtVal>();
      power * coefficient
    })
    .sum()
}

#[test]
fn quotient_snapshot() -> io::Result<()> {
  let mut out = b"Aiur quotient arithmetic v1\n".to_vec();
  let logs = [0, 1, 2, 4, 8, 16, 31, 32];
  let counts = [0, 1, 2, 3, 4, 7, 8, 9, 16, 31, 32];
  let values = challenges(Val::from_u64(17));
  nat(&mut out, logs.len() * counts.len() * 8);
  for bits in logs {
    let domain =
      TwoAdicMultiplicativeCoset::<Val>::new(Val::ONE, bits).unwrap();
    for count in counts {
      for seed in 0..8 {
        let point = values[8 + seed];
        let alpha = values[seed];
        let constraints: Vec<_> = (0..count)
          .map(|index| values[(index * 7 + seed) % values.len()])
          .collect();
        let composition = constraints
          .iter()
          .fold(ExtVal::ZERO, |acc, &value| acc * alpha + value);
        let mut row: Vec<_> = (0..2 * count)
          .map(|index| values[(index * 11 + seed + 13) % values.len()])
          .collect();
        let selectors = domain.selectors_at_point(point);
        let expected = composition * selectors.inv_vanishing;
        if seed % 2 == 0 && count != 0 {
          let error = expected - quotient_value(point, bits, &row);
          row[0] += error;
        }
        let quotient = quotient_value(point, bits, &row);
        let accepted = expected == quotient;
        if seed % 2 == 0 || count == 0 {
          assert!(accepted);
        } else {
          assert!(!accepted);
        }
        nat(&mut out, bits);
        nat(&mut out, count);
        nat(&mut out, seed);
        extension(&mut out, point);
        extension(&mut out, alpha);
        extensions(&mut out, &constraints);
        extensions(&mut out, &row);
        extension(&mut out, composition);
        extension(&mut out, quotient);
        out.push(u8::from(accepted));
        if accepted && !row.is_empty() {
          row[0] += ExtVal::ONE;
          assert_ne!(expected, quotient_value(point, bits, &row));
        }
      }
    }
  }
  if let Some(path) = std::env::var_os("IX_QUOTIENT_SNAPSHOT") {
    std::fs::write(path, &out)?;
  }
  Ok(())
}
