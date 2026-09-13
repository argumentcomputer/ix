// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Native final-polynomial Horner evaluation and upstream coefficient helpers.

use multi_stark::{
  p3_field::{
    BasedVectorSpace, Field, HornerIter, PrimeCharacteristicRing, PrimeField64,
  },
  types::{ExtVal, Val},
};
use p3_stir::utils::{
  add_polys, divide_by_linear, eval_poly, vanishing_poly_from_roots,
};
use std::io;

fn nat(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn field(out: &mut Vec<u8>, value: Val) {
  out.extend(value.as_canonical_u64().to_le_bytes());
}

fn extension(out: &mut Vec<u8>, value: ExtVal) {
  let coordinates: &[Val] = value.as_basis_coefficients_slice();
  for &coordinate in coordinates {
    field(out, coordinate);
  }
}

fn values<F: Copy>(
  out: &mut Vec<u8>,
  values: &[F],
  write: fn(&mut Vec<u8>, F),
) {
  nat(out, values.len());
  for &value in values {
    write(out, value);
  }
}

fn base_sample(seed: usize) -> Val {
  if seed == 2 { Val::NEG_ONE } else { Val::from_usize(seed) }
}

fn extension_sample(seed: usize) -> ExtVal {
  if seed < 3 {
    ExtVal::from(base_sample(seed))
  } else {
    ExtVal::new([Val::from_usize(seed * 67), Val::from_usize(seed + 1)])
  }
}

fn coefficients<F: Field>(
  length: usize,
  seed: usize,
  sample: fn(usize) -> F,
) -> Vec<F> {
  (0..length)
    .map(|index| match seed {
      0 => F::ZERO,
      1 => {
        if index + 1 == length {
          F::ONE
        } else {
          F::ZERO
        }
      },
      2 if index >= length / 2 => F::ZERO,
      _ => sample(seed * 67 + index * 13 + 3),
    })
    .collect()
}

fn cases<F: Field>(
  out: &mut Vec<u8>,
  sample: fn(usize) -> F,
  write: fn(&mut Vec<u8>, F),
) -> [usize; 5] {
  let domain: Vec<_> = (0..80).map(sample).collect();
  for (index, value) in domain.iter().enumerate() {
    assert!(!domain[..index].contains(value));
  }
  values(out, &domain, write);
  let mut count = 0;
  let mut divisions = 0;
  let mut zero_cases = 0;
  let mut root_sets = 0;
  let mut repeated_sets = 0;
  for length in [0, 1, 2, 3, 4, 7, 8, 9, 16, 31, 32, 65] {
    for right_length in [0, 1, length, length + 3] {
      for seed in 0..8 {
        let left = coefficients(length, seed, sample);
        let right = coefficients(right_length, seed, sample);
        let root = sample(seed);
        let point = if seed % 3 == 0 { root } else { sample(seed + 19) };
        values(out, &left, write);
        values(out, &right, write);
        write(out, root);
        write(out, point);
        let at_point: F = left.iter().copied().horner(point);
        let at_root: F = left.iter().copied().horner(root);
        let right_value: F = right.iter().copied().horner(point);
        assert_eq!(at_point, eval_poly(&left, point));
        assert_eq!(at_root, eval_poly(&left, root));
        assert_eq!(right_value, eval_poly(&right, point));
        write(out, at_point);
        write(out, at_root);
        write(out, right_value);
        let added = add_polys(&left, &right);
        let difference = add_polys(
          &left,
          &right.iter().map(|&value| -value).collect::<Vec<_>>(),
        );
        values(out, &added, write);
        values(out, &difference, write);
        assert_eq!(eval_poly(&added, point), at_point + right_value);
        assert_eq!(eval_poly(&difference, point), at_point - right_value);
        if !left.is_empty() {
          let (quotient, remainder) = divide_by_linear(&left, root);
          assert_eq!(quotient.len(), left.len() - 1);
          assert_eq!(remainder, at_root);
          assert_eq!(
            (point - root) * eval_poly(&quotient, point) + remainder,
            at_point
          );
          values(out, &quotient, write);
          write(out, remainder);
          divisions += 1;
        }
        let roots = domain
          .iter()
          .filter(|&&value| eval_poly(&left, value).is_zero())
          .count();
        let agreements = domain
          .iter()
          .filter(|&&value| eval_poly(&difference, value).is_zero())
          .count();
        let zero = left.iter().all(|value| value.is_zero());
        if zero {
          zero_cases += 1;
        } else {
          assert!(roots < left.len());
        }
        if difference.iter().any(|value| !value.is_zero()) {
          assert!(agreements < left.len().max(right.len()));
        }
        nat(out, roots);
        nat(out, agreements);
        count += 1;
      }
    }
  }
  for length in [0, 1, 2, 3, 7, 16, 31, 32, 63] {
    for variant in 0..4 {
      let roots: Vec<_> = (0..length)
        .map(|index| {
          sample(match variant {
            0 => index,
            1 => length - index - 1,
            2 => 0,
            _ => index / 2,
          })
        })
        .collect();
      let repeated = roots
        .iter()
        .enumerate()
        .any(|(index, value)| roots[..index].contains(value));
      let polynomial = vanishing_poly_from_roots(&roots);
      assert_eq!(polynomial.len(), roots.len() + 1);
      assert_eq!(polynomial.last(), Some(&F::ONE));
      values(out, &roots, write);
      values(out, &polynomial, write);
      for point in [sample(0), sample(2), sample(17), sample(79)] {
        assert_eq!(
          eval_poly(&polynomial, point),
          roots.iter().map(|&root| point - root).product()
        );
        write(out, eval_poly(&polynomial, point));
      }
      let count = domain
        .iter()
        .filter(|&&point| eval_poly(&polynomial, point).is_zero())
        .count();
      assert!(count <= roots.len());
      if !repeated {
        assert_eq!(count, roots.len());
      }
      nat(out, count);
      root_sets += 1;
      repeated_sets += usize::from(repeated);
    }
  }
  [count, divisions, zero_cases, root_sets, repeated_sets]
}

#[test]
fn polynomial_snapshot() -> io::Result<()> {
  let mut out = b"Aiur coefficient polynomials v1\n".to_vec();
  let base = cases(&mut out, base_sample, field);
  let extension = cases(&mut out, extension_sample, extension);
  for count in base.into_iter().chain(extension) {
    nat(&mut out, count);
  }
  if let Ok(path) = std::env::var("IX_POLYNOMIAL_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  println!(
    "Native polynomial arithmetic/divisions/zero cases/root sets/repeated sets: base {base:?}, extension {extension:?}"
  );
  Ok(())
}
