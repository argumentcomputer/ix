// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Native FRI folds of global polynomials spanning several coefficient blocks.

use multi_stark::{
  p3_field::{
    BasedVectorSpace, HornerIter, PrimeCharacteristicRing, PrimeField64,
    TwoAdicField,
  },
  p3_matrix::dense::RowMajorMatrix,
  types::{ExtVal, Val},
};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_util::reverse_bits_len;
use std::{io, marker::PhantomData};

fn nat(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn extension(out: &mut Vec<u8>, value: ExtVal) {
  let coordinates: &[Val] = value.as_basis_coefficients_slice();
  for &coordinate in coordinates {
    out.extend(coordinate.as_canonical_u64().to_le_bytes());
  }
}

fn extensions(out: &mut Vec<u8>, values: &[ExtVal]) {
  nat(out, values.len());
  for &value in values {
    extension(out, value);
  }
}

fn sample(seed: usize) -> ExtVal {
  ExtVal::new([Val::from_usize(seed * 67 + 3), Val::from_usize(seed * 13 + 1)])
}

fn coefficients(arity: usize, variant: usize) -> Vec<ExtVal> {
  let length = match variant {
    0 => 0,
    1 => 1,
    2 => arity - 1,
    3 => arity,
    4 => arity + 1,
    5 => 2 * arity + 1,
    6 => 3 * arity,
    _ => 3 * arity + 2,
  };
  (0..length)
    .map(|index| match variant {
      6 => {
        if index + 1 == length {
          ExtVal::ONE
        } else {
          ExtVal::ZERO
        }
      },
      7 if index > arity => ExtVal::ZERO,
      _ => sample(index + 17),
    })
    .collect()
}

fn query_point(bits: usize, index: usize) -> ExtVal {
  Val::two_adic_generator(bits)
    .exp_u64(u64::try_from(reverse_bits_len(index, bits)).unwrap())
    .into()
}

fn nodes(parent: usize, log_arity: usize, index: usize) -> Vec<ExtVal> {
  (0..1 << log_arity)
    .map(|slot| query_point(parent, (index << log_arity) + slot))
    .collect()
}

fn fold_row(
  index: usize,
  height: usize,
  log_arity: usize,
  challenge: ExtVal,
  values: &[ExtVal],
) -> ExtVal {
  <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Val, ExtVal>>::fold_row(
    &TwoAdicFriFolding(PhantomData),
    index,
    height,
    log_arity,
    challenge,
    values.iter().copied(),
  )
}

fn folded_coefficients(
  coefficients: &[ExtVal],
  arity: usize,
  challenge: ExtVal,
) -> Vec<ExtVal> {
  coefficients
    .chunks(arity)
    .map(|block| block.iter().copied().horner(challenge))
    .collect()
}

#[test]
fn folding_snapshot() -> io::Result<()> {
  let mut out = b"Aiur global FRI folding v1\n".to_vec();
  let mut rows = 0;
  let mut evaluations = 0;
  for parent in 0..=32 {
    for log_arity in 0..=parent.min(6) {
      let height = parent - log_arity;
      let arity = 1 << log_arity;
      let mask = (1_usize << height) - 1;
      let mut indices = vec![0, mask / 2, mask];
      indices.sort_unstable();
      indices.dedup();
      nat(&mut out, indices.len());
      for index in indices {
        nat(&mut out, index);
        let nodes = nodes(parent, log_arity, index);
        for variant in 0..8 {
          let polynomial = coefficients(arity, variant);
          let values: Vec<_> = nodes
            .iter()
            .map(|&node| polynomial.iter().copied().horner(node))
            .collect();
          extensions(&mut out, &polynomial);
          extensions(&mut out, &values);
          for challenge in
            [ExtVal::ZERO, sample(41), ExtVal::ONE, nodes[0], nodes[arity - 1]]
          {
            let folded = folded_coefficients(&polynomial, arity, challenge);
            let result = fold_row(index, height, log_arity, challenge, &values);
            assert_eq!(
              result,
              folded.iter().copied().horner(query_point(height, index))
            );
            extension(&mut out, challenge);
            extensions(&mut out, &folded);
            extension(&mut out, result);
            evaluations += 1;
          }
          rows += 1;
        }
      }
    }
  }
  let mut matrices = 0;
  let mut matrix_rows = 0;
  for parent in 1..=9 {
    for log_arity in 1..=parent.min(6) {
      let arity = 1 << log_arity;
      let height = parent - log_arity;
      for variant in 0..8 {
        let polynomial = coefficients(arity, variant);
        let data: Vec<_> = (0..1 << parent)
          .map(|index| {
            polynomial.iter().copied().horner(query_point(parent, index))
          })
          .collect();
        extensions(&mut out, &polynomial);
        extensions(&mut out, &data);
        for challenge in [ExtVal::ZERO, sample(41), ExtVal::ONE] {
          let folded = folded_coefficients(&polynomial, arity, challenge);
          let result = <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<
            Val,
            ExtVal,
          >>::fold_matrix(
            &TwoAdicFriFolding(PhantomData),
            challenge,
            log_arity,
            RowMajorMatrix::new(data.clone(), arity),
          );
          assert_eq!(result.len(), 1 << height);
          for (index, &value) in result.iter().enumerate() {
            assert_eq!(
              value,
              folded.iter().copied().horner(query_point(height, index))
            );
            matrix_rows += 1;
          }
          extension(&mut out, challenge);
          extensions(&mut out, &folded);
          extensions(&mut out, &result);
          matrices += 1;
        }
      }
    }
  }
  let mut pairs = 0;
  let mut pair_evaluations = 0;
  for log_arity in 0..=6 {
    let arity = 1 << log_arity;
    let parent = log_arity + 2;
    let mut challenges = nodes(parent, log_arity, 1);
    challenges.extend([ExtVal::ZERO, sample(41)]);
    let left: Vec<_> = (0..arity).map(|index| sample(index + 7)).collect();
    let mut right = left.clone();
    right[arity / 2] += sample(131);
    extensions(&mut out, &left);
    extensions(&mut out, &right);
    let mut agreements = 0;
    for challenge in challenges {
      let first = fold_row(1, 2, log_arity, challenge, &left);
      let second = fold_row(1, 2, log_arity, challenge, &right);
      agreements += usize::from(first == second);
      extension(&mut out, challenge);
      extension(&mut out, first);
      extension(&mut out, second);
      pair_evaluations += 1;
    }
    assert_eq!(agreements, arity - 1);
    nat(&mut out, agreements);
    pairs += 1;
  }
  for count in
    [rows, evaluations, matrices, matrix_rows, pairs, pair_evaluations]
  {
    nat(&mut out, count);
  }
  if let Ok(path) = std::env::var("IX_FOLDING_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  println!(
    "Global FRI folding: {rows} rows, {evaluations} evaluations, {matrices} matrices, {matrix_rows} matrix rows, {pairs} distinct row pairs, {pair_evaluations} pair evaluations"
  );
  Ok(())
}
