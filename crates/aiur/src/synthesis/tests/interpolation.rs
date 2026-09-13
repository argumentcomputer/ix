// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Actual FRI row interpolation and both native matrix folding paths.

use multi_stark::{
  p3_field::{
    BasedVectorSpace, Field, HornerIter, PrimeCharacteristicRing, PrimeField64,
    TwoAdicField,
  },
  p3_matrix::dense::RowMajorMatrix,
  types::{ExtVal, Val},
};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_util::{reverse_bits_len, reverse_slice_index_bits};
use std::{io, marker::PhantomData};

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
  match variant {
    0 => vec![],
    1 => vec![sample(1)],
    2 => (0..arity)
      .map(|index| if index + 1 == arity { ExtVal::ONE } else { ExtVal::ZERO })
      .collect(),
    _ => (0..arity).map(|index| sample(index + 17)).collect(),
  }
}

fn fold_row(
  index: usize,
  height: usize,
  log_arity: usize,
  point: ExtVal,
  values: &[ExtVal],
) -> ExtVal {
  <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Val, ExtVal>>::fold_row(
    &TwoAdicFriFolding(PhantomData),
    index,
    height,
    log_arity,
    point,
    values.iter().copied(),
  )
}

#[test]
fn interpolation_snapshot() -> io::Result<()> {
  let mut out = b"Aiur FRI interpolation v1\n".to_vec();
  let mut rows = 0;
  let mut evaluations = 0;
  for parent in 0..=32 {
    for log_arity in 0..=parent.min(6) {
      let height = parent - log_arity;
      let arity = 1 << log_arity;
      let mask = if height == 0 {
        0
      } else {
        usize::MAX >> (usize::BITS as usize - height)
      };
      let mut indices = vec![0, mask / 2, mask];
      indices.sort_unstable();
      indices.dedup();
      nat(&mut out, indices.len());
      for index in indices {
        nat(&mut out, index);
        let start = Val::two_adic_generator(parent)
          .exp_u64(u64::try_from(reverse_bits_len(index, height)).unwrap());
        let mut nodes: Vec<_> = Val::two_adic_generator(log_arity)
          .shifted_powers(start)
          .take(arity)
          .collect();
        reverse_slice_index_bits(&mut nodes);
        let scale = (Val::from_usize(arity)
          * nodes[0].exp_power_of_2(log_arity))
        .inverse();
        field(&mut out, scale);
        for variant in 0..4 {
          let polynomial = coefficients(arity, variant);
          let values: Vec<ExtVal> = nodes
            .iter()
            .map(|&node| polynomial.iter().copied().horner(ExtVal::from(node)))
            .collect();
          extensions(&mut out, &polynomial);
          extensions(&mut out, &values);
          for point in [
            ExtVal::ZERO,
            ExtVal::from(Val::from_u64(7)),
            sample(41),
            ExtVal::from(nodes[0]),
            ExtVal::from(nodes[arity - 1]),
          ] {
            let result = fold_row(index, height, log_arity, point, &values);
            assert_eq!(result, polynomial.iter().copied().horner(point));
            extension(&mut out, point);
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
    // fold_matrix requires a positive arity logarithm in the accepted FRI
    // profile; the row helper above also tests its singleton boundary.
    for log_arity in 1..=parent.min(6) {
      let arity = 1 << log_arity;
      let height = parent - log_arity;
      let data: Vec<_> =
        (0..1 << parent).map(|index| sample(index + parent * 19)).collect();
      for point in [ExtVal::ZERO, sample(41), ExtVal::ONE] {
        let folded = <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<
          Val,
          ExtVal,
        >>::fold_matrix(
          &TwoAdicFriFolding(PhantomData),
          point,
          log_arity,
          RowMajorMatrix::new(data.clone(), arity),
        );
        assert_eq!(folded.len(), 1 << height);
        for (index, row) in data.chunks_exact(arity).enumerate() {
          assert_eq!(
            folded[index],
            fold_row(index, height, log_arity, point, row)
          );
          matrix_rows += 1;
        }
        extension(&mut out, point);
        extensions(&mut out, &data);
        extensions(&mut out, &folded);
        matrices += 1;
      }
    }
  }
  for count in [rows, evaluations, matrices, matrix_rows] {
    nat(&mut out, count);
  }
  if let Ok(path) = std::env::var("IX_INTERPOLATION_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  println!(
    "FRI interpolation: {rows} rows, {evaluations} challenge evaluations, {matrices} matrices, {matrix_rows} matrix rows"
  );
  Ok(())
}
