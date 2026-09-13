// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Native bit reversal, FRI interpolation node selection and domain reduction.

use multi_stark::{
  p3_field::{
    BasedVectorSpace, PrimeCharacteristicRing, PrimeField64, TwoAdicField,
  },
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

fn samples(bits: usize, exhaustive: usize) -> Vec<usize> {
  let mask =
    if bits == 0 { 0 } else { usize::MAX >> (usize::BITS as usize - bits) };
  let mut indices: Vec<_> = (0..=mask.min(exhaustive - 1)).collect();
  indices.extend([mask, mask / 2, mask.saturating_sub(1)]);
  for seed in 0..16_usize {
    indices.push(seed.wrapping_mul(0x0a37_51c9) & mask);
  }
  indices.sort_unstable();
  indices.dedup();
  indices
}

#[test]
fn fri_domain_snapshot() -> io::Result<()> {
  let mut out = b"Aiur FRI domains v1\n".to_vec();
  let word_bits = usize::BITS as usize;
  assert!(word_bits == 32 || word_bits == 64);
  nat(&mut out, word_bits);
  let mut reversals = 0;
  for bits in 0..=word_bits {
    let indices = samples(bits, 1024);
    nat(&mut out, indices.len());
    for index in indices {
      let reversed = reverse_bits_len(index, bits);
      assert_eq!(reverse_bits_len(reversed, bits), index);
      nat(&mut out, index);
      nat(&mut out, reversed);
      reversals += 1;
    }
  }
  // Width zero is an overflowing shift, so an inadmissible nonzero index
  // retains its full-word reverse. The correspondence theorem needs a bound.
  nat(&mut out, reverse_bits_len(1, 0));
  assert_eq!(reverse_bits_len(1, 0), 1 << (word_bits - 1));

  let mut points = 0;
  for bits in 0..=32 {
    let generator = Val::two_adic_generator(bits);
    let indices = samples(bits, 1024);
    nat(&mut out, indices.len());
    for index in indices {
      let reversed = reverse_bits_len(index, bits);
      let point = generator.exp_u64(u64::try_from(reversed).unwrap());
      let input = Val::from_u64(7) * point;
      assert_eq!(point.exp_power_of_2(bits), Val::ONE);
      assert_ne!(input.exp_power_of_2(bits), Val::ONE);
      nat(&mut out, index);
      field(&mut out, point);
      field(&mut out, input);
      points += 1;
    }
  }

  let mut nested = 0;
  for parent in 0..=32 {
    let generator = Val::two_adic_generator(parent);
    for child in 0..=parent {
      assert_eq!(
        generator.exp_power_of_2(parent - child),
        Val::two_adic_generator(child)
      );
      let indices = samples(child, 4);
      nat(&mut out, indices.len());
      for index in indices {
        let padded = generator
          .exp_u64(u64::try_from(reverse_bits_len(index, parent)).unwrap());
        let reduced = Val::two_adic_generator(child)
          .exp_u64(u64::try_from(reverse_bits_len(index, child)).unwrap());
        assert_eq!(padded, reduced);
        nat(&mut out, index);
        field(&mut out, padded);
        nested += 1;
      }
    }
  }

  let folding = TwoAdicFriFolding::<(), ()>(PhantomData);
  assert_eq!(<TwoAdicFriFolding<(), ()> as FriFoldingStrategy<Val, ExtVal>>::extra_query_index_bits(&folding), 0);
  let mut rows = 0;
  let mut slots = 0;
  for parent in 0..=32 {
    // Arity one covers the public helper's boundary. Accepted FRI rounds
    // additionally require a positive arity logarithm.
    for log_arity in 0..=parent.min(8) {
      let height = parent - log_arity;
      let arity = 1 << log_arity;
      let mask =
        if height == 0 { 0 } else { usize::MAX >> (word_bits - height) };
      let mut indices = vec![0, mask / 2, mask, 0x0a37_51c9 & mask];
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
        let values: Vec<_> = (0..arity)
          .map(|slot| {
            ExtVal::new([
              Val::from_usize(slot + 1),
              Val::from_usize(slot * 19 + 3),
            ])
          })
          .collect();
        let child = Val::two_adic_generator(height)
          .exp_u64(u64::try_from(reverse_bits_len(index, height)).unwrap());
        for (slot, &node) in nodes.iter().enumerate() {
          let query = index * arity + slot;
          let direct = Val::two_adic_generator(parent)
            .exp_u64(u64::try_from(reverse_bits_len(query, parent)).unwrap());
          assert_eq!(node, direct);
          assert_eq!(node.exp_power_of_2(log_arity), child);
          let folded = <TwoAdicFriFolding<(), ()> as FriFoldingStrategy<
            Val,
            ExtVal,
          >>::fold_row(
            &folding,
            index,
            height,
            log_arity,
            ExtVal::from(node),
            values.iter().copied(),
          );
          assert_eq!(folded, values[slot]);
          field(&mut out, node);
          field(&mut out, child);
          extension(&mut out, folded);
          slots += 1;
        }
        rows += 1;
      }
    }
  }
  for count in [reversals, points, nested, rows, slots] {
    nat(&mut out, count);
  }
  if let Ok(path) = std::env::var("IX_FRI_DOMAIN_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  println!(
    "FRI domains: {reversals} reversals, {points} query points, {nested} nested points, {rows} rows and {slots} native fold-node selections"
  );
  Ok(())
}
