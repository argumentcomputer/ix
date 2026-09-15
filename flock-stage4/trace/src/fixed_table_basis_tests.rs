use super::*;
use crate::{F128FixedTableDavioLimitsV0, F128FixedTableLimitsV0};

const LIMITS: F128FixedTableBasisLimitsV0 = F128FixedTableBasisLimitsV0 {
  state_slots: 100_000,
  dense_words: 1_000_000,
  word_operations: 10_000_000,
  coefficient_terms: 1_000_000,
};

fn source(order: &[u32], entries: &[(u64, [u8; 16])]) -> F128FixedTableV0 {
  F128FixedTableV0::compile(
    order,
    entries.iter().copied(),
    F128FixedTableLimitsV0 { entries: 100_000, nodes: 100_000 },
  )
  .unwrap()
}

fn evaluate(table: &F128FixedTableBasisV0, index: u64) -> u128 {
  let mut values = table
    .constants()
    .iter()
    .map(|&b| u128::from_le_bytes(b))
    .collect::<Vec<_>>();
  let sum = |terms: &[u32], values: &[u128]| {
    terms.iter().fold(0, |sum, &i| sum ^ values[i as usize])
  };
  for layer in table.layers().iter().rev() {
    values = layer
      .rows()
      .iter()
      .map(|row| {
        sum(row.low(), &values)
          ^ if index >> layer.coordinate() & 1 != 0 {
            sum(row.slope(), &values)
          } else {
            0
          }
      })
      .collect();
  }
  sum(table.output(), &values)
}

#[test]
fn exact_coefficients_include_all_field_bits_orders_skips_and_duplicates() {
  let mut seed = 17u128;
  for variables in 0..=8u32 {
    for variant in 0..4 {
      let mut order = (0..variables).collect::<Vec<_>>();
      if variant & 1 != 0 {
        order.reverse();
      }
      if variables > 0 {
        order.rotate_left(1);
      }
      let entries = (0..1u64 << variables)
        .flat_map(|i| {
          seed = seed.wrapping_mul(0xda942042e4dd58b5).wrapping_add(0x57b425);
          let value = match variant {
            0 => seed,
            1 => u128::from((i & 3) == 0),
            2 => 1u128 << (i % 128),
            _ => {
              if i & 7 == 0 {
                0xa539
              } else {
                0
              }
            },
          };
          [(i, value.to_le_bytes()), (i, [0xa3; 16]), (i, [0xa3; 16])]
        })
        .collect::<Vec<_>>();
      let original = source(&order, &entries);
      let table = F128FixedTableBasisV0::compile(&original, LIMITS).unwrap();
      assert_eq!(table.source_digest(), original.digest());
      assert!(
        table.layers().iter().map(|l| l.coordinate()).eq(order.iter().copied())
      );
      for index in 0..1u64 << variables {
        let expected = entries
          .iter()
          .filter(|(i, _)| *i == index)
          .fold(0u128, |a, (_, b)| a ^ u128::from_le_bytes(*b));
        assert_eq!(
          evaluate(&table, index),
          expected,
          "n={variables} variant={variant} index={index}"
        );
      }
      let reversed = entries.iter().rev().copied().collect::<Vec<_>>();
      let rebuilt =
        F128FixedTableBasisV0::compile(&source(&order, &reversed), LIMITS)
          .unwrap();
      assert_eq!(table, rebuilt);
      assert_eq!(table.digest(), rebuilt.digest());
    }
  }
}

#[test]
fn empty_constant_and_sixty_four_coordinate_cubes_are_bounded() {
  for (order, entries) in [
    (vec![], vec![]),
    (vec![], vec![(0, [0x79; 16])]),
    ((0..64).rev().collect(), vec![(u64::MAX, [0x83; 16])]),
    (vec![1, 0], (0..4).map(|i| (i, [0x27; 16])).collect()),
  ] {
    let table =
      F128FixedTableBasisV0::compile(&source(&order, &entries), LIMITS)
        .unwrap();
    for index in [0, 1, 2, 3, u64::MAX] {
      let index = if order.len() < 64 {
        index & ((1u64 << order.len()) - 1)
      } else {
        index
      };
      let expected = entries
        .iter()
        .filter(|(i, _)| *i == index)
        .fold(0, |a, (_, b)| a ^ u128::from_le_bytes(*b));
      assert_eq!(evaluate(&table, index), expected);
    }
  }
}

#[test]
fn budgets_accept_exact_counts_and_refuse_each_one_below() {
  let original = source(
    &[2, 0, 1],
    &(0..8u64).map(|i| (i, (1u128 << i).to_le_bytes())).collect::<Vec<_>>(),
  );
  let table = F128FixedTableBasisV0::compile(&original, LIMITS).unwrap();
  let used = table.census();
  let exact = F128FixedTableBasisLimitsV0 {
    state_slots: used.state_slots,
    dense_words: used.dense_words,
    word_operations: used.word_operations,
    coefficient_terms: used.coefficient_terms,
  };
  assert_eq!(F128FixedTableBasisV0::compile(&original, exact).unwrap(), table);
  for (limits, error) in [
    (
      F128FixedTableBasisLimitsV0 {
        state_slots: exact.state_slots - 1,
        ..exact
      },
      Error::StateLimit,
    ),
    (
      F128FixedTableBasisLimitsV0 {
        dense_words: exact.dense_words - 1,
        ..exact
      },
      Error::DenseWordLimit,
    ),
    (
      F128FixedTableBasisLimitsV0 {
        word_operations: exact.word_operations - 1,
        ..exact
      },
      Error::WorkLimit,
    ),
    (
      F128FixedTableBasisLimitsV0 {
        coefficient_terms: exact.coefficient_terms - 1,
        ..exact
      },
      Error::CoefficientTermLimit,
    ),
  ] {
    assert_eq!(F128FixedTableBasisV0::compile(&original, limits), Err(error));
  }
  let davio = original
    .positive_davio(F128FixedTableDavioLimitsV0 {
      working_nodes: 1000,
      nodes: 1000,
      xor_calls: 10000,
    })
    .unwrap();
  assert_eq!(
    F128FixedTableBasisV0::compile(&davio, LIMITS),
    Err(Error::UnsupportedEncoding)
  );
}

#[test]
fn dense_decoder_crosses_word_boundary_and_identity_covers_program_not_budgets()
{
  let entries =
    (0..128u64).map(|i| (i, (1u128 << i).to_le_bytes())).collect::<Vec<_>>();
  let original = source(&(0..7).collect::<Vec<_>>(), &entries);
  let table = F128FixedTableBasisV0::compile(&original, LIMITS).unwrap();
  assert_eq!(table.constants().len(), 128);
  for i in 0..128 {
    assert_eq!(evaluate(&table, i), 1u128 << i);
  }
  let digest = table.digest();
  let mut changed = table.clone();
  changed.census.word_operations += 1;
  assert_eq!(digest, changed.digest());
  let mut mutations = Vec::new();
  let mut changed = table.clone();
  changed.source_digest[0] ^= 1;
  mutations.push(changed);
  let mut changed = table.clone();
  changed.constants[0][0] ^= 1;
  mutations.push(changed);
  let mut changed = table.clone();
  changed.layers[0].coordinate ^= 1;
  mutations.push(changed);
  let mut changed = table.clone();
  changed.layers[0].child_rank += 1;
  mutations.push(changed);
  let mut changed = table.clone();
  changed.layers[0].rows[0].low.push(0);
  mutations.push(changed);
  let mut changed = table.clone();
  changed.layers[0].rows[0].slope.push(0);
  mutations.push(changed);
  let mut changed = table.clone();
  changed.output.clear();
  mutations.push(changed);
  for changed in mutations {
    assert_ne!(digest, changed.digest());
  }
}
