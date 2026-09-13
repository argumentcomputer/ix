use super::*;
use crate::{F128MatrixSideV1, F128StructuredMatricesLimitsV0};

const SOURCE_LIMITS: F128StructuredMatricesLimitsV0 =
  F128StructuredMatricesLimitsV0 {
    tables: 16,
    source_entries: 100_000,
    blocks: 100_000,
    coefficient_terms: 100_000,
    shared_nodes: 100_000,
    temporary_nodes: 100_000,
  };
const LIMITS: F128FixedTableBasisLimitsV0 = F128FixedTableBasisLimitsV0 {
  state_slots: 1_000_000,
  dense_words: 1_000_000,
  word_operations: 10_000_000,
  coefficient_terms: 1_000_000,
};

fn id(table: u64, variables: u32) -> F128StaticMatrixIdV1 {
  F128StaticMatrixIdV1 {
    registry_digest: [73; 32],
    table,
    side: F128MatrixSideV1::A,
    variables,
  }
}

fn coefficient(
  program: &F128StructuredMatrixSpanV0,
  output: usize,
  row: u32,
  col: u32,
) -> bool {
  let low = program.low_variables;
  let mask = (1 << low) - 1;
  let pair = u16::try_from((row & mask) | ((col & mask) << low)).unwrap();
  let mut values = program
    .leaf_generators
    .iter()
    .map(|terms| terms.binary_search(&pair).is_ok())
    .collect::<Vec<_>>();
  let sum = |values: &[bool], terms: &[u32]| {
    terms.iter().fold(false, |v, &i| v ^ values[i as usize])
  };
  for layer in program.layers.iter().rev() {
    assert_eq!(layer.child_width() as usize, values.len());
    let coordinate = layer.coordinate();
    let high = program.high_variables;
    let point = if coordinate < high {
      (row >> (low + coordinate)) & 1 == 1
    } else {
      (col >> (low + coordinate - high)) & 1 == 1
    };
    values = layer
      .rows()
      .iter()
      .map(|r| sum(&values, r.low()) ^ (point && sum(&values, r.slope())))
      .collect();
  }
  sum(&values, &program.outputs[output].1)
}

#[test]
fn entire_boolean_cubes_match_literal_coefficients_and_rebuild() {
  for low in 0..=3 {
    let sources = (0..3)
      .map(|index| {
        let variables = low + index;
        let mut entries = (0..1u32 << variables)
          .flat_map(|row| {
            (0..1u32 << variables).filter_map(move |col| {
              ((row * 7 + col * 13 + index) % 11 < 3).then_some((row, col))
            })
          })
          .collect::<Vec<_>>();
        entries.extend([(0, 0), (0, 0)]);
        (id(u64::from(index), variables), entries)
      })
      .collect::<Vec<_>>();
    let source =
      F128StructuredMatricesV0::compile(low, sources.clone(), SOURCE_LIMITS)
        .unwrap();
    let program = F128StructuredMatrixSpanV0::compile(&source, LIMITS).unwrap();
    assert_eq!(program.source_digest(), source.digest());
    assert_eq!(
      program,
      F128StructuredMatrixSpanV0::compile(&source, LIMITS).unwrap()
    );
    let reverse = sources
      .iter()
      .map(|(id, entries)| {
        (*id, entries.iter().rev().copied().collect::<Vec<_>>())
      })
      .collect::<Vec<_>>();
    let reversed =
      F128StructuredMatricesV0::compile(low, reverse, SOURCE_LIMITS).unwrap();
    assert_eq!(
      program,
      F128StructuredMatrixSpanV0::compile(&reversed, LIMITS).unwrap()
    );
    for (index, (id, entries)) in sources.iter().enumerate() {
      assert_eq!(program.outputs[index].0, *id);
      for row in 0..1u32 << id.variables {
        for col in 0..1u32 << id.variables {
          let expected =
            entries.iter().filter(|&&(r, c)| r == row && c == col).count() % 2
              == 1;
          assert_eq!(
            coefficient(&program, index, row, col),
            expected,
            "low={low} table={index} row={row} col={col}"
          );
        }
      }
    }
  }
}

#[test]
fn block_vectors_are_not_numeric_tags_and_dependent_outputs_are_retained() {
  // Four dependent blocks span three low-pair vectors. Treating arbitrary
  // block IDs as field coefficients would not preserve this exact module.
  let entries =
    [(0, 0), (0, 1), (4, 0), (4, 2), (8, 1), (8, 2), (12, 0), (12, 1), (12, 2)];
  let source = F128StructuredMatricesV0::compile(
    2,
    [
      (id(0, 4), entries.to_vec()),
      (id(1, 4), entries.to_vec()),
      (id(2, 2), vec![]),
    ],
    SOURCE_LIMITS,
  )
  .unwrap();
  let program = F128StructuredMatrixSpanV0::compile(&source, LIMITS).unwrap();
  assert_eq!(source.blocks().len(), 4);
  assert_eq!(program.leaf_generators.len(), 3);
  assert!(program.leaf_generators.iter().all(|row| row.len() == 1));
  assert_eq!(program.outputs[0].1, program.outputs[1].1);
  assert!(program.outputs[2].1.is_empty());
  for row in 0..16 {
    for col in 0..16 {
      for output in 0..2 {
        assert_eq!(
          coefficient(&program, output, row, col),
          entries.contains(&(row, col))
        );
      }
    }
  }
}

#[test]
fn zero_dimension_empty_and_maximum_coordinate_forests_are_exact() {
  for (low, variables, entries) in
    [(0, 0, vec![(0, 0)]), (0, 32, vec![]), (6, 32, vec![(u32::MAX, u32::MAX)])]
  {
    let source = F128StructuredMatricesV0::compile(
      low,
      [(id(0, variables), entries.clone())],
      SOURCE_LIMITS,
    )
    .unwrap();
    let program = F128StructuredMatrixSpanV0::compile(&source, LIMITS).unwrap();
    for (row, col) in
      [(0, 0), (u32::MAX, u32::MAX), (u32::MAX - 1, u32::MAX), (u32::MAX, 0)]
    {
      if variables == 0 && (row != 0 || col != 0) {
        continue;
      }
      assert_eq!(
        coefficient(&program, 0, row, col),
        entries.contains(&(row, col))
      );
    }
    if entries.is_empty() {
      assert!(program.pairs.is_empty());
      assert!(program.leaf_generators.is_empty());
      assert!(program.layers.iter().all(|layer| layer.rows().is_empty()));
    }
  }
}

fn fixture() -> F128StructuredMatrixSpanV0 {
  let source = F128StructuredMatricesV0::compile(
    1,
    [
      (id(0, 3), vec![(0, 0), (0, 1), (2, 3), (3, 4), (6, 2), (7, 7)]),
      (id(1, 2), vec![(1, 0), (2, 1)]),
    ],
    SOURCE_LIMITS,
  )
  .unwrap();
  F128StructuredMatrixSpanV0::compile(&source, LIMITS).unwrap()
}

#[test]
fn each_cumulative_compilation_limit_is_exact_and_fail_closed() {
  let source = F128StructuredMatricesV0::compile(
    1,
    [(id(0, 3), vec![(0, 1), (0, 3), (1, 2), (2, 3), (3, 1), (7, 7)])],
    SOURCE_LIMITS,
  )
  .unwrap();
  let program = F128StructuredMatrixSpanV0::compile(&source, LIMITS).unwrap();
  let census = program.census();
  let exact = F128FixedTableBasisLimitsV0 {
    state_slots: census.state_slots,
    dense_words: census.dense_words,
    word_operations: census.word_operations,
    coefficient_terms: census.coefficient_terms,
  };
  assert_eq!(
    program,
    F128StructuredMatrixSpanV0::compile(&source, exact).unwrap()
  );
  for which in 0..4 {
    let mut limits = exact;
    let expected = match which {
      0 => {
        limits.state_slots -= 1;
        Error::StateLimit
      },
      1 => {
        limits.dense_words -= 1;
        Error::DenseWordLimit
      },
      2 => {
        limits.word_operations -= 1;
        Error::WorkLimit
      },
      _ => {
        limits.coefficient_terms -= 1;
        Error::CoefficientTermLimit
      },
    };
    assert_eq!(
      F128StructuredMatrixSpanV0::compile(&source, limits),
      Err(expected)
    );
  }
}

#[test]
fn digest_binds_every_program_component_but_not_census() {
  let original = fixture();
  for which in 0..10 {
    let mut program = original.clone();
    match which {
      0 => program.source_digest[0] ^= 1,
      1 => program.low_variables += 1,
      2 => program.high_variables += 1,
      3 => program.pairs[0] ^= 1,
      4 => program.leaf_generators[0][0] ^= 1,
      5 => program.layers[0].coordinate ^= 1,
      6 => program.layers[0].child_width += 1,
      7 => program.layers[0].rows[0].low.push(0),
      8 => program.layers[0].rows[0].slope.push(0),
      _ => program.outputs[0].1.push(0),
    }
    assert_ne!(program.digest(), original.digest(), "component {which}");
  }
  for which in 0..4 {
    let mut program = original.clone();
    match which {
      0 => program.outputs[0].0.registry_digest[0] ^= 1,
      1 => program.outputs[0].0.table += 1,
      2 => program.outputs[0].0.side = F128MatrixSideV1::B,
      _ => program.outputs[0].0.variables += 1,
    }
    assert_ne!(program.digest(), original.digest());
  }
  let mut program = original.clone();
  program.census = Default::default();
  assert_eq!(program.digest(), original.digest());
}
