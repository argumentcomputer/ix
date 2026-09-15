use super::*;

const LIMITS: F128StructuredMatricesLimitsV0 = F128StructuredMatricesLimitsV0 {
  tables: 16,
  source_entries: 10_000,
  blocks: 10_000,
  coefficient_terms: 10_000,
  shared_nodes: 10_000,
  temporary_nodes: 10_000,
};

fn id(table: u64, variables: u32) -> F128StaticMatrixIdV1 {
  F128StaticMatrixIdV1 {
    registry_digest: [17; 32],
    table,
    side: F128MatrixSideV1::A,
    variables,
  }
}

fn coefficient(
  program: &F128StructuredMatricesV0,
  output: usize,
  row: u32,
  col: u32,
) -> bool {
  let low = program.low_variables;
  let mask = (1 << low) - 1;
  let pair = u16::try_from((row & mask) | ((col & mask) << low)).unwrap();
  let mut values = Vec::new();
  for node in &program.nodes {
    values.push(match *node {
      F128StructuredMatrixNodeV0::Zero => false,
      F128StructuredMatrixNodeV0::Block(block) => {
        program.blocks[block as usize].binary_search(&pair).is_ok()
      },
      F128StructuredMatrixNodeV0::Branch {
        column,
        bit,
        low: zero,
        high: one,
      } => {
        let bits = if column { col } else { row };
        values[if (bits >> (low + bit)) & 1 == 0 { zero } else { one } as usize]
      },
    });
  }
  values[program.outputs[output].1 as usize]
}

#[test]
fn all_small_coefficients_match_across_shapes_sharing_and_cancellation() {
  for low in 0..=3 {
    let sources = (0..3)
      .map(|index| {
        let variables = low + index;
        let entries = (0..1u32 << variables)
          .flat_map(|row| {
            (0..1u32 << variables).filter_map(move |col| {
              ((row * 17 + col * 31 + index) % 7 < 2).then_some((row, col))
            })
          })
          .collect::<Vec<_>>();
        (id(u64::from(index), variables), entries)
      })
      .collect::<Vec<_>>();
    let program =
      F128StructuredMatricesV0::compile(low, sources.clone(), LIMITS).unwrap();
    let reversed = sources
      .iter()
      .map(|(id, entries)| {
        (*id, entries.iter().rev().copied().collect::<Vec<_>>())
      })
      .collect::<Vec<_>>();
    assert_eq!(
      program,
      F128StructuredMatricesV0::compile(low, reversed, LIMITS).unwrap()
    );
    let duplicates = sources
      .iter()
      .map(|(id, entries)| {
        let mut entries = entries.clone();
        entries.extend([(0, 0), (0, 0), (1, 1), (1, 1)]);
        (*id, entries)
      })
      .collect::<Vec<_>>();
    // The zero-dimensional first matrix cannot contain coordinate one.
    let duplicates = duplicates
      .into_iter()
      .map(|(id, mut entries)| {
        if id.variables == 0 {
          entries.truncate(entries.len() - 2);
        }
        (id, entries)
      })
      .collect::<Vec<_>>();
    let cancelled =
      F128StructuredMatricesV0::compile(low, duplicates, LIMITS).unwrap();
    assert_eq!(program.digest(), cancelled.digest());
    for (index, (id, entries)) in sources.iter().enumerate() {
      for row in 0..1u32 << id.variables {
        for col in 0..1u32 << id.variables {
          assert_eq!(
            coefficient(&program, index, row, col),
            entries.contains(&(row, col)),
            "low={low} table={index} row={row} col={col}"
          );
        }
      }
    }
  }
  let one = (id(0, 4), vec![(0, 0), (1, 1), (2, 2), (8, 1), (9, 0)]);
  let source =
    F128StructuredMatricesV0::compile(2, [one.clone()], LIMITS).unwrap();
  let shared = F128StructuredMatricesV0::compile(
    2,
    [one.clone(), (id(1, 4), one.1)],
    LIMITS,
  )
  .unwrap();
  assert_eq!(source.nodes, shared.nodes);
  assert_eq!(source.blocks, shared.blocks);
  assert_eq!(shared.outputs[0].1, shared.outputs[1].1);
  assert_ne!(source.digest(), shared.digest());
}

#[test]
fn empty_and_maximum_coordinate_tables_are_exact() {
  let empty = F128StructuredMatricesV0::compile(
    0,
    [(id(0, 32), Vec::<(u32, u32)>::new())],
    LIMITS,
  )
  .unwrap();
  assert_eq!(empty.nodes, vec![F128StructuredMatrixNodeV0::Zero]);
  assert_eq!(empty.high_variables, 32);
  let table = F128StructuredMatricesV0::compile(
    6,
    [(id(0, 32), vec![(u32::MAX, u32::MAX)])],
    LIMITS,
  )
  .unwrap();
  assert!(coefficient(&table, 0, u32::MAX, u32::MAX));
  for (row, col) in [(0, 0), (u32::MAX - 1, u32::MAX), (u32::MAX, u32::MAX - 1)]
  {
    assert!(!coefficient(&table, 0, row, col));
  }
  let constant =
    F128StructuredMatricesV0::compile(0, [(id(0, 0), vec![(0, 0)])], LIMITS)
      .unwrap();
  assert_eq!(constant.high_variables, 0);
  assert!(coefficient(&constant, 0, 0, 0));
}

#[test]
fn geometry_identity_and_each_exact_resource_limit_fail_closed() {
  let sources = [
    (id(0, 3), vec![(0, 1), (0, 2), (1, 1), (2, 3), (5, 6)]),
    (id(1, 2), vec![(0, 0), (3, 3)]),
  ];
  let table =
    F128StructuredMatricesV0::compile(1, sources.clone(), LIMITS).unwrap();
  let census = table.census();
  let exact = F128StructuredMatricesLimitsV0 {
    tables: 2,
    source_entries: census.source_entries,
    blocks: census.blocks,
    coefficient_terms: census.coefficient_terms,
    shared_nodes: census.shared_nodes,
    temporary_nodes: census.maximum_temporary_nodes,
  };
  assert_eq!(
    table,
    F128StructuredMatricesV0::compile(1, sources.clone(), exact).unwrap()
  );
  for which in 0..6 {
    let mut limits = exact;
    match which {
      0 => limits.tables -= 1,
      1 => limits.source_entries -= 1,
      2 => limits.blocks -= 1,
      3 => limits.coefficient_terms -= 1,
      4 => limits.shared_nodes -= 1,
      _ => limits.temporary_nodes -= 1,
    }
    assert!(
      F128StructuredMatricesV0::compile(1, sources.clone(), limits).is_err(),
      "limit {which}"
    );
  }
  assert_eq!(
    F128StructuredMatricesV0::compile(7, sources.clone(), LIMITS),
    Err(Error::Geometry)
  );
  assert_eq!(
    F128StructuredMatricesV0::compile(4, sources.clone(), LIMITS),
    Err(Error::Geometry)
  );
  assert_eq!(
    F128StructuredMatricesV0::compile(0, [(id(0, 33), vec![])], LIMITS),
    Err(Error::Geometry)
  );
  assert_eq!(
    F128StructuredMatricesV0::compile(0, [(id(0, 1), vec![(2, 0)])], LIMITS),
    Err(Error::Coordinate)
  );
  assert_eq!(
    F128StructuredMatricesV0::compile(0, [(id(0, 1), vec![(0, 2)])], LIMITS),
    Err(Error::Coordinate)
  );
  assert_eq!(
    F128StructuredMatricesV0::compile(
      0,
      Vec::<(F128StaticMatrixIdV1, Vec<(u32, u32)>)>::new(),
      LIMITS
    ),
    Err(Error::Geometry)
  );
  let mut reversed = sources.clone();
  reversed.reverse();
  assert_eq!(
    F128StructuredMatricesV0::compile(1, reversed, LIMITS),
    Err(Error::MatrixOrder)
  );
  let mut repeated = sources.clone();
  repeated[1].0 = id(0, 4);
  assert_eq!(
    F128StructuredMatricesV0::compile(1, repeated, LIMITS),
    Err(Error::MatrixOrder)
  );
  let mut foreign = sources;
  foreign[1].0.registry_digest[0] ^= 1;
  assert_eq!(
    F128StructuredMatricesV0::compile(1, foreign, LIMITS),
    Err(Error::Registry)
  );
}

#[test]
fn digest_binds_program_not_diagnostic_counters() {
  let program = F128StructuredMatricesV0::compile(
    1,
    [(id(0, 3), vec![(0, 0), (1, 1), (4, 1)])],
    LIMITS,
  )
  .unwrap();
  for which in 0..8 {
    let mut wrong = program.clone();
    match which {
      0 => wrong.low_variables += 1,
      1 => wrong.high_variables += 1,
      2 => wrong.pairs[0] ^= 1,
      3 => wrong.blocks[0][0] ^= 1,
      4 => wrong.outputs[0].0.registry_digest[0] ^= 1,
      5 => wrong.outputs[0].1 ^= 1,
      6 => wrong.outputs[0].0.variables += 1,
      _ => wrong.nodes.push(F128StructuredMatrixNodeV0::Zero),
    }
    assert_ne!(wrong.digest(), program.digest(), "field {which}");
  }
  let mut counters = program.clone();
  counters.census.source_entries += 1;
  assert_eq!(counters.digest(), program.digest());
}
