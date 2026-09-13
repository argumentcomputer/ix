use super::*;

const LIMITS: F128JaggedDirectLimitsV0 = F128JaggedDirectLimitsV0 {
  runs: 1000,
  combo_terms: 1000,
  row_nodes: 10_000,
  equality_nodes: 10_000,
};

fn id(rows: u32, columns: u32) -> F128JaggedMatrixIdV1 {
  F128JaggedMatrixIdV1 {
    circuit_digest: [11; 32],
    row_variables: rows,
    column_variables: columns,
  }
}

fn pair(left: u64, right: u64, bits: u32) -> u64 {
  (0..bits).fold(0, |v, bit| {
    v | (((left >> bit) & 1) << (2 * bit))
      | (((right >> bit) & 1) << (2 * bit + 1))
  })
}

fn coefficient(program: &F128JaggedDirectTableV0, row: u32, col: u64) -> bool {
  let mut eq = Vec::new();
  for node in &program.equality_nodes {
    eq.push(match *node {
      F128JaggedEqualityNodeV0::Factor { coordinate, complement } => {
        ((col >> coordinate) & 1 != 0) ^ complement
      },
      F128JaggedEqualityNodeV0::Multiply { left, right } => {
        eq[left as usize] && eq[right as usize]
      },
    });
  }
  let pairs =
    program.pair_outputs.iter().map(|&i| eq[i as usize]).collect::<Vec<_>>();
  for (index, &expected) in program.pairs.iter().enumerate() {
    assert_eq!(pairs[index], col == expected);
  }
  let mut nodes = Vec::new();
  for node in &program.row_nodes {
    nodes.push(match *node {
      F128JaggedRowNodeV0::Pair(index) => pairs[index as usize],
      F128JaggedRowNodeV0::Branch { coordinate, low, high } => {
        nodes[if (row >> coordinate) & 1 == 0 { low } else { high } as usize]
      },
    });
  }
  nodes[program.row_root as usize]
}

#[test]
fn every_small_matrix_coefficient_and_combo_address_are_exact() {
  for row_bits in 0..=5 {
    for boundary_bits in 1..=3 {
      let limit = 1u64 << (boundary_bits - 1);
      let bounds = (0..1u32 << row_bits)
        .map(|row| {
          let left = u64::from((row / 3) * 19) % (limit + 1);
          let right = (left + u64::from(row % 3)).min(limit);
          (left, right, 1)
        })
        .collect::<Vec<_>>();
      let matrix = id(row_bits, 2 * boundary_bits);
      let program = F128JaggedDirectTableV0::compile(
        matrix,
        bounds.clone(),
        0..1u32 << row_bits,
        LIMITS,
      )
      .unwrap();
      assert_eq!(
        program,
        F128JaggedDirectTableV0::compile(
          matrix,
          bounds.clone(),
          0..1u32 << row_bits,
          LIMITS,
        )
        .unwrap()
      );
      for row in 0..1u32 << row_bits {
        let (left, right, _) = bounds[row as usize];
        let expected = pair(left, right, boundary_bits);
        assert_eq!(program.combo[row as usize].0, row);
        assert_eq!(
          program.pairs[program.combo[row as usize].1 as usize],
          expected
        );
        for column in 0..1u64 << (2 * boundary_bits) {
          assert_eq!(coefficient(&program, row, column), column == expected);
        }
      }
    }
  }
}

#[test]
fn run_boundaries_padding_and_maximum_dimensions_do_not_enumerate_domains() {
  let bounds = [(0, 1, 3), (1, 2, 2), (2, 2, 3)];
  let program = F128JaggedDirectTableV0::compile(
    id(3, 4),
    bounds,
    [0, 2, 3, 4, 5, 7, 3],
    LIMITS,
  )
  .unwrap();
  for row in 0..8 {
    let (left, right) = if row < 3 {
      (0, 1)
    } else if row < 5 {
      (1, 2)
    } else {
      (2, 2)
    };
    for column in 0..16 {
      assert_eq!(
        coefficient(&program, row, column),
        column == pair(left, right, 2)
      );
    }
  }
  let high = 1u64 << 31;
  let huge = F128JaggedDirectTableV0::compile(
    id(32, 64),
    [(0, 0, u32::MAX), (high, high, 1)],
    [0, u32::MAX],
    LIMITS,
  )
  .unwrap();
  let top = pair(high, high, 32);
  assert!(coefficient(&huge, 0, 0));
  assert!(!coefficient(&huge, 0, top));
  assert!(coefficient(&huge, u32::MAX - 1, 0));
  assert!(coefficient(&huge, u32::MAX, top));
  assert!(!coefficient(&huge, u32::MAX, top ^ 1));
  assert!(huge.row_nodes.len() < 100);
  assert!(huge.equality_nodes.len() < 200);
  let constant = F128JaggedDirectTableV0::compile(
    id(3, 2),
    [(0, 0, 3), (0, 0, 5)],
    [7],
    LIMITS,
  )
  .unwrap();
  assert_eq!(constant.row_nodes, [F128JaggedRowNodeV0::Pair(0)]);
}

#[test]
fn exact_limits_and_malformed_layouts_fail_closed() {
  let matrix = id(3, 4);
  let bounds = [(0, 1, 3), (1, 2, 2), (2, 2, 3)];
  let combo = [0, 3, 7];
  let program =
    F128JaggedDirectTableV0::compile(matrix, bounds, combo, LIMITS).unwrap();
  let exact = F128JaggedDirectLimitsV0 {
    runs: 3,
    combo_terms: 3,
    row_nodes: u32::try_from(program.row_nodes.len()).unwrap(),
    equality_nodes: u32::try_from(program.equality_nodes.len()).unwrap(),
  };
  assert_eq!(
    program,
    F128JaggedDirectTableV0::compile(matrix, bounds, combo, exact).unwrap()
  );
  for kind in 0..4 {
    let mut limits = exact;
    let name = match kind {
      0 => {
        limits.runs -= 1;
        "runs"
      },
      1 => {
        limits.combo_terms -= 1;
        "combo terms"
      },
      2 => {
        limits.row_nodes -= 1;
        "row nodes"
      },
      3 => {
        limits.equality_nodes -= 1;
        "equality nodes"
      },
      _ => unreachable!(),
    };
    assert_eq!(
      F128JaggedDirectTableV0::compile(matrix, bounds, combo, limits),
      Err(Error::Limit(name))
    );
  }
  for (rows, cols) in [(33, 4), (3, 0), (3, 3), (3, 66)] {
    assert_eq!(
      F128JaggedDirectTableV0::compile(id(rows, cols), bounds, combo, LIMITS),
      Err(Error::Geometry)
    );
  }
  for (bounds, expected) in [
    (vec![], Error::Coverage),
    (vec![(0, 0, 7)], Error::Coverage),
    (vec![(0, 0, 9)], Error::Coverage),
    (vec![(0, 0, 0), (0, 0, 8)], Error::Coverage),
    (vec![(2, 1, 8)], Error::Boundary),
    (vec![(0, 3, 8)], Error::Boundary),
  ] {
    assert_eq!(
      F128JaggedDirectTableV0::compile(matrix, bounds, combo, LIMITS),
      Err(expected)
    );
  }
  for combo in [vec![], vec![8], vec![u32::MAX]] {
    assert_eq!(
      F128JaggedDirectTableV0::compile(matrix, bounds, combo, LIMITS),
      Err(Error::ComboAddress)
    );
  }
}

#[test]
fn program_identity_binds_layout_pair_tree_row_diagram_and_combo_order() {
  let original = F128JaggedDirectTableV0::compile(
    id(3, 4),
    [(0, 1, 3), (1, 2, 2), (2, 2, 3)],
    [0, 3, 7],
    LIMITS,
  )
  .unwrap();
  for field in 0..10 {
    let mut changed = original.clone();
    match field {
      0 => changed.matrix.circuit_digest[0] ^= 1,
      1 => changed.matrix.row_variables += 1,
      2 => changed.matrix.column_variables += 2,
      3 => changed.runs[0].0 += 1,
      4 => changed.pairs[0] ^= 1,
      5 => {
        changed.equality_nodes[0] =
          F128JaggedEqualityNodeV0::Multiply { left: 0, right: 0 }
      },
      6 => changed.pair_outputs[0] += 1,
      7 => changed.row_nodes[0] = F128JaggedRowNodeV0::Pair(1),
      8 => changed.row_root += 1,
      9 => changed.combo.swap(0, 1),
      _ => unreachable!(),
    }
    assert_ne!(changed.digest(), original.digest(), "field {field}");
  }
}
