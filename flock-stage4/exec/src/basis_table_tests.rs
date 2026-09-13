//! Bounded optional cost experiment. Does not change the approved closure
//! programs, Flock parameters, setup identities, or terminal proof relation.

use super::{memory_summary, setup};
use flock_prover::field::F128;
use ix_stage4_trace::{
  F128FixedTableBasisLimitsV0, F128FixedTableBasisV0, F128FixedTableLimitsV0,
  F128FixedTableNodeV0 as Node, F128FixedTableV0,
};
use std::time::Instant;

const LIMITS: F128FixedTableBasisLimitsV0 = F128FixedTableBasisLimitsV0 {
  state_slots: 4_000_000,
  dense_words: 16_000_000,
  word_operations: 200_000_000,
  coefficient_terms: 8_000_000,
};

fn decode(bytes: [u8; 16]) -> F128 {
  F128::new(
    u64::from_le_bytes(bytes[..8].try_into().unwrap()),
    u64::from_le_bytes(bytes[8..].try_into().unwrap()),
  )
}

fn point(count: usize, seed: u64) -> Vec<F128> {
  (0..count)
    .map(|i| {
      F128::new(
        seed.wrapping_mul(i as u64 + 17),
        (seed ^ i as u64).wrapping_mul(0x9e3779b97f4a7c15),
      )
    })
    .collect()
}

fn evaluate_source(table: &F128FixedTableV0, point: &[F128]) -> F128 {
  let mut values = Vec::new();
  for node in table.nodes() {
    let value = match *node {
      Node::Constant(bytes) => decode(bytes),
      Node::Branch { coordinate, low, high } => {
        values[low as usize]
          + point[coordinate as usize]
            * (values[low as usize] + values[high as usize])
      },
      Node::Davio { .. } => panic!("source must be Shannon"),
    };
    values.push(value);
  }
  values[table.root() as usize]
}

fn evaluate_basis(table: &F128FixedTableBasisV0, point: &[F128]) -> F128 {
  let mut values =
    table.constants().iter().copied().map(decode).collect::<Vec<_>>();
  let sum = |indices: &[u32], values: &[F128]| {
    indices.iter().fold(F128::ZERO, |a, &i| a + values[i as usize])
  };
  for layer in table.layers().iter().rev() {
    values = layer
      .rows()
      .iter()
      .map(|row| {
        sum(row.low(), &values)
          + point[layer.coordinate() as usize] * sum(row.slope(), &values)
      })
      .collect();
  }
  sum(table.output(), &values)
}

#[test]
#[ignore = "bounded exact cofactor-basis cost experiment on approved tables; no root-program adoption or terminal proof"]
fn fixed_root_table_cofactor_basis_census() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let started = Instant::now();
  let tables = crate::compile_exec_root_tables(
    &replay,
    F128FixedTableLimitsV0 { entries: 64_000_000, nodes: 2_000_000 },
  )
  .unwrap();
  eprintln!(
    "basis experiment exact source tables: {:.3}s; digest {:?}; {}",
    started.elapsed().as_secs_f64(),
    tables.digest(),
    memory_summary()
  );
  let sources = tables
    .matrices()
    .iter()
    .map(|(id, table)| (format!("Boolean {} {:?}", id.table, id.side), table))
    .chain([
      ("structure".to_owned(), &tables.structure().1),
      ("jagged".to_owned(), &tables.jagged().1),
    ]);
  let mut completed = 0;
  let mut refused = 0;
  for (name, source) in sources {
    let started = Instant::now();
    let result = F128FixedTableBasisV0::compile(source, LIMITS);
    match result {
      Ok(table) => {
        let ranks =
          table.layers().iter().map(|l| l.rows().len()).collect::<Vec<_>>();
        let nonzero_slopes = table
          .layers()
          .iter()
          .flat_map(|l| l.rows())
          .filter(|r| !r.slope().is_empty())
          .count();
        eprintln!(
          "basis {name}: {:.3}s; source {} nodes; ranks {ranks:?}; leaf rank {}; {nonzero_slopes} nonzero slope sites (NOT general-product or constraint count); {:?}; digest {:?}; {}",
          started.elapsed().as_secs_f64(),
          source.nodes().len(),
          table.constants().len(),
          table.census(),
          table.digest(),
          memory_summary()
        );
        for point in [
          vec![F128::ZERO; source.order().len()],
          vec![F128::ONE; source.order().len()],
          point(source.order().len(), 7),
          point(source.order().len(), 0xb515),
        ] {
          assert_eq!(
            evaluate_basis(&table, &point),
            evaluate_source(source, &point),
            "{name}"
          );
        }
        completed += 1;
      },
      Err(error) => {
        eprintln!(
          "basis {name}: refused within {LIMITS:?}: {error}; {:.3}s; source {} nodes; {}",
          started.elapsed().as_secs_f64(),
          source.nodes().len(),
          memory_summary()
        );
        refused += 1;
      },
    }
  }
  assert_eq!(completed + refused, 48);
  assert!(completed > 0);
  eprintln!(
    "basis experiment: {completed} complete exact programs with four native-field differentials each; {refused} bounded refusals; NO approved root-program change, full R1CS census, key or proof"
  );
}

#[test]
#[ignore = "bounded paired R1CS/PLONK component census of the actual structure table; no full closed census or proof"]
fn structure_cofactor_basis_component_constraint_census() {
  use ix_fflonk::PlonkGateProjectionV1;
  use ix_terminal_circuit::{
    ConstraintPhase, R1csBuilder, R1csError, alloc_f128_private,
    constrain_f128_fixed_table, constrain_f128_fixed_table_basis,
  };
  // Resource cutoff applies independently to EACH component. A prefix is
  // never reported as a completed circuit or selected as an optimization.
  const ROW_LIMIT: u64 = 200_000_000;
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let tables = crate::compile_exec_root_tables(
    &replay,
    F128FixedTableLimitsV0 { entries: 64_000_000, nodes: 2_000_000 },
  )
  .unwrap();
  let source = &tables.structure().1;
  let basis = F128FixedTableBasisV0::compile(source, LIMITS).unwrap();
  eprintln!(
    "structure source digest {:?}, basis digest {:?}, source tables {:?}",
    source.digest(),
    basis.digest(),
    tables.digest()
  );
  let mut completed_rows = Vec::new();
  for use_basis in [false, true] {
    let started = Instant::now();
    let projection = PlonkGateProjectionV1::new();
    let observed = projection.clone();
    let mut observe = observed.observer();
    let mut count = 0u64;
    let mut builder = R1csBuilder::new_shape_projection_observed_fallible(
      move |c| {
        observe(c);
        count += 1;
        if count.is_multiple_of(10_000_000) {
          eprintln!(
            "structure basis={use_basis} prefix {count} R1CS constraints, {:.3}s; {}",
            started.elapsed().as_secs_f64(),
            memory_summary()
          );
        }
        let prefix = observed.prefix().map_err(|_| R1csError::InternalShape)?;
        if prefix.constraint_rows > ROW_LIMIT {
          return Err(R1csError::ResourceLimit {
            resource: "structure component PLONK rows",
            limit: ROW_LIMIT,
            actual: prefix.constraint_rows,
          });
        }
        Ok(())
      },
    );
    let phase = ConstraintPhase::MatrixFold;
    let point = (0..source.order().len())
      .map(|_| alloc_f128_private(&mut builder, [0; 16], phase).unwrap())
      .collect::<Vec<_>>();
    let result = if use_basis {
      constrain_f128_fixed_table_basis(&mut builder, &basis, &point, phase)
    } else {
      constrain_f128_fixed_table(&mut builder, source, &point, phase)
    };
    let finished = builder.finish_projection();
    match (result, finished) {
      (Ok(_), Ok(r1cs)) => {
        let plonk = projection.finish_for_sizing(&r1cs).unwrap();
        eprintln!(
          "structure basis={use_basis} COMPLETE component {:.3}s: {r1cs:?}; {plonk:?}; {}",
          started.elapsed().as_secs_f64(),
          memory_summary()
        );
        completed_rows.push(plonk.constraint_rows);
      },
      (
        Err(R1csError::ResourceLimit { .. }),
        Err(R1csError::ResourceLimit { .. }),
      ) => {
        eprintln!(
          "structure basis={use_basis} REFUSED component prefix {:?}, {:.3}s; no full census",
          projection.prefix().unwrap(),
          started.elapsed().as_secs_f64()
        );
      },
      other => panic!("unexpected component outcome: {other:?}"),
    }
  }
  // An observation, not a performance assertion or automatic adoption.
  eprintln!(
    "structure completed component constraint rows {completed_rows:?}; full closed relation/key/proof remains unproduced"
  );
}

#[test]
#[ignore = "bounded larger cofactor-basis budget diagnostic on four largest tables; no automatic adoption"]
fn large_table_cofactor_basis_budget_diagnostic() {
  let limits = F128FixedTableBasisLimitsV0 {
    dense_words: 64_000_000,
    word_operations: 4_000_000_000,
    coefficient_terms: 16_000_000,
    ..LIMITS
  };
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let tables = crate::compile_exec_root_tables(
    &replay,
    F128FixedTableLimitsV0 { entries: 64_000_000, nodes: 2_000_000 },
  )
  .unwrap();
  for (id, source) in
    tables.matrices().iter().filter(|(id, _)| [0, 9].contains(&id.table))
  {
    let started = Instant::now();
    match F128FixedTableBasisV0::compile(source, limits) {
      Ok(table) => {
        let ranks =
          table.layers().iter().map(|l| l.rows().len()).collect::<Vec<_>>();
        eprintln!(
          "large basis {} {:?}: {:.3}s; ranks {ranks:?}; {:?}; digest {:?}; {}",
          id.table,
          id.side,
          started.elapsed().as_secs_f64(),
          table.census(),
          table.digest(),
          memory_summary()
        );
        for seed in [7, 0xb515] {
          let point = point(source.order().len(), seed);
          assert_eq!(
            evaluate_basis(&table, &point),
            evaluate_source(source, &point)
          );
        }
      },
      Err(error) => eprintln!(
        "large basis {} {:?}: refused {error}, {:.3}s within {limits:?}; {}",
        id.table,
        id.side,
        started.elapsed().as_secs_f64(),
        memory_summary()
      ),
    }
  }
}
