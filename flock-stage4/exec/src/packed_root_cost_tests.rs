//! Bounded setup-owned root-program cost probes. These do not select a
//! different approved program, omit roots, generate a key or prove Exec.

use super::{
  capacity_tests::SMALL,
  closure_tests::{LIMITS, evaluate},
  memory_summary,
};
use ix_stage4_trace::{
  F128FixedMatrixProgramV0 as Program, F128FixedTableBasisV0,
  F128FixedTableLimitsV0, F128FixedTableV0, F128MatrixSideV1,
};
use ixby_flock::{
  blake3_backend::Blake3Backend,
  ixby::{
    decode::PrimitiveSet,
    exec::{CompiledExec, SemanticProfile, compile_exec_profile_with_backend},
  },
};
use std::time::Instant;

fn setup() -> CompiledExec {
  compile_exec_profile_with_backend(
    SemanticProfile::scalar(SMALL).unwrap(),
    SMALL,
    PrimitiveSet::scalar(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap()
}

#[test]
#[ignore = "bounded exact cofactor/rank diagnostic for packed small-class root tables; not a constraint census, adoption, key or proof"]
fn packed_small_root_program_rank_diagnostic() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let tables =
    crate::compile_exec_root_tables(&replay, LIMITS.diagrams).unwrap();
  let sources = tables
    .matrices()
    .iter()
    .map(|(id, table)| {
      (format!("Boolean {} {:?} k={}", id.table, id.side, id.variables), table)
    })
    .chain([
      ("structure".to_owned(), &tables.structure().1),
      ("jagged".to_owned(), &tables.jagged().1),
    ]);
  let mut outcomes = 0;
  for (name, source) in sources {
    let started = Instant::now();
    match F128FixedTableBasisV0::compile(source, LIMITS.structure_basis) {
      Ok(basis) => {
        let ranks =
          basis.layers().iter().map(|l| l.rows().len()).collect::<Vec<_>>();
        let slopes = basis
          .layers()
          .iter()
          .flat_map(|l| l.rows())
          .filter(|r| !r.slope().is_empty())
          .count();
        eprintln!(
          "packed root {name}: source nnz={} nodes={}; ranks={ranks:?}; nonzero slope sites={slopes} (NOT constraint count); {:?}; {:.3}s; {}",
          source.nonzero_entries(),
          source.nodes().len(),
          basis.census(),
          started.elapsed().as_secs_f64(),
          memory_summary()
        );
        let source = Program::DecisionDiagram(source.clone());
        let basis = Program::CofactorBasis(basis);
        for seed in [0u128, 1, 0x9ab0_712d_f384_5231_c876_efa9_97b1_13ad] {
          let point = (0..ranks.len())
            .map(|i| {
              seed
                .wrapping_mul(i as u128 + 3)
                .rotate_left(u32::try_from(i).unwrap())
                .to_le_bytes()
            })
            .collect::<Vec<_>>();
          assert_eq!(
            evaluate(&basis, &point, &[]),
            evaluate(&source, &point, &[]),
            "{name}"
          );
        }
      },
      Err(error) => {
        eprintln!(
          "packed root {name}: source nnz={} nodes={}; basis REFUSED {error}; {:.3}s; {}",
          source.nonzero_entries(),
          source.nodes().len(),
          started.elapsed().as_secs_f64(),
          memory_summary()
        );
      },
    }
    outcomes += 1;
  }
  assert_eq!(outcomes, 66);
}

#[test]
#[ignore = "bounded exact alternative-order diagnostic on the largest packed root tables; not a constraint census or program adoption"]
fn packed_small_large_root_order_diagnostic() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let tables =
    crate::compile_exec_root_tables(&replay, LIMITS.diagrams).unwrap();
  for (id, source) in tables.matrices().iter().filter(|(id, _)| id.table < 3) {
    let ty = &setup.verifier_shape().registry.boolean_types()
      [usize::try_from(id.table).unwrap()];
    let matrix = match id.side {
      F128MatrixSideV1::A => &ty.a_0,
      F128MatrixSideV1::B => &ty.b_0,
    };
    let k = id.variables;
    let entries = matrix
      .rows
      .iter()
      .enumerate()
      .flat_map(|(row, cols)| {
        cols.iter().map(move |&col| {
          (row as u64 | ((col as u64) << k), 1u128.to_le_bytes())
        })
      })
      .collect::<Vec<_>>();
    let mut orders = vec![
      ("interleaved_msb".to_owned(), source.order().to_vec()),
      ("interleaved_lsb".to_owned(), (0..k).flat_map(|i| [i, k + i]).collect()),
      (
        "reverse_interleaved_msb".to_owned(),
        (0..k).rev().flat_map(|i| [k + i, i]).collect(),
      ),
      (
        "reverse_interleaved_lsb".to_owned(),
        (0..k).flat_map(|i| [k + i, i]).collect(),
      ),
      (
        "rows_then_columns".to_owned(),
        (0..k).rev().chain((k..2 * k).rev()).collect(),
      ),
      (
        "columns_then_rows".to_owned(),
        (k..2 * k).rev().chain((0..k).rev()).collect(),
      ),
    ];
    for chunk in [2, 3, 4, 6] {
      let bits = (0..k).rev().collect::<Vec<_>>();
      for column_first in [false, true] {
        let order = bits
          .chunks(chunk)
          .flat_map(|part| {
            let a = if column_first { k } else { 0 };
            let b = k - a;
            part
              .iter()
              .map(move |i| i + a)
              .chain(part.iter().map(move |i| i + b))
          })
          .collect();
        orders
          .push((format!("chunk{chunk}_column_first={column_first}"), order));
      }
    }
    let expected_points = [0u128, 0xb710_9881_d2f3_9471_983a_adef_2853_176b]
      .map(|seed| {
        (0..2 * k)
          .map(|i| {
            seed.wrapping_mul(u128::from(i) + 3).rotate_left(i).to_le_bytes()
          })
          .collect::<Vec<_>>()
      });
    let source_program = Program::DecisionDiagram(source.clone());
    for (name, order) in orders {
      let started = Instant::now();
      let candidate = F128FixedTableV0::compile(
        &order,
        entries.iter().copied(),
        F128FixedTableLimitsV0 { entries: 100_000, nodes: 1_000_000 },
      )
      .unwrap();
      eprintln!(
        "packed root order {} {:?} {name}: nnz={} nodes={} source_nodes={}; {:.3}s",
        id.table,
        id.side,
        candidate.nonzero_entries(),
        candidate.nodes().len(),
        source.nodes().len(),
        started.elapsed().as_secs_f64()
      );
      let candidate = Program::DecisionDiagram(candidate);
      for point in &expected_points {
        assert_eq!(
          evaluate(&candidate, point, &[]),
          evaluate(&source_program, point, &[])
        );
      }
    }
  }
}
