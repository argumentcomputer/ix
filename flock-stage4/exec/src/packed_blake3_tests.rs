//! Cost/equivalence of the candidate compression registry, NOT an approved
//! Exec backend, whole closed relation, terminal key, or compact proof.

use super::closure_tests::evaluate;
use flock_prover::{
  field::F128,
  matrix_fold::{Weight, bilinear},
  r1cs::SparseBinaryMatrix,
};
use ix_stage4_trace::{
  F128FixedMatrixProgramV0 as Program, F128FixedTableLimitsV0, F128FixedTableV0,
};
use ixby_flock::packed_blake3::{PackedGateKind, PackedWordGate};

fn bytes(x: F128) -> [u8; 16] {
  (u128::from(x.lo) | (u128::from(x.hi) << 64)).to_le_bytes()
}

fn point(bits: usize, seed: u64) -> Vec<F128> {
  (0..bits)
    .map(|i| {
      F128::new(
        seed.wrapping_mul(i as u64 + 0x0191_8731),
        seed
          .wrapping_add(0xb871_3141_c711_e592)
          .rotate_left(u32::try_from(i).unwrap()),
      )
    })
    .collect()
}

fn diagram(matrix: &SparseBinaryMatrix, bits: usize) -> F128FixedTableV0 {
  assert_eq!(matrix.num_rows, 1 << bits);
  assert_eq!(matrix.num_cols, 1 << bits);
  let bits = u32::try_from(bits).unwrap();
  let order: Vec<_> = (0..bits).rev().flat_map(|i| [i, bits + i]).collect();
  let entries = matrix.rows.iter().enumerate().flat_map(|(row, cols)| {
    cols.iter().map(move |col| {
      (row as u64 | ((*col as u64) << bits), 1u128.to_le_bytes())
    })
  });
  F128FixedTableV0::compile(
    &order,
    entries,
    F128FixedTableLimitsV0 { entries: 20_000, nodes: 10_000 },
  )
  .unwrap()
}

#[test]
fn candidate_word_table_diagrams_match_all_native_bilinear_roots() {
  let mut total_nnz = 0;
  let mut total_nodes = 0;
  for kind in PackedGateKind::ALL {
    let gate = PackedWordGate::new(9, kind).unwrap();
    let table = gate.r1cs();
    for matrix in [&table.a_0, &table.b_0] {
      let dd = diagram(matrix, table.k_log);
      assert_eq!(dd, diagram(matrix, table.k_log));
      total_nnz += dd.nonzero_entries();
      total_nodes += dd.nodes().len();
      let program = Program::DecisionDiagram(dd);
      for seed in [0, 1, 0xf891_1413_d980_b175, u64::MAX] {
        let row = point(table.k_log, seed);
        let col = point(table.k_log, seed.wrapping_add(471));
        let native =
          bilinear(&Weight::eq(row.clone()), &Weight::eq(col.clone()), matrix);
        assert_eq!(
          evaluate(
            &program,
            &row.into_iter().map(bytes).collect::<Vec<_>>(),
            &col.into_iter().map(bytes).collect::<Vec<_>>(),
          ),
          native,
          "{kind:?} seed {seed}"
        );
      }
    }
  }
  assert_eq!(total_nnz, 23_808);
  assert_eq!(total_nodes, 1_582);
  eprintln!(
    "candidate packed BLAKE3: 20 exact A/B diagrams, {total_nnz} nonzero entries, {total_nodes} retained nodes; not a full-relation cost"
  );
}

#[test]
#[ignore = "bounded complete R1CS/PLONK census of all candidate compression matrix roots; not Exec closure/proving"]
fn candidate_word_table_roots_have_value_independent_complete_component_census()
{
  use ix_fflonk::PlonkGateProjectionV1;
  use ix_terminal_circuit::{
    ConstraintPhase, R1csBuilder, R1csError, alloc_f128_private,
    constrain_f128_fixed_table, enforce_f128_equal,
  };
  const ROW_LIMIT: u64 = 50_000_000;
  let phase = ConstraintPhase::MatrixFold;
  let mut total_rows = 0;
  let mut total_constraints = 0;
  for kind in PackedGateKind::ALL {
    let table = PackedWordGate::new(9, kind).unwrap().r1cs();
    for (side, matrix) in [("A", &table.a_0), ("B", &table.b_0)] {
      let dd = diagram(matrix, table.k_log);
      let row = point(table.k_log, 0xf891_1413_d980_b175);
      let col = point(table.k_log, 471);
      let expected = bytes(bilinear(
        &Weight::eq(row.clone()),
        &Weight::eq(col.clone()),
        matrix,
      ));
      let mut first = None;
      for shape_only in [true, false] {
        let projection = PlonkGateProjectionV1::new();
        let observed = projection.clone();
        let mut observe = observed.observer();
        let observer = move |c: &ix_terminal_circuit::Constraint| {
          observe(c);
          let rows = observed
            .prefix()
            .map_err(|_| R1csError::InternalShape)?
            .constraint_rows;
          if rows > ROW_LIMIT {
            return Err(R1csError::ResourceLimit {
              resource: "packed BLAKE3 matrix component PLONK rows",
              limit: ROW_LIMIT,
              actual: rows,
            });
          }
          Ok(())
        };
        let mut builder = if shape_only {
          R1csBuilder::new_shape_projection_observed_fallible(observer)
        } else {
          R1csBuilder::new_projection_observed_fallible(observer)
        };
        let point = row
          .iter()
          .chain(&col)
          .map(|x| {
            alloc_f128_private(
              &mut builder,
              if shape_only { [0; 16] } else { bytes(*x) },
              phase,
            )
            .unwrap()
          })
          .collect::<Vec<_>>();
        let output =
          constrain_f128_fixed_table(&mut builder, &dd, &point, phase).unwrap();
        if !shape_only {
          assert_eq!(*output.value(), expected, "{kind:?} {side}");
        }
        let claim = alloc_f128_private(
          &mut builder,
          if shape_only { [0; 16] } else { expected },
          phase,
        )
        .unwrap();
        enforce_f128_equal(&mut builder, &output, &claim, phase);
        let r1cs = builder.finish_projection().unwrap();
        let plonk = projection.finish_for_sizing(&r1cs).unwrap();
        if let Some((shape, count)) = first.take() {
          assert_eq!(r1cs, shape, "{kind:?} {side} assigned/setup census");
          assert_eq!(plonk, count);
          total_rows += plonk.constraint_rows;
          total_constraints += r1cs.census().constraints;
          eprintln!(
            "packed BLAKE3 {kind:?} {side}: nnz={}, nodes={}, R1CS={}, PLONK={}; setup/assigned agree",
            dd.nonzero_entries(),
            dd.nodes().len(),
            r1cs.census().constraints,
            plonk.constraint_rows
          );
        } else {
          first = Some((r1cs, plonk));
        }
      }
    }
  }
  assert_eq!(total_constraints, 8_786_640);
  assert_eq!(total_rows, 14_121_316);
  eprintln!(
    "COMPLETE candidate compression A/B components: {total_constraints} R1CS constraints, {total_rows} PLONK rows, 20 distinct point/claim bindings; no structure/jagged/PCS/transcript census, no whole relation/key/proof"
  );
}

#[test]
#[ignore = "materialized representative candidate lane-table root; not a complete Exec relation"]
fn candidate_lane_table_materialization_constrains_all_claim_bits() {
  use ark_bls12_381::Fr;
  use ark_ff::Field;
  use ix_terminal_circuit::{
    ConstraintPhase, R1csBuilder, alloc_f128_private,
    constrain_f128_fixed_table, enforce_f128_equal,
  };
  let table =
    PackedWordGate::new(9, PackedGateKind::LanesLeft1).unwrap().r1cs();
  let dd = diagram(&table.a_0, table.k_log);
  let mut identity = None;
  for seed in [0, 0xf891_1413_d980_b175] {
    let row = point(table.k_log, seed);
    let col = point(table.k_log, seed.wrapping_add(471));
    let expected = bytes(bilinear(
      &Weight::eq(row.clone()),
      &Weight::eq(col.clone()),
      &table.a_0,
    ));
    let phase = ConstraintPhase::MatrixFold;
    let mut builder = R1csBuilder::new();
    let point = row
      .iter()
      .chain(&col)
      .map(|x| alloc_f128_private(&mut builder, bytes(*x), phase).unwrap())
      .collect::<Vec<_>>();
    let result =
      constrain_f128_fixed_table(&mut builder, &dd, &point, phase).unwrap();
    assert_eq!(*result.value(), expected);
    let claim = alloc_f128_private(&mut builder, expected, phase).unwrap();
    enforce_f128_equal(&mut builder, &result, &claim, phase);
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    for bit in claim.bit_variables() {
      let mut wrong = witness.clone();
      wrong
        .set(*bit, Fr::ONE - wrong.assignment()[bit.index() as usize])
        .unwrap();
      assert!(r1cs.check(&wrong).is_err());
    }
    if let Some(digest) = identity {
      assert_eq!(r1cs.digest(), digest);
    } else {
      identity = Some(r1cs.digest());
    }
    eprintln!(
      "candidate lane table actual materialization: {:?}, 128 claim-bit negatives",
      r1cs.census()
    );
  }
}
