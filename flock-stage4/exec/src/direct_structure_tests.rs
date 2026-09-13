//! Exact original structure-claim component differential and bounded census.
//! This is not the whole Exec relation, a terminal key, or a proof.

use super::{
  capacity_tests::SMALL,
  closure_tests::{LIMITS, decode, evaluate},
  memory_summary,
};
use flock_prover::{
  circuit::SigmaAssertion,
  field::F128,
  matrix_fold::{Weight, bilinear},
};
use ix_stage4_trace::{F128FixedMatrixProgramV0, F128FixedTableBasisV0};
use ixby_flock::{
  blake3_backend::Blake3Backend,
  ixby::{
    decode::PrimitiveSet,
    exec::{SemanticProfile, compile_exec_profile_with_backend},
  },
};
use std::time::Instant;

fn bytes(v: F128) -> [u8; 16] {
  (u128::from(v.lo) | (u128::from(v.hi) << 64)).to_le_bytes()
}

#[test]
#[ignore = "bounded paired native differential and exact R1CS/PLONK census for all 3 original structure claims; not complete Exec/key/proof"]
fn packed_small_shared_original_structure_component_census() {
  use ix_fflonk::PlonkGateProjectionV1;
  use ix_terminal_circuit::{
    Constraint, ConstraintPhase, F128CircuitStructureClaimVariablesV1,
    R1csBuilder, R1csError, alloc_f128_constant, alloc_f128_private,
    constrain_f128_structure_original_claims,
  };
  let setup = compile_exec_profile_with_backend(
    SemanticProfile::scalar(SMALL).unwrap(),
    SMALL,
    PrimitiveSet::scalar(),
    Blake3Backend::PackedWordsV0,
  )
  .unwrap();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let tables =
    crate::compile_exec_root_tables(&replay, LIMITS.diagrams).unwrap();
  let (id, source) = tables.structure();
  let table =
    F128FixedTableBasisV0::compile(source, LIMITS.structure_basis).unwrap();
  assert_eq!(
    table,
    F128FixedTableBasisV0::compile(source, LIMITS.structure_basis).unwrap()
  );
  let program = F128FixedMatrixProgramV0::CofactorBasis(table.clone());
  let shape = setup.verifier_shape();
  let native = SigmaAssertion::matrix(&shape.circuit);
  let row_bits = id.row_variables as usize;
  let base_bits = id.column_variables as usize - 3;
  let active_base = replay.wiring.rho_challenges.len() - row_bits;
  assert!(active_base <= base_bits);
  let seed = 0x812a_9473_a34f_1f81_0ea6_1769_093b_4127u128;
  let rho = (0..replay.wiring.rho_challenges.len())
    .map(|i| {
      let v = seed
        .wrapping_mul(i as u128 + 7)
        .rotate_left(u32::try_from(i).unwrap() * 11);
      decode(&v.to_le_bytes())
    })
    .collect::<Vec<_>>();
  let row = &rho[..row_bits];
  let columns = (0..3)
    .map(|plane| {
      let mut col = rho[row_bits..].to_vec();
      col.resize(base_bits, F128::ZERO);
      col.extend((0..3).map(|bit| {
        if (plane >> bit) & 1 == 0 { F128::ZERO } else { F128::ONE }
      }));
      col
    })
    .collect::<Vec<_>>();
  let expected = columns
    .iter()
    .map(|col| {
      let value =
        bilinear(&Weight::eq(row.to_vec()), &Weight::eq(col.clone()), &native);
      assert_eq!(
        evaluate(
          &program,
          &row.iter().copied().map(bytes).collect::<Vec<_>>(),
          &col.iter().copied().map(bytes).collect::<Vec<_>>()
        ),
        value
      );
      value
    })
    .collect::<Vec<_>>();
  // Also compare a fully general point so the test does not silently reduce
  // the approved source to planes 0..2 or omit its constant-wire pins.
  let arbitrary = (0..id.column_variables)
    .map(|i| F128::new(u64::from(i) + 83, 151))
    .collect::<Vec<_>>();
  assert_eq!(
    evaluate(
      &program,
      &row.iter().copied().map(bytes).collect::<Vec<_>>(),
      &arbitrary.iter().copied().map(bytes).collect::<Vec<_>>()
    ),
    bilinear(&Weight::eq(row.to_vec()), &Weight::eq(arbitrary), &native)
  );
  eprintln!(
    "shared structure: source={}, basis={}, source_entries={}, source_nodes={}, native all 3 original claims AND general 8-plane point PASS; {}",
    blake3::Hash::from(source.digest()),
    blake3::Hash::from(table.digest()),
    source.nonzero_entries(),
    source.nodes().len(),
    memory_summary()
  );
  let phase = ConstraintPhase::MatrixFold;
  let mut first = None;
  for shape_only in [true, false] {
    let started = Instant::now();
    let plonk = PlonkGateProjectionV1::new();
    let observed = plonk.clone();
    let mut observe = observed.observer();
    let observer = move |c: &Constraint| {
      observe(c);
      let rows = observed
        .prefix()
        .map_err(|_| R1csError::InternalShape)?
        .constraint_rows;
      if rows > 50_000_000 {
        return Err(R1csError::ResourceLimit {
          resource: "shared structure component PLONK rows",
          limit: 50_000_000,
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
    let rho = rho
      .iter()
      .map(|&v| {
        alloc_f128_private(
          &mut builder,
          if shape_only { [0; 16] } else { bytes(v) },
          phase,
        )
        .unwrap()
      })
      .collect::<Vec<_>>();
    let zero = alloc_f128_constant(&mut builder, [0; 16], phase).unwrap();
    let one =
      alloc_f128_constant(&mut builder, 1u128.to_le_bytes(), phase).unwrap();
    let claims = (0..3)
      .map(|plane| {
        let mut column_point = rho[row_bits..].to_vec();
        column_point.resize(base_bits, zero.clone());
        column_point.extend((0..3).map(|bit| {
          if (plane >> bit) & 1 == 0 { zero.clone() } else { one.clone() }
        }));
        F128CircuitStructureClaimVariablesV1 {
          matrix: *id,
          row_point: rho[..row_bits].to_vec(),
          column_point,
          value: alloc_f128_private(
            &mut builder,
            if shape_only { [0; 16] } else { bytes(expected[plane]) },
            phase,
          )
          .unwrap(),
        }
      })
      .collect::<Vec<_>>();
    let outputs = constrain_f128_structure_original_claims(
      &mut builder,
      *id,
      &table,
      &claims,
      phase,
    )
    .unwrap();
    if !shape_only {
      for (output, &expected) in outputs.iter().zip(&expected) {
        assert_eq!(*output.value(), bytes(expected));
      }
    }
    let r1cs = builder.finish_projection().unwrap();
    let plonk = plonk.finish_for_sizing(&r1cs).unwrap();
    eprintln!(
      "COMPLETE all 3 original structure claims shape_only={shape_only}: R1CS={}, PLONK={}, projection={}; {:.3}s; {}. COMPONENT ONLY, no full Exec/key/proof.",
      r1cs.census().constraints,
      plonk.constraint_rows,
      blake3::Hash::from(r1cs.digest()),
      started.elapsed().as_secs_f64(),
      memory_summary()
    );
    if let Some((shape, count)) = first.take() {
      assert_eq!(r1cs, shape);
      assert_eq!(plonk, count);
    } else {
      first = Some((r1cs, plonk));
    }
  }
}
