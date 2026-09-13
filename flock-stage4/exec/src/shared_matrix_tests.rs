//! Original-claim structured-matrix prototype: fixed setup geometry, native
//! differentials and an exact circuit COMPONENT census, not full Exec closure.

#[path = "shared_matrix_order_tests.rs"]
mod order_tests;

#[path = "shared_matrix_span_tests.rs"]
mod span_tests;

use super::{capacity_tests::SMALL, closure_tests::decode, memory_summary};
use flock_prover::{
  field::F128,
  matrix_fold::{Weight, bilinear},
};
use ix_stage4_trace::{
  F128MatrixSideV1, F128StructuredMatricesLimitsV0, F128StructuredMatricesV0,
  F128StructuredMatrixNodeV0,
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

fn compile(replay: &crate::CompiledExecReplay<'_>) -> F128StructuredMatricesV0 {
  let claims = &replay.boolean.trace.deferred_matrix_claims;
  assert_eq!(claims.len(), 64);
  let shared = claims.iter().max_by_key(|c| c.matrix.variables).unwrap();
  assert_eq!(shared.row.low.len(), 64);
  assert_eq!(shared.column.low.len(), 64);
  let sources = claims.iter().map(|c| {
    // These are symbolic references, not observed/private field values.
    let high = c.matrix.variables as usize - 6;
    assert_eq!(c.row.low, shared.row.low);
    assert_eq!(c.column.low, shared.column.low);
    assert_eq!(c.row.point, shared.row.point[..high]);
    assert_eq!(c.column.point, shared.column.point[..high]);
    let ty = &replay.setup.verifier_shape().registry.boolean_types()
      [usize::try_from(c.matrix.table).unwrap()];
    assert_eq!(c.matrix.registry_digest, replay.setup.identities().registry);
    assert_eq!(c.matrix.variables as usize, ty.k_log);
    let matrix = match c.matrix.side {
      F128MatrixSideV1::A => &ty.a_0,
      F128MatrixSideV1::B => &ty.b_0,
    };
    (
      c.matrix,
      matrix.rows.iter().enumerate().flat_map(|(row, columns)| {
        columns.iter().map(move |&column| {
          (u32::try_from(row).unwrap(), u32::try_from(column).unwrap())
        })
      }),
    )
  });
  F128StructuredMatricesV0::compile(
    6,
    sources,
    F128StructuredMatricesLimitsV0 {
      tables: 64,
      source_entries: 2_000_000,
      blocks: 100_000,
      coefficient_terms: 2_000_000,
      shared_nodes: 1_000_000,
      temporary_nodes: 1_000_000,
    },
  )
  .unwrap()
}

fn inputs(program: &F128StructuredMatricesV0, seed: u128) -> [Vec<F128>; 4] {
  core::array::from_fn(|part| {
    let len = if part < 2 { 64 } else { program.high_variables() as usize };
    (0..len)
      .map(|index| {
        let value = seed
          .wrapping_mul((part * 179 + index + 3) as u128)
          .rotate_left(u32::try_from(index).unwrap() * 7);
        decode(&value.to_le_bytes())
      })
      .collect()
  })
}

fn expected(
  setup: &CompiledExec,
  program: &F128StructuredMatricesV0,
  input: &[Vec<F128>; 4],
) -> Vec<F128> {
  program
    .outputs()
    .iter()
    .map(|(id, _)| {
      let high = id.variables as usize - 6;
      let ty = &setup.verifier_shape().registry.boolean_types()
        [usize::try_from(id.table).unwrap()];
      let matrix = match id.side {
        F128MatrixSideV1::A => &ty.a_0,
        F128MatrixSideV1::B => &ty.b_0,
      };
      bilinear(
        &Weight::low_eq(input[0].clone(), input[2][..high].to_vec()),
        &Weight::low_eq(input[1].clone(), input[3][..high].to_vec()),
        matrix,
      )
    })
    .collect()
}

fn evaluate(
  program: &F128StructuredMatricesV0,
  input: &[Vec<F128>; 4],
) -> Vec<F128> {
  let blocks = program
    .blocks()
    .iter()
    .map(|pairs| {
      pairs.iter().fold(F128::ZERO, |v, &pair| {
        v + input[0][usize::from(pair) & 63] * input[1][usize::from(pair) >> 6]
      })
    })
    .collect::<Vec<_>>();
  let mut nodes = Vec::new();
  for node in program.nodes() {
    nodes.push(match *node {
      F128StructuredMatrixNodeV0::Zero => F128::ZERO,
      F128StructuredMatrixNodeV0::Block(i) => blocks[i as usize],
      F128StructuredMatrixNodeV0::Branch { column, bit, low, high } => {
        let x = input[if column { 3 } else { 2 }][bit as usize];
        nodes[low as usize] + x * (nodes[low as usize] + nodes[high as usize])
      },
    });
  }
  program.outputs().iter().map(|(_, root)| nodes[*root as usize]).collect()
}

fn bytes(value: F128) -> [u8; 16] {
  (u128::from(value.lo) | (u128::from(value.hi) << 64)).to_le_bytes()
}

#[test]
#[ignore = "bounded setup-owned shared matrix native differential; no R1CS census, key, proof or relation adoption"]
fn packed_small_shared_original_matrix_native_differential() {
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let started = Instant::now();
  let program = compile(&replay);
  assert_eq!(program, compile(&replay));
  for seed in [0, 1, 0x91ad_8481_abe7_fa10_2758_019a_68a4_19fe] {
    let input = inputs(&program, seed);
    assert_eq!(evaluate(&program, &input), expected(&setup, &program, &input));
  }
  eprintln!(
    "shared original 64 matrices: digest={}, pairs={}, {:?}, high_variables={}, native differential/rebuild PASS; {:.3}s; {}",
    blake3::Hash::from(program.digest()),
    program.pairs().len(),
    program.census(),
    program.high_variables(),
    started.elapsed().as_secs_f64(),
    memory_summary(),
  );
}

#[test]
#[ignore = "bounded 64 original matrix R1CS/PLONK component census with shared point wires; excludes all remaining replay/structure/jagged phases and is not a whole relation/key/proof"]
fn packed_small_shared_original_matrix_complete_component_census() {
  use ix_fflonk::PlonkGateProjectionV1;
  use ix_terminal_circuit::{
    Constraint, ConstraintPhase, F128DeferredMatrixClaimVariablesV1,
    F128StructuredWeightVariablesV1, R1csBuilder, R1csError,
    alloc_f128_private, constrain_f128_structured_matrix_claims,
  };
  const LIMIT: u64 = 750_000_000;
  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let program = compile(&replay);
  let input = inputs(&program, 0x91ad_8481_abe7_fa10_2758_019a_68a4_19fe);
  let expected = expected(&setup, &program, &input);
  assert_eq!(evaluate(&program, &input), expected);
  let mut first = None;
  for shape_only in [true, false] {
    let started = Instant::now();
    let plonk = PlonkGateProjectionV1::new();
    let observed = plonk.clone();
    let mut observe = observed.observer();
    let mut next_report = 10_000_000;
    let observer = move |c: &Constraint| {
      observe(c);
      let rows = observed
        .prefix()
        .map_err(|_| R1csError::InternalShape)?
        .constraint_rows;
      if rows >= next_report {
        eprintln!(
          "shared matrix component shape_only={shape_only}: {rows} PLONK rows, {:.3}s; {}",
          started.elapsed().as_secs_f64(),
          memory_summary()
        );
        next_report += 10_000_000;
      }
      if rows > LIMIT {
        return Err(R1csError::ResourceLimit {
          resource: "shared original matrix component PLONK rows",
          limit: LIMIT,
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
    let phase = ConstraintPhase::MatrixFold;
    let input = input
      .iter()
      .map(|part| {
        part
          .iter()
          .map(|&v| {
            alloc_f128_private(
              &mut builder,
              if shape_only { [0; 16] } else { bytes(v) },
              phase,
            )
            .unwrap()
          })
          .collect::<Vec<_>>()
      })
      .collect::<Vec<_>>();
    let claims = program
      .outputs()
      .iter()
      .zip(&expected)
      .map(|((id, _), &v)| {
        let high = id.variables as usize - 6;
        F128DeferredMatrixClaimVariablesV1 {
          matrix: *id,
          row: F128StructuredWeightVariablesV1 {
            low: input[0].clone(),
            point: input[2][..high].to_vec(),
          },
          column: F128StructuredWeightVariablesV1 {
            low: input[1].clone(),
            point: input[3][..high].to_vec(),
          },
          value: alloc_f128_private(
            &mut builder,
            if shape_only { [0; 16] } else { bytes(v) },
            phase,
          )
          .unwrap(),
        }
      })
      .collect::<Vec<_>>();
    let outputs = constrain_f128_structured_matrix_claims(
      &mut builder,
      &program,
      &claims,
      phase,
    )
    .unwrap();
    if !shape_only {
      for (v, &expected) in outputs.iter().zip(&expected) {
        assert_eq!(*v.value(), bytes(expected));
      }
    }
    let r1cs = builder.finish_projection().unwrap();
    let plonk = plonk.finish_for_sizing(&r1cs).unwrap();
    eprintln!(
      "COMPLETE shared original 64 matrices shape_only={shape_only}: program={}, pairs={}, {:?}, R1CS={}, PLONK={}, projection={}; {:.3}s; {}. COMPONENT ONLY: no transcript/PCS/structure/jagged/Exec claim binding/key/proof.",
      blake3::Hash::from(program.digest()),
      program.pairs().len(),
      program.census(),
      r1cs.census().constraints,
      plonk.constraint_rows,
      blake3::Hash::from(r1cs.digest()),
      started.elapsed().as_secs_f64(),
      memory_summary(),
    );
    if let Some((shape, count)) = first.take() {
      assert_eq!(r1cs, shape);
      assert_eq!(plonk, count);
    } else {
      first = Some((r1cs, plonk));
    }
  }
}
