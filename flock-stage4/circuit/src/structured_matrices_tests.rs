use super::*;
use crate::{
  F128StructuredWeightVariablesV1, R1csShapeLimitsV0, alloc_f128_private,
  f128::{native_f128_add as add, native_f128_multiply as multiply},
};
use ark_bls12_381::Fr;
use ark_ff::Field;
use ix_stage4_trace::{
  F128MatrixSideV1, F128StaticMatrixIdV1, F128StructuredMatricesLimitsV0,
};

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;

fn sources() -> Vec<(F128StaticMatrixIdV1, Vec<(u32, u32)>)> {
  let entries = vec![(0, 0), (1, 1), (2, 0), (3, 1)];
  [entries.clone(), vec![(0, 1), (1, 0)], entries, vec![]]
    .into_iter()
    .enumerate()
    .map(|(table, entries)| {
      (
        F128StaticMatrixIdV1 {
          registry_digest: [13; 32],
          table: table as u64,
          side: F128MatrixSideV1::A,
          variables: if table == 1 { 1 } else { 2 },
        },
        entries,
      )
    })
    .collect()
}

fn program() -> F128StructuredMatricesV0 {
  F128StructuredMatricesV0::compile(
    1,
    sources(),
    F128StructuredMatricesLimitsV0 {
      tables: 4,
      source_entries: 100,
      blocks: 100,
      coefficient_terms: 100,
      shared_nodes: 100,
      temporary_nodes: 100,
    },
  )
  .unwrap()
}

// Literal sparse bilinear sum, independent of the shared compiler/evaluator.
fn weight(index: u32, low: &[[u8; 16]], point: &[[u8; 16]]) -> [u8; 16] {
  point.iter().enumerate().fold(low[(index & 1) as usize], |v, (bit, &x)| {
    multiply(
      v,
      if (index >> (bit + 1)) & 1 == 0 {
        add(x, 1u128.to_le_bytes())
      } else {
        x
      },
    )
  })
}

fn fixture(
  builder: &mut R1csBuilder,
  seed: u128,
) -> Vec<F128DeferredMatrixClaimVariablesV1> {
  let raw: [[u8; 16]; 6] = core::array::from_fn(|i| {
    seed
      .wrapping_mul(i as u128 + 3)
      .rotate_left(u32::try_from(i).unwrap() * 7)
      .to_le_bytes()
  });
  let inputs = raw.map(|v| alloc_f128_private(builder, v, PHASE).unwrap());
  sources()
    .iter()
    .map(|(matrix, entries)| {
      let high = matrix.variables as usize - 1;
      let value = entries.iter().fold([0; 16], |sum, &(row, column)| {
        add(
          sum,
          multiply(
            weight(row, &raw[..2], &raw[4..4 + high]),
            weight(column, &raw[2..4], &raw[5..5 + high]),
          ),
        )
      });
      F128DeferredMatrixClaimVariablesV1 {
        matrix: *matrix,
        row: F128StructuredWeightVariablesV1 {
          low: inputs[..2].to_vec(),
          point: inputs[4..4 + high].to_vec(),
        },
        column: F128StructuredWeightVariablesV1 {
          low: inputs[2..4].to_vec(),
          point: inputs[5..5 + high].to_vec(),
        },
        value: alloc_f128_private(builder, value, PHASE).unwrap(),
      }
    })
    .collect()
}

#[test]
fn original_claims_match_literal_and_every_claim_and_output_bit_is_bound() {
  let program = program();
  let mut shape = None;
  for seed in [0, 0x72c9_71af_e48a_8951_917a_d89f_283a_1997] {
    let mut builder = R1csBuilder::new();
    let claims = fixture(&mut builder, seed);
    let outputs = constrain_f128_structured_matrix_claims(
      &mut builder,
      &program,
      &claims,
      PHASE,
    )
    .unwrap();
    for (output, claim) in outputs.iter().zip(&claims) {
      assert_eq!(output.value(), claim.value.value());
    }
    // Identical matrices really share the same result wires.
    assert_eq!(outputs[0].bit_variables(), outputs[2].bit_variables());
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    for value in claims.iter().map(|c| &c.value).chain(&outputs) {
      for &bit in value.bit_variables() {
        let mut bad = witness.clone();
        bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
        assert!(r1cs.check(&bad).is_err(), "unbound bit {bit:?}");
      }
    }
    let mut setup = R1csBuilder::new_shape(R1csShapeLimitsV0 {
      variables: 100_000,
      constraints: 100_000,
      nonzero_terms: 1_000_000,
    })
    .unwrap();
    let dummy = fixture(&mut setup, 0);
    constrain_f128_structured_matrix_claims(
      &mut setup, &program, &dummy, PHASE,
    )
    .unwrap();
    assert_eq!(setup.finish_shape().unwrap(), r1cs);
    if let Some(digest) = shape {
      assert_eq!(r1cs.digest(), digest);
    } else {
      shape = Some(r1cs.digest());
    }
  }
}

#[test]
fn missing_reordered_foreign_malformed_and_equal_valued_unshared_claims_refuse_before_emission()
 {
  let program = program();
  let mut baseline = R1csBuilder::new_projection();
  fixture(&mut baseline, 0);
  alloc_f128_private(&mut baseline, [0; 16], PHASE).unwrap();
  let baseline = baseline.finish_projection().unwrap();
  for case in 0..19 {
    let mut builder = R1csBuilder::new_projection();
    let mut claims = fixture(&mut builder, 0);
    // Equal value, DISTINCT wires. Sharing must not be justified by values.
    let spare = alloc_f128_private(&mut builder, [0; 16], PHASE).unwrap();
    match case {
      0 => {
        claims.pop();
      },
      1 => claims.swap(0, 1),
      2 => claims.push(claims[0].clone()),
      3 => claims[2].matrix.registry_digest[0] ^= 1,
      4 => claims[2].matrix.table += 9,
      5 => claims[2].matrix.side = F128MatrixSideV1::B,
      6 => claims[2].matrix.variables += 1,
      7 => {
        claims[2].row.low.pop();
      },
      8 => {
        claims[2].column.low.pop();
      },
      9 => {
        claims[2].row.point.pop();
      },
      10 => {
        claims[2].column.point.pop();
      },
      11 => claims[2].row.point.push(spare),
      12 => claims[2].column.point.push(spare),
      13 => claims[2].row.low[0] = spare,
      14 => claims[2].column.low[0] = spare,
      15 => claims[2].row.point[0] = spare,
      16 => claims[2].column.point[0] = spare,
      17 => {
        claims[0].row.point.pop();
      },
      18 => claims.clear(),
      _ => unreachable!(),
    }
    assert_eq!(
      constrain_f128_structured_matrix_claims(
        &mut builder,
        &program,
        &claims,
        PHASE
      ),
      Err(R1csError::InternalShape),
      "case {case}",
    );
    assert_eq!(builder.finish_projection().unwrap(), baseline, "case {case}");
  }
}

#[test]
fn false_claim_is_rejected_by_constraints_and_raw_dimensions_are_checked() {
  let program = program();
  for index in 0..program.outputs().len() {
    let mut builder = R1csBuilder::new();
    let mut claims = fixture(&mut builder, 0);
    claims[index].value =
      alloc_f128_private(&mut builder, [1; 16], PHASE).unwrap();
    constrain_f128_structured_matrix_claims(
      &mut builder,
      &program,
      &claims,
      PHASE,
    )
    .unwrap();
    assert!(matches!(builder.finish(), Err(R1csError::Unsatisfied { .. })));
  }
  for malformed in 0..4 {
    let mut builder = R1csBuilder::new_projection();
    let mut claims = fixture(&mut builder, 0);
    let mut shared = claims.remove(0);
    match malformed {
      0 => {
        shared.row.low.pop();
      },
      1 => {
        shared.column.low.pop();
      },
      2 => {
        shared.row.point.pop();
      },
      3 => {
        shared.column.point.pop();
      },
      _ => unreachable!(),
    }
    assert_eq!(
      constrain_f128_structured_matrices(
        &mut builder,
        &program,
        &shared.row.low,
        &shared.column.low,
        &shared.row.point,
        &shared.column.point,
        PHASE,
      ),
      Err(R1csError::InternalShape),
    );
  }
}
