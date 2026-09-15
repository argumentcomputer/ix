use super::*;
use crate::{
  F128JaggedClaimVariablesV1, F128JaggedComboTermVariablesV1,
  R1csShapeLimitsV0, alloc_f128_private,
  f128::{native_f128_add as add, native_f128_multiply as mul},
};
use ark_bls12_381::Fr;
use ark_ff::Field;
use ix_stage4_trace::{F128JaggedDirectLimitsV0, F128JaggedMatrixIdV1};

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;
const ADDRESSES: [u32; 3] = [1, 0, 1];

fn table() -> F128JaggedDirectTableV0 {
  F128JaggedDirectTableV0::compile(
    F128JaggedMatrixIdV1 {
      circuit_digest: [13; 32],
      row_variables: 1,
      column_variables: 2,
    },
    [(0, 0, 1), (0, 1, 1)],
    ADDRESSES,
    F128JaggedDirectLimitsV0 {
      runs: 2,
      combo_terms: 3,
      row_nodes: 100,
      equality_nodes: 100,
    },
  )
  .unwrap()
}

fn eq(index: u32, point: &[[u8; 16]]) -> [u8; 16] {
  point.iter().enumerate().fold(1u128.to_le_bytes(), |v, (bit, &x)| {
    mul(
      v,
      if (index >> bit) & 1 == 0 { add(1u128.to_le_bytes(), x) } else { x },
    )
  })
}

fn fixture(
  builder: &mut R1csBuilder,
  seed: u128,
) -> F128JaggedAssertionVariablesV1 {
  let raw: [[u8; 16]; 9] = core::array::from_fn(|i| {
    seed
      .wrapping_mul(i as u128 + 3)
      .rotate_left(u32::try_from(i).unwrap() * 7)
      .to_le_bytes()
  });
  let input = raw.map(|v| alloc_f128_private(builder, v, PHASE).unwrap());
  let mut claims = Vec::new();
  for index in 0..2 {
    // Independently sum the two actual sparse rows, with their literal pair
    // indices 0 and 2 (right endpoint is the odd interleaved coordinate).
    let mut expected = [0; 16];
    for row in 0..2 {
      expected = add(
        expected,
        mul(
          mul(raw[4 + index], eq(row, &raw[2 + index..3 + index])),
          eq(2 * row, &raw[..2]),
        ),
      );
    }
    claims.push(F128JaggedClaimVariablesV1 {
      row: F128JaggedRowWeightVariablesV1::Eq {
        scale: Box::new(input[4 + index].clone()),
        point: vec![input[2 + index].clone()],
      },
      column_point: input[..2].to_vec(),
      value: alloc_f128_private(builder, expected, PHASE).unwrap(),
    });
  }
  let mut expected = [0; 16];
  let terms = ADDRESSES
    .iter()
    .enumerate()
    .map(|(index, &address)| {
      expected = add(expected, mul(raw[6 + index], eq(2 * address, &raw[..2])));
      F128JaggedComboTermVariablesV1 {
        coefficient: input[6 + index].clone(),
        address,
      }
    })
    .collect();
  claims.push(F128JaggedClaimVariablesV1 {
    row: F128JaggedRowWeightVariablesV1::Combo { terms },
    column_point: input[..2].to_vec(),
    value: alloc_f128_private(builder, expected, PHASE).unwrap(),
  });
  F128JaggedAssertionVariablesV1 { matrix: table().matrix(), claims }
}

#[test]
fn both_scaled_eqs_and_every_combo_term_match_literal_and_bind_all_outputs() {
  let table = table();
  let mut shape = None;
  for seed in [0, 0x7a97_51e0_f137_8690_abc4_9be2_8974_61c3] {
    let mut builder = R1csBuilder::new();
    let assertion = fixture(&mut builder, seed);
    let outputs =
      constrain_f128_jagged_direct(&mut builder, &table, &assertion, PHASE)
        .unwrap();
    for (output, claim) in outputs.iter().zip(&assertion.claims) {
      assert_eq!(output.value(), claim.value.value());
    }
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    for value in outputs.iter().chain(assertion.claims.iter().map(|c| &c.value))
    {
      for &bit in value.bit_variables() {
        let mut bad = witness.clone();
        bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
        assert!(r1cs.check(&bad).is_err(), "unbound output {bit:?}");
      }
    }
    let mut setup = R1csBuilder::new_shape(R1csShapeLimitsV0 {
      variables: 100_000,
      constraints: 100_000,
      nonzero_terms: 1_000_000,
    })
    .unwrap();
    let dummy = fixture(&mut setup, 0);
    constrain_f128_jagged_direct(&mut setup, &table, &dummy, PHASE).unwrap();
    assert_eq!(setup.finish_shape().unwrap(), r1cs);
    if let Some(digest) = shape {
      assert_eq!(r1cs.digest(), digest);
    } else {
      shape = Some(r1cs.digest());
    }
  }
}

#[test]
fn false_original_claims_fail_r1cs_without_a_host_acceptance_check() {
  let table = table();
  for index in 0..3 {
    let mut builder = R1csBuilder::new();
    let mut assertion = fixture(&mut builder, 0);
    assertion.claims[index].value =
      alloc_f128_private(&mut builder, [1; 16], PHASE).unwrap();
    constrain_f128_jagged_direct(&mut builder, &table, &assertion, PHASE)
      .unwrap();
    assert!(matches!(builder.finish(), Err(R1csError::Unsatisfied { .. })));
  }
}

#[test]
fn missing_foreign_reordered_malformed_or_equal_valued_unshared_claims_refuse_before_emission()
 {
  let table = table();
  let mut baseline = R1csBuilder::new_projection();
  fixture(&mut baseline, 0);
  alloc_f128_private(&mut baseline, [0; 16], PHASE).unwrap();
  let baseline = baseline.finish_projection().unwrap();
  for case in 0..18 {
    let mut builder = R1csBuilder::new_projection();
    let mut assertion = fixture(&mut builder, 0);
    let spare = alloc_f128_private(&mut builder, [0; 16], PHASE).unwrap();
    match case {
      0 => assertion.matrix.circuit_digest[0] ^= 1,
      1 => assertion.matrix.row_variables += 1,
      2 => assertion.matrix.column_variables += 2,
      3 => {
        assertion.claims.pop();
      },
      4 => assertion.claims.push(assertion.claims[0].clone()),
      5 => assertion.claims.clear(),
      6 => assertion.claims.swap(0, 2),
      7 => {
        assertion.claims[0].column_point.pop();
      },
      8 => {
        assertion.claims[1].column_point.pop();
      },
      9 => assertion.claims[2].column_point.push(spare),
      10 => assertion.claims[1].column_point[0] = spare,
      11 => assertion.claims[2].column_point[1] = spare,
      12 | 13 => {
        let F128JaggedRowWeightVariablesV1::Eq { point, .. } =
          &mut assertion.claims[case - 12].row
        else {
          unreachable!()
        };
        point.pop();
      },
      14..=17 => {
        let F128JaggedRowWeightVariablesV1::Combo { terms } =
          &mut assertion.claims[2].row
        else {
          unreachable!()
        };
        match case {
          14 => {
            terms.pop();
          },
          15 => terms.push(terms[0].clone()),
          16 => terms.swap(0, 1),
          17 => terms[0].address = 2,
          _ => unreachable!(),
        }
      },
      _ => unreachable!(),
    }
    assert_eq!(
      constrain_f128_jagged_direct(&mut builder, &table, &assertion, PHASE),
      Err(R1csError::InternalShape),
      "case {case}"
    );
    assert_eq!(builder.finish_projection().unwrap(), baseline, "case {case}");
  }
}
