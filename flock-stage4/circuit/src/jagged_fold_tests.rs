use super::*;
use crate::{F128JaggedComboTermVariablesV1, Variable, alloc_f128_private};
use ix_stage4_trace::{
  F128JaggedComboTermBindingV1, F128JaggedFoldClaimBindingV1,
};

// A dimension-zero fold exercises both row-weight encodings and their exact
// digest/header/scale/address/value bindings. Other tests cover round gadgets
// and the nonconstant jagged table evaluator; this is not a full Exec proof.
fn trace(combo: bool) -> F128JaggedAccumulatorTraceV1 {
  let value = if combo { 4 } else { 3 };
  F128JaggedAccumulatorTraceV1 {
    matrix: F128JaggedMatrixIdV1 {
      circuit_digest: [9; 32],
      row_variables: 0,
      column_variables: 0,
    },
    circuit_digest_payload: 0,
    shape_observation: 0,
    claims: vec![F128JaggedFoldClaimBindingV1 {
      claim: 0,
      row: if combo {
        F128JaggedRowBindingV1::Combo {
          header_observation: 1,
          terms: vec![F128JaggedComboTermBindingV1 {
            coefficient_observation: 2,
            address_observation: 3,
            address: 0,
          }],
        }
      } else {
        F128JaggedRowBindingV1::Eq {
          header_observation: 1,
          scale_observation: 2,
          point_observations: vec![],
        }
      },
      column_point_observations: vec![],
      value_observation: value,
    }],
    lambda_challenges: vec![0],
    column_rounds: vec![],
    bridge_observations: vec![value + 1],
    mu_challenges: vec![1],
    row_rounds: vec![],
    value_observation: value + 2,
  }
}

fn emit(
  builder: &mut R1csBuilder,
  trace: &F128JaggedAccumulatorTraceV1,
  seed: u64,
  zero_scratch: bool,
) -> Result<Vec<Variable>, F128JaggedAccumulatorCircuitError> {
  let combo =
    matches!(trace.claims[0].row, F128JaggedRowBindingV1::Combo { .. });
  let root = f128_from_u64s(seed, 17);
  let scale = f128_from_u64s(seed + 1, 3);
  let value = crate::f128::native_f128_multiply(scale, root);
  let source = |bytes| if zero_scratch { [0; 16] } else { bytes };
  let scale = alloc_f128_private(builder, source(scale), PHASE)?;
  let value_variables = alloc_f128_private(builder, source(value), PHASE)?;
  let claim = F128JaggedClaimVariablesV1 {
    row: if combo {
      F128JaggedRowWeightVariablesV1::Combo {
        terms: vec![F128JaggedComboTermVariablesV1 {
          coefficient: scale,
          address: 0,
        }],
      }
    } else {
      F128JaggedRowWeightVariablesV1::Eq {
        scale: Box::new(scale),
        point: vec![],
      }
    },
    column_point: vec![],
    value: value_variables,
  };
  let mut observations = vec![
    f128_from_u64s(0, 1),
    if combo { f128_from_u64s(1, 1) } else { [0; 16] },
    f128_from_u64s(seed + 1, 3),
  ];
  if combo {
    observations.push([0; 16]);
  }
  observations.extend([value, value, root]);
  let observations = observations
    .into_iter()
    .map(|word| alloc_f128_private(builder, source(word), PHASE))
    .collect::<Result<Vec<_>, _>>()?;
  let challenges = [f128_from_u64s(11, seed), f128_from_u64s(13, seed)]
    .map(|word| alloc_f128_private(builder, source(word), PHASE))
    .into_iter()
    .collect::<Result<Vec<_>, _>>()?;
  let digests = [[9; 16]; 2]
    .map(|word| alloc_f128_private(builder, source(word), PHASE))
    .into_iter()
    .collect::<Result<Vec<_>, _>>()?;
  let payloads = vec![
    digests.iter().map(F128TranscriptWordV1::from_f128_variables).collect(),
  ];
  let assertion = F128JaggedAssertionVariablesV1 {
    matrix: trace.matrix,
    claims: vec![claim],
  };
  let output = constrain_f128_jagged_accumulator(
    builder,
    trace,
    F128JaggedAccumulatorCircuitInputsV1 {
      assertion: &assertion,
      observed_values: &observations,
      byte_payloads: &payloads,
      challenges: &challenges,
    },
  )?;
  Ok(
    output
      .root_claim
      .value
      .bit_variables()
      .iter()
      .copied()
      .chain(observations.iter().map(|word| word.bit_variables()[0]))
      .chain(digests.iter().map(|word| word.bit_variables()[0]))
      .collect(),
  )
}

#[test]
fn setup_jagged_fold_retains_both_row_encodings_and_all_bindings() {
  for combo in [false, true] {
    let trace = trace(combo);
    let mut builder = crate::r1cs::test_shape_builder();
    let targets = emit(&mut builder, &trace, 0, true).unwrap();
    let shape = builder.finish_shape().unwrap();
    for seed in [1, 11, 31] {
      let mut builder = R1csBuilder::new();
      assert_eq!(emit(&mut builder, &trace, seed, false).unwrap(), targets);
      let (assigned, witness) = builder.finish().unwrap();
      assert_eq!(shape, assigned);
      shape.check(&witness).unwrap();
      for &bit in &targets {
        let mut bad = witness.clone();
        bad
          .set(bit, Fr::ONE - witness.assignment()[bit.index() as usize])
          .unwrap();
        assert!(shape.check(&bad).is_err());
      }
    }
    assert!(matches!(
      emit(&mut R1csBuilder::new(), &trace, 0, true),
      Err(F128JaggedAccumulatorCircuitError::DigestPayloadMismatch { .. })
    ));
    let mut bad = trace;
    bad.lambda_challenges.clear();
    assert!(matches!(
      emit(&mut crate::r1cs::test_shape_builder(), &bad, 0, true),
      Err(F128JaggedAccumulatorCircuitError::InvalidTrace(_))
    ));
  }
}
