use super::*;
use crate::{
  R1csShapeLimitsV0, alloc_f128_private,
  f128::{native_f128_add as add, native_f128_multiply as mul},
};
use ark_bls12_381::Fr;
use ark_ff::Field;
use ix_stage4_trace::{
  F128FixedTableBasisLimitsV0, F128FixedTableLimitsV0, F128FixedTableV0,
};

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;
const ENTRIES: [(u64, [u8; 16]); 8] = [
  (0, [0x17; 16]),
  (1, [0x72; 16]),
  (2, [0x81; 16]),
  (3, [0x39; 16]),
  (4, [0x91; 16]),
  (9, [0x29; 16]),
  (20, [0x13; 16]),
  (21, [0x49; 16]),
];

fn matrix() -> F128CircuitStructureMatrixIdV1 {
  F128CircuitStructureMatrixIdV1 {
    circuit_digest: [43; 32],
    row_variables: 1,
    column_variables: 4,
  }
}

fn compile(
  order: &[u32],
  entries: &[(u64, [u8; 16])],
) -> F128FixedTableBasisV0 {
  let table = F128FixedTableV0::compile(
    order,
    entries.iter().copied(),
    F128FixedTableLimitsV0 { entries: 100, nodes: 1000 },
  )
  .unwrap();
  F128FixedTableBasisV0::compile(
    &table,
    F128FixedTableBasisLimitsV0 {
      state_slots: 1000,
      dense_words: 10000,
      word_operations: 100000,
      coefficient_terms: 10000,
    },
  )
  .unwrap()
}

fn literal(entries: &[(u64, [u8; 16])], point: &[[u8; 16]]) -> [u8; 16] {
  entries.iter().fold([0; 16], |sum, &(index, value)| {
    add(
      sum,
      point.iter().enumerate().fold(value, |v, (bit, &x)| {
        mul(
          v,
          if (index >> bit) & 1 == 0 { add(x, 1u128.to_le_bytes()) } else { x },
        )
      }),
    )
  })
}

fn fixture(
  builder: &mut R1csBuilder,
  seed: u128,
) -> Vec<F128CircuitStructureClaimVariablesV1> {
  let raw: [[u8; 16]; 4] = core::array::from_fn(|i| {
    seed
      .wrapping_mul(i as u128 + 3)
      .rotate_left(u32::try_from(i).unwrap() * 11)
      .to_le_bytes()
  });
  let wires = raw.map(|v| alloc_f128_private(builder, v, PHASE).unwrap());
  (0..3)
    .map(|plane| {
      let indices = [
        0,
        1,
        if plane == 1 { 3 } else { 2 },
        if plane == 2 { 3 } else { 2 },
        2,
      ];
      let expected = literal(&ENTRIES, &indices.map(|i| raw[i]));
      let point = indices.map(|i| wires[i].clone());
      F128CircuitStructureClaimVariablesV1 {
        matrix: matrix(),
        row_point: point[..1].to_vec(),
        column_point: point[1..].to_vec(),
        value: alloc_f128_private(builder, expected, PHASE).unwrap(),
      }
    })
    .collect()
}

#[test]
fn all_three_structure_values_match_literal_and_every_output_bit_is_bound() {
  let table = compile(&[4, 3, 2, 1, 0], &ENTRIES);
  let mut first = None;
  for seed in [0, 0x937a_5b91_9942_1367_cfff_0191_a395_6103] {
    let mut builder = R1csBuilder::new();
    let claims = fixture(&mut builder, seed);
    let outputs = constrain_f128_structure_original_claims(
      &mut builder,
      matrix(),
      &table,
      &claims,
      PHASE,
    )
    .unwrap();
    for (output, claim) in outputs.iter().zip(&claims) {
      assert_eq!(output.value(), claim.value.value());
    }
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    for value in outputs.iter().chain(claims.iter().map(|c| &c.value)) {
      for &bit in value.bit_variables() {
        let mut bad = witness.clone();
        bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
        assert!(r1cs.check(&bad).is_err());
      }
    }
    let mut shape = R1csBuilder::new_shape(R1csShapeLimitsV0 {
      variables: 1_000_000,
      constraints: 1_000_000,
      nonzero_terms: 10_000_000,
    })
    .unwrap();
    let dummy = fixture(&mut shape, 0);
    constrain_f128_structure_original_claims(
      &mut shape,
      matrix(),
      &table,
      &dummy,
      PHASE,
    )
    .unwrap();
    assert_eq!(shape.finish_shape().unwrap(), r1cs);
    if let Some(digest) = first {
      assert_eq!(r1cs.digest(), digest);
    } else {
      first = Some(r1cs.digest());
    }
  }
}

#[test]
fn sharing_uses_complete_suffix_wire_identity_not_equal_assignments() {
  let table = compile(&[4, 3, 2, 1, 0], &ENTRIES);
  let mut counts = Vec::new();
  for shared in [true, false] {
    let mut builder = R1csBuilder::new_projection();
    let wires = (0..5)
      .map(|i| alloc_f128_private(&mut builder, [i + 17; 16], PHASE).unwrap())
      .collect::<Vec<_>>();
    // Allocate the SAME input count in either case. Unshared points have
    // exactly the same values, but independent bit wires at every coordinate.
    let duplicates = (0..3)
      .map(|_| {
        wires
          .iter()
          .map(|v| alloc_f128_private(&mut builder, *v.value(), PHASE).unwrap())
          .collect::<Vec<_>>()
      })
      .collect::<Vec<_>>();
    let points = if shared { vec![wires; 3] } else { duplicates };
    let outputs = constrain_f128_fixed_table_basis_batch(
      &mut builder,
      &table,
      &points,
      PHASE,
    )
    .unwrap();
    for output in &outputs {
      assert_eq!(
        *output.value(),
        literal(
          &ENTRIES,
          &points[0].iter().map(|v| *v.value()).collect::<Vec<_>>()
        )
      );
    }
    assert_eq!(
      outputs[0].bit_variables() == outputs[1].bit_variables(),
      shared
    );
    counts.push(builder.finish_projection().unwrap().census().constraints);
  }
  assert!(counts[0] < counts[1], "shared {counts:?}");
}

#[test]
fn malformed_structure_claims_refuse_before_emission_and_false_values_fail_r1cs()
 {
  let table = compile(&[4, 3, 2, 1, 0], &ENTRIES);
  let mut baseline = R1csBuilder::new_projection();
  fixture(&mut baseline, 0);
  let baseline = baseline.finish_projection().unwrap();
  for case in 0..9 {
    let mut builder = R1csBuilder::new_projection();
    let mut claims = fixture(&mut builder, 0);
    let mut id = matrix();
    match case {
      0 => {
        claims.pop();
      },
      1 => claims.push(claims[0].clone()),
      2 => claims.clear(),
      3 => claims[1].matrix.circuit_digest[0] ^= 1,
      4 => {
        claims[2].row_point.pop();
      },
      5 => {
        claims[0].column_point.pop();
      },
      6 => {
        let extra = claims[0].value.clone();
        claims[1].column_point.push(extra);
      },
      7 => id.row_variables += 1,
      8 => id.column_variables = u32::MAX,
      _ => unreachable!(),
    }
    assert_eq!(
      constrain_f128_structure_original_claims(
        &mut builder,
        id,
        &table,
        &claims,
        PHASE
      ),
      Err(R1csError::InternalShape)
    );
    assert_eq!(builder.finish_projection().unwrap(), baseline);
  }
  for index in 0..3 {
    let mut builder = R1csBuilder::new();
    let mut claims = fixture(&mut builder, 0);
    let mut bad = *claims[index].value.value();
    bad[0] ^= 1;
    claims[index].value = alloc_f128_private(&mut builder, bad, PHASE).unwrap();
    constrain_f128_structure_original_claims(
      &mut builder,
      matrix(),
      &table,
      &claims,
      PHASE,
    )
    .unwrap();
    assert!(matches!(builder.finish(), Err(R1csError::Unsatisfied { .. })));
  }
}

#[test]
fn batch_handles_zero_constants_empty_batches_and_dimension_refusal() {
  for entries in [vec![], vec![(0, [19; 16])]] {
    let table = compile(&[], &entries);
    let mut builder = R1csBuilder::new();
    let outputs = constrain_f128_fixed_table_basis_batch(
      &mut builder,
      &table,
      &vec![vec![]; 3],
      PHASE,
    )
    .unwrap();
    for output in outputs {
      assert_eq!(*output.value(), literal(&entries, &[]));
    }
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
  }
  let table = compile(&[0], &[]);
  let mut builder = R1csBuilder::new_projection();
  assert!(
    constrain_f128_fixed_table_basis_batch(&mut builder, &table, &[], PHASE)
      .unwrap()
      .is_empty()
  );
  assert_eq!(
    constrain_f128_fixed_table_basis_batch(
      &mut builder,
      &table,
      &[vec![]],
      PHASE
    ),
    Err(R1csError::InternalShape)
  );
  assert_eq!(
    builder.finish_projection().unwrap(),
    R1csBuilder::new_projection().finish_projection().unwrap()
  );
}
