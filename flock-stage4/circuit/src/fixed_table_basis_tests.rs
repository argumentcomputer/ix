use super::*;
use crate::{
  R1csShapeLimitsV0, alloc_f128_private, enforce_f128_equal,
  f128::{native_f128_add as add, native_f128_multiply as multiply},
};
use ark_bls12_381::Fr;
use ark_ff::Field;
use ix_stage4_trace::{
  F128FixedTableBasisLimitsV0, F128FixedTableLimitsV0, F128FixedTableV0,
};

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;
const LIMITS: F128FixedTableBasisLimitsV0 = F128FixedTableBasisLimitsV0 {
  state_slots: 1000,
  dense_words: 10000,
  word_operations: 100000,
  coefficient_terms: 10000,
};

fn compile(
  order: &[u32],
  entries: &[(u64, [u8; 16])],
) -> F128FixedTableBasisV0 {
  let original = F128FixedTableV0::compile(
    order,
    entries.iter().copied(),
    F128FixedTableLimitsV0 { entries: 100, nodes: 1000 },
  )
  .unwrap();
  F128FixedTableBasisV0::compile(&original, LIMITS).unwrap()
}

fn literal(entries: &[(u64, [u8; 16])], point: &[[u8; 16]]) -> [u8; 16] {
  entries.iter().fold([0; 16], |sum, &(index, value)| {
    let value = point.iter().enumerate().fold(value, |term, (bit, &x)| {
      multiply(
        term,
        if index >> bit & 1 != 0 { x } else { add(x, 1u128.to_le_bytes()) },
      )
    });
    add(sum, value)
  })
}

#[test]
fn cofactor_basis_mle_is_exact_constrained_and_proof_free_shape_matches() {
  let entries = [
    (0, [0x73; 16]),
    (1, [0x57; 16]),
    (4, [0x22; 16]),
    (6, [0xa1; 16]),
    (6, [0x87; 16]),
  ];
  let table = compile(&[1, 2, 0], &entries);
  let emit = |builder: &mut R1csBuilder, point: [[u8; 16]; 3], expected| {
    let point = point.map(|x| alloc_f128_private(builder, x, PHASE).unwrap());
    let output =
      constrain_f128_fixed_table_basis(builder, &table, &point, PHASE).unwrap();
    let claimed = alloc_f128_private(builder, expected, PHASE).unwrap();
    enforce_f128_equal(builder, &output, &claimed, PHASE);
    (point, output, claimed)
  };
  let mut shape = R1csBuilder::new_shape(R1csShapeLimitsV0 {
    variables: 1_000_000,
    constraints: 1_000_000,
    nonzero_terms: 10_000_000,
  })
  .unwrap();
  emit(&mut shape, [[0; 16]; 3], [0; 16]);
  let shape = shape.finish_shape().unwrap();
  for point in [
    [[0; 16]; 3],
    [1u128.to_le_bytes(); 3],
    [[0x31; 16], [0xaf; 16], [0x59; 16]],
  ] {
    let expected = literal(&entries, &point);
    let mut builder = R1csBuilder::new();
    let (_, output, claimed) = emit(&mut builder, point, expected);
    assert_eq!(*output.value(), expected);
    let (r1cs, witness) = builder.finish().unwrap();
    assert_eq!(shape, r1cs);
    r1cs.check(&witness).unwrap();
    for &bit in claimed.bit_variables().iter().chain(output.bit_variables()) {
      let mut bad = witness.clone();
      bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
      assert!(r1cs.check(&bad).is_err());
    }
  }
}

#[test]
fn cofactor_basis_handles_constants_zero_rank_skips_and_wrong_point_length() {
  for (order, entries, expected) in [
    (vec![], vec![], [0; 16]),
    (vec![], vec![(0, [0xa5; 16])], [0xa5; 16]),
    (vec![1, 0], (0..4).map(|i| (i, [0x61; 16])).collect(), [0x61; 16]),
    (vec![1, 0], vec![], [0; 16]),
  ] {
    let table = compile(&order, &entries);
    let mut builder = R1csBuilder::new();
    let point = order
      .iter()
      .map(|_| alloc_f128_private(&mut builder, [0xf7; 16], PHASE).unwrap())
      .collect::<Vec<_>>();
    let output =
      constrain_f128_fixed_table_basis(&mut builder, &table, &point, PHASE)
        .unwrap();
    assert_eq!(*output.value(), expected);
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(
      constrain_f128_fixed_table_basis(
        &mut R1csBuilder::new(),
        &table,
        &vec![output; order.len() + 1],
        PHASE
      ),
      Err(R1csError::InternalShape)
    );
  }
}
