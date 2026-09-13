//! Exact MLE evaluation through a fixed binary-linear matrix program.
//! The caller owns table authorization and must bind transcript point/value
//! wires. This standalone gadget is not a closed terminal relation.

use crate::{
  ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError, constrain_f128_add,
  constrain_f128_multiply, f128::alloc_f128_constant,
};
use ix_stage4_trace::{BinaryLinearMapV0, BinaryLinearReferenceV0};
use std::collections::{BTreeMap, BTreeSet};

/// Compute `eq(row)^T * M * eq(column)` with a verifier-owned exact XOR
/// program for `M`. The column basis is generated only for referenced input
/// coordinates. Output interpolation uses the same fixed sharing as the map,
/// never a test of witness values. No matrix evaluation hint is accepted.
pub fn constrain_f128_binary_linear_table(
  builder: &mut R1csBuilder,
  map: &BinaryLinearMapV0,
  row: &[F128VariablesV1],
  column: &[F128VariablesV1],
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let rows = u32::try_from(row.len()).ok().and_then(|n| 1usize.checked_shl(n));
  let columns =
    u32::try_from(column.len()).ok().and_then(|n| 1u32.checked_shl(n));
  if rows != Some(map.outputs().len()) || columns != Some(map.inputs()) {
    return Err(R1csError::InternalShape);
  }
  let zero = alloc_f128_constant(builder, [0; 16], phase)?;
  let one = alloc_f128_constant(builder, 1u128.to_le_bytes(), phase)?;
  let references = map
    .xors()
    .iter()
    .flat_map(|&(a, b)| [a, b])
    .chain(map.outputs().iter().copied());
  let indices = references
    .filter_map(|reference| match reference {
      BinaryLinearReferenceV0::Input(i) => Some(i),
      _ => None,
    })
    .collect::<BTreeSet<_>>()
    .into_iter()
    .collect::<Vec<_>>();
  let mut inputs = BTreeMap::new();
  basis(builder, column, &indices, &one, &mut inputs, phase)?;
  let mut operations = Vec::with_capacity(map.xors().len());
  let resolve = |r, operations: &[F128VariablesV1]| match r {
    BinaryLinearReferenceV0::Zero => zero.clone(),
    BinaryLinearReferenceV0::Input(i) => inputs[&i].clone(),
    BinaryLinearReferenceV0::Xor(i) => operations[i as usize].clone(),
  };
  for &(left, right) in map.xors() {
    let left = resolve(left, &operations);
    let right = resolve(right, &operations);
    operations.push(constrain_f128_add(builder, &left, &right, phase)?);
  }
  let mut values =
    map.outputs().iter().map(|&r| resolve(r, &operations)).collect::<Vec<_>>();
  for point in row {
    let mut next = Vec::with_capacity(values.len() / 2);
    for [low, high] in values.as_chunks::<2>().0 {
      // Reference identity is fixed by setup, unlike equality of their
      // assignment values. Eliding an equal pair cannot select a new shape.
      let value = if low.bit_variables() == high.bit_variables() {
        low.clone()
      } else {
        let delta = constrain_f128_add(builder, low, high, phase)?;
        let slope = constrain_f128_multiply(builder, point, &delta, phase)?;
        constrain_f128_add(builder, low, &slope, phase)?
      };
      next.push(value);
    }
    values = next;
  }
  values.pop().ok_or(R1csError::InternalShape)
}

/// MSB-first descent over a fixed set of requested Boolean indices; leaves
/// retain the LSB-coordinate convention of both Flock's basis and the map.
fn basis(
  builder: &mut R1csBuilder,
  point: &[F128VariablesV1],
  indices: &[u32],
  weight: &F128VariablesV1,
  output: &mut BTreeMap<u32, F128VariablesV1>,
  phase: ConstraintPhase,
) -> Result<(), R1csError> {
  if indices.is_empty() {
    return Ok(());
  }
  let Some((coordinate, rest)) = point.split_last() else {
    debug_assert_eq!(indices.len(), 1);
    output.insert(indices[0], weight.clone());
    return Ok(());
  };
  let bit = 1u32 << rest.len();
  let middle = indices.partition_point(|index| index & bit == 0);
  let high = constrain_f128_multiply(builder, weight, coordinate, phase)?;
  if middle > 0 {
    let low = constrain_f128_add(builder, weight, &high, phase)?;
    basis(builder, rest, &indices[..middle], &low, output, phase)?;
  }
  basis(builder, rest, &indices[middle..], &high, output, phase)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    alloc_f128_private, enforce_f128_equal,
    f128::{native_f128_add as add, native_f128_multiply as multiply},
  };
  use BinaryLinearReferenceV0::{Input, Xor, Zero};
  use ark_bls12_381::Fr;
  use ark_ff::Field;
  use ix_stage4_trace::{
    BinaryLinearMapLimitsV0, BinaryLinearValidationLimitsV0,
  };

  const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;
  const LIMITS: BinaryLinearMapLimitsV0 =
    BinaryLinearMapLimitsV0 { inputs: 8, xors: 10, outputs: 8 };

  fn eq(index: usize, point: &[[u8; 16]]) -> [u8; 16] {
    point.iter().enumerate().fold(1u128.to_le_bytes(), |a, (bit, &x)| {
      multiply(
        a,
        if index >> bit & 1 != 0 { x } else { add(x, 1u128.to_le_bytes()) },
      )
    })
  }

  #[test]
  fn shared_linear_formula_matches_literal_mle_and_constrains_its_claim() {
    let rows = vec![vec![0, 3], vec![0, 3, 7], vec![], vec![0, 3]];
    let map = BinaryLinearMapV0::compile(
      8,
      vec![(Input(0), Input(3)), (Xor(0), Input(7))],
      vec![Xor(0), Xor(1), Zero, Xor(0)],
      LIMITS,
    )
    .unwrap();
    map
      .check_rows(
        &rows,
        BinaryLinearValidationLimitsV0 {
          coefficient_words: 10,
          source_entries: 10,
        },
      )
      .unwrap();
    let mut shape = None;
    for point in [[0; 16], 1u128.to_le_bytes(), [0x29; 16]] {
      let row = [point, [0x31; 16]];
      let column = [[0x75; 16], point, [0xb4; 16]];
      let expected =
        rows.iter().enumerate().fold([0; 16], |sum, (i, columns)| {
          columns.iter().fold(sum, |sum, &j| {
            add(sum, multiply(eq(i, &row), eq(j, &column)))
          })
        });
      let mut builder = R1csBuilder::new();
      let row =
        row.map(|v| alloc_f128_private(&mut builder, v, PHASE).unwrap());
      let column =
        column.map(|v| alloc_f128_private(&mut builder, v, PHASE).unwrap());
      let output = constrain_f128_binary_linear_table(
        &mut builder,
        &map,
        &row,
        &column,
        PHASE,
      )
      .unwrap();
      assert_eq!(*output.value(), expected);
      let claimed = alloc_f128_private(&mut builder, expected, PHASE).unwrap();
      enforce_f128_equal(&mut builder, &output, &claimed, PHASE);
      let (r1cs, witness) = builder.finish().unwrap();
      r1cs.check(&witness).unwrap();
      for &bit in claimed.bit_variables() {
        let mut bad = witness.clone();
        bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
        assert!(r1cs.check(&bad).is_err());
      }
      if let Some(digest) = shape {
        assert_eq!(r1cs.digest(), digest);
      } else {
        shape = Some(r1cs.digest());
      }
    }
  }

  #[test]
  fn constant_empty_point_and_rectangular_shape_are_explicit() {
    for output in [Zero, Input(0)] {
      let map =
        BinaryLinearMapV0::compile(1, vec![], vec![output], LIMITS).unwrap();
      let mut builder = R1csBuilder::new();
      let result =
        constrain_f128_binary_linear_table(&mut builder, &map, &[], &[], PHASE)
          .unwrap();
      assert_eq!(*result.value(), u128::from(output == Input(0)).to_le_bytes());
      let (r1cs, witness) = builder.finish().unwrap();
      r1cs.check(&witness).unwrap();
      assert!(
        constrain_f128_binary_linear_table(
          &mut R1csBuilder::new(),
          &map,
          &[result],
          &[],
          PHASE
        )
        .is_err()
      );
    }
  }
}
