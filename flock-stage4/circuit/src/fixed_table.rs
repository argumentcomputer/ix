//! Exact in-circuit evaluation of a verifier-owned sparse-table diagram.
//! This gadget alone is not a closed Exec relation: the caller must bind the
//! fixed table identity and the point/value wires of every deferred claim.

use crate::{
  ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError, constrain_f128_add,
  constrain_f128_multiply, f128::alloc_f128_constant,
};
use ix_stage4_trace::{F128FixedTableNodeV0, F128FixedTableV0};

/// Evaluate the table's multilinear extension at already-constrained point
/// coordinates. The DAG and all coefficients are setup constants; no advice
/// about a table value, branch outcome, or intermediate sum is accepted.
pub fn constrain_f128_fixed_table(
  builder: &mut R1csBuilder,
  table: &F128FixedTableV0,
  point: &[F128VariablesV1],
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  if point.len() != table.order().len() {
    return Err(R1csError::InternalShape);
  }
  let mut complements: Vec<Option<F128VariablesV1>> = vec![None; point.len()];
  let mut one = None;
  let mut values = Vec::with_capacity(table.nodes().len());
  for node in table.nodes() {
    let value = match *node {
      F128FixedTableNodeV0::Constant(value) => {
        alloc_f128_constant(builder, value, phase)?
      },
      F128FixedTableNodeV0::Branch { coordinate, low, high } => {
        let low = &values[low as usize];
        let high = &values[high as usize];
        let delta = constrain_f128_add(builder, low, high, phase)?;
        let slope = constrain_f128_multiply(
          builder,
          &point[coordinate as usize],
          &delta,
          phase,
        )?;
        constrain_f128_add(builder, low, &slope, phase)?
      },
      F128FixedTableNodeV0::Davio { coordinate, base, slope, complement } => {
        let coordinate = coordinate as usize;
        let factor = if complement {
          if complements[coordinate].is_none() {
            if one.is_none() {
              one =
                Some(alloc_f128_constant(builder, 1u128.to_le_bytes(), phase)?);
            }
            complements[coordinate] = Some(constrain_f128_add(
              builder,
              one.as_ref().expect("initialized one"),
              &point[coordinate],
              phase,
            )?);
          }
          complements[coordinate].as_ref().expect("initialized complement")
        } else {
          &point[coordinate]
        };
        let product = constrain_f128_multiply(
          builder,
          factor,
          &values[slope as usize],
          phase,
        )?;
        constrain_f128_add(builder, &values[base as usize], &product, phase)?
      },
    };
    values.push(value);
  }
  Ok(values[table.root() as usize].clone())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    alloc_f128_private, enforce_f128_equal,
    f128::{native_f128_add as add, native_f128_multiply as multiply},
  };
  use ark_bls12_381::Fr;
  use ark_ff::Field;
  use ix_stage4_trace::{F128FixedTableDavioLimitsV0, F128FixedTableLimitsV0};

  const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;
  const LIMITS: F128FixedTableLimitsV0 =
    F128FixedTableLimitsV0 { entries: 100, nodes: 100 };

  fn literal(entries: &[(u64, [u8; 16])], point: &[[u8; 16]]) -> [u8; 16] {
    entries.iter().fold([0; 16], |sum, &(index, value)| {
      let term = point.iter().enumerate().fold(value, |term, (i, &x)| {
        let weight =
          if index >> i & 1 != 0 { x } else { add(1u128.to_le_bytes(), x) };
        multiply(term, weight)
      });
      add(sum, term)
    })
  }

  #[test]
  fn fixed_sparse_mle_is_exact_and_all_output_bits_are_constrained() {
    let entries = [
      (0, 7u128.to_le_bytes()),
      (1, 19u128.to_le_bytes()),
      (6, [0xa7; 16]),
      (7, [0x19; 16]),
      (7, [0xa8; 16]),
    ];
    let table = F128FixedTableV0::compile(&[2, 0, 1], entries, LIMITS).unwrap();
    let davio = table
      .positive_davio(F128FixedTableDavioLimitsV0 {
        working_nodes: 1000,
        nodes: 1000,
        xor_calls: 1000,
      })
      .unwrap();
    let mixed = table
      .mixed_davio(F128FixedTableDavioLimitsV0 {
        working_nodes: 1000,
        nodes: 1000,
        xor_calls: 1000,
      })
      .unwrap();
    for table in [table, davio, mixed] {
      let mut first_shape = None;
      for point in [
        [[0; 16]; 3],
        [1u128.to_le_bytes(); 3],
        [[0x12; 16], [0xe1; 16], [0x39; 16]],
      ] {
        let expected = literal(&entries, &point);
        let mut builder = R1csBuilder::new();
        let point =
          point.map(|x| alloc_f128_private(&mut builder, x, PHASE).unwrap());
        let output =
          constrain_f128_fixed_table(&mut builder, &table, &point, PHASE)
            .unwrap();
        assert_eq!(*output.value(), expected);
        let claimed =
          alloc_f128_private(&mut builder, expected, PHASE).unwrap();
        enforce_f128_equal(&mut builder, &output, &claimed, PHASE);
        let (r1cs, witness) = builder.finish().unwrap();
        r1cs.check(&witness).unwrap();
        for &bit in claimed.bit_variables() {
          let mut bad = witness.clone();
          bad
            .set(bit, Fr::ONE - bad.assignment()[bit.index() as usize])
            .unwrap();
          assert!(r1cs.check(&bad).is_err());
        }
        for &bit in output.bit_variables() {
          let mut bad = witness.clone();
          bad
            .set(bit, Fr::ONE - bad.assignment()[bit.index() as usize])
            .unwrap();
          assert!(r1cs.check(&bad).is_err());
        }
        if let Some(digest) = first_shape {
          assert_eq!(r1cs.digest(), digest);
        } else {
          first_shape = Some(r1cs.digest());
        }
      }
    }
  }
  #[test]
  fn skipped_variables_empty_cube_and_point_shape_are_explicit() {
    for (order, entries, expected) in [
      (vec![], vec![], [0; 16]),
      (vec![], vec![(0, [5; 16])], [5; 16]),
      (vec![1, 0], (0..4).map(|i| (i, [7; 16])).collect(), [7; 16]),
    ] {
      let table = F128FixedTableV0::compile(&order, entries, LIMITS).unwrap();
      let mut builder = R1csBuilder::new();
      let point = order
        .iter()
        .map(|_| alloc_f128_private(&mut builder, [0x13; 16], PHASE).unwrap())
        .collect::<Vec<_>>();
      let output =
        constrain_f128_fixed_table(&mut builder, &table, &point, PHASE)
          .unwrap();
      assert_eq!(*output.value(), expected);
      let (r1cs, witness) = builder.finish().unwrap();
      r1cs.check(&witness).unwrap();
      let wrong = vec![output; order.len() + 1];
      assert!(
        constrain_f128_fixed_table(
          &mut R1csBuilder::new(),
          &table,
          &wrong,
          PHASE
        )
        .is_err()
      );
    }
  }
}
