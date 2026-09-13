//! Batched exact cofactor evaluation at setup-determined coordinate wires.
//! Sharing depends on wire identity, never on private field assignments.

use crate::{
  ConstraintPhase, F128CircuitStructureClaimVariablesV1, F128VariablesV1,
  R1csBuilder, R1csError, constrain_f128_add, constrain_f128_multiply,
  enforce_f128_equal, f128::alloc_f128_constant,
};
use ix_stage4_trace::{F128CircuitStructureMatrixIdV1, F128FixedTableBasisV0};

/// Evaluate the SAME approved full table at every point, in input order.
/// A cofactor layer is shared only while its entire already-consumed suffix
/// uses identical bit wires. Equal assignments on distinct wires never merge.
/// Table approval and connection to transcript claims belong to the caller.
pub fn constrain_f128_fixed_table_basis_batch(
  builder: &mut R1csBuilder,
  table: &F128FixedTableBasisV0,
  points: &[Vec<F128VariablesV1>],
  phase: ConstraintPhase,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  if points.iter().any(|point| point.len() != table.layers().len()) {
    return Err(R1csError::InternalShape);
  }
  if points.is_empty() {
    return Ok(Vec::new());
  }
  let zero = alloc_f128_constant(builder, [0; 16], phase)?;
  let constants = table
    .constants()
    .iter()
    .map(|&value| alloc_f128_constant(builder, value, phase))
    .collect::<Result<Vec<_>, _>>()?;
  let mut groups = vec![((0..points.len()).collect::<Vec<_>>(), constants)];
  for layer in table.layers().iter().rev() {
    let coordinate = layer.coordinate() as usize;
    let mut next = Vec::new();
    for (indices, values) in groups {
      debug_assert_eq!(values.len(), layer.child_rank() as usize);
      let mut partitions: Vec<Vec<usize>> = Vec::new();
      for index in indices {
        if let Some(part) = partitions.iter_mut().find(|part| {
          points[part[0]][coordinate].bit_variables()
            == points[index][coordinate].bit_variables()
        }) {
          part.push(index);
        } else {
          partitions.push(vec![index]);
        }
      }
      for part in partitions {
        let x = &points[part[0]][coordinate];
        let mut outputs = Vec::with_capacity(layer.rows().len());
        for row in layer.rows() {
          let low = sum(builder, &values, row.low(), &zero, phase)?;
          let slope = sum(builder, &values, row.slope(), &zero, phase)?;
          let product = constrain_f128_multiply(builder, x, &slope, phase)?;
          outputs.push(constrain_f128_add(builder, &low, &product, phase)?);
        }
        next.push((part, outputs));
      }
    }
    groups = next;
  }
  let mut outputs = vec![zero.clone(); points.len()];
  for (indices, values) in groups {
    let value = sum(builder, &values, table.output(), &zero, phase)?;
    for index in indices {
      outputs[index] = value.clone();
    }
  }
  builder.check_status()?;
  Ok(outputs)
}

/// Bind all three original Product-GKR structure claims, including their
/// values, to the SAME approved eight-plane matrix. This does not discard
/// constant-pin or zero planes, nor assume host-valued coordinates are fixed.
/// The surrounding replay must supply its complete original claim vector.
pub fn constrain_f128_structure_original_claims(
  builder: &mut R1csBuilder,
  matrix: F128CircuitStructureMatrixIdV1,
  table: &F128FixedTableBasisV0,
  claims: &[F128CircuitStructureClaimVariablesV1],
  phase: ConstraintPhase,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  if claims.len() != 3
    || u64::from(matrix.row_variables) + u64::from(matrix.column_variables)
      != table.layers().len() as u64
    || claims.iter().any(|claim| {
      claim.matrix != matrix
        || claim.row_point.len() != matrix.row_variables as usize
        || claim.column_point.len() != matrix.column_variables as usize
    })
  {
    return Err(R1csError::InternalShape);
  }
  let points = claims
    .iter()
    .map(|claim| [claim.row_point.clone(), claim.column_point.clone()].concat())
    .collect::<Vec<_>>();
  let outputs =
    constrain_f128_fixed_table_basis_batch(builder, table, &points, phase)?;
  for (output, claim) in outputs.iter().zip(claims) {
    enforce_f128_equal(builder, output, &claim.value, phase);
  }
  builder.check_status()?;
  Ok(outputs)
}

fn sum(
  builder: &mut R1csBuilder,
  values: &[F128VariablesV1],
  terms: &[u32],
  zero: &F128VariablesV1,
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  let Some((&first, rest)) = terms.split_first() else {
    return Ok(zero.clone());
  };
  let mut value = values[first as usize].clone();
  for &index in rest {
    value =
      constrain_f128_add(builder, &value, &values[index as usize], phase)?;
  }
  Ok(value)
}

#[cfg(test)]
#[path = "fixed_table_batch_tests.rs"]
mod tests;
