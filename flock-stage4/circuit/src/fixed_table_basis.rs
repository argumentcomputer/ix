//! Exact cofactor-basis evaluation for setup-owned table programs. The caller
//! must authorize the table and bind its transcript point and claimed value.

use crate::{
  ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError, constrain_f128_add,
  constrain_f128_multiply, f128::alloc_f128_constant,
};
use ix_stage4_trace::F128FixedTableBasisV0;

/// Every coefficient comes from the immutable setup program; neither the
/// point assignment nor a native table-value hint can select circuit shape.
pub fn constrain_f128_fixed_table_basis(
  builder: &mut R1csBuilder,
  table: &F128FixedTableBasisV0,
  point: &[F128VariablesV1],
  phase: ConstraintPhase,
) -> Result<F128VariablesV1, R1csError> {
  if point.len() != table.layers().len() {
    return Err(R1csError::InternalShape);
  }
  let zero = alloc_f128_constant(builder, [0; 16], phase)?;
  let mut values = table
    .constants()
    .iter()
    .map(|&value| alloc_f128_constant(builder, value, phase))
    .collect::<Result<Vec<_>, _>>()?;
  for layer in table.layers().iter().rev() {
    debug_assert_eq!(values.len(), layer.child_rank() as usize);
    let mut next = Vec::with_capacity(layer.rows().len());
    for row in layer.rows() {
      let low = sum(builder, &values, row.low(), &zero, phase)?;
      let slope = sum(builder, &values, row.slope(), &zero, phase)?;
      let product = constrain_f128_multiply(
        builder,
        &point[layer.coordinate() as usize],
        &slope,
        phase,
      )?;
      next.push(constrain_f128_add(builder, &low, &product, phase)?);
    }
    values = next;
  }
  sum(builder, &values, table.output(), &zero, phase)
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
  let mut result = values[first as usize].clone();
  for &index in rest {
    result =
      constrain_f128_add(builder, &result, &values[index as usize], phase)?;
  }
  Ok(result)
}

#[cfg(test)]
#[path = "fixed_table_basis_tests.rs"]
mod tests;
