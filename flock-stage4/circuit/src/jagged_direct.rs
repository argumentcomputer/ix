//! Check all three original jagged claims directly against a fixed layout.
//! The pair weights are shared only at the SAME constrained column wires.

use crate::{
  ConstraintPhase, F128JaggedAssertionVariablesV1,
  F128JaggedRowWeightVariablesV1, F128VariablesV1, R1csBuilder, R1csError,
  constrain_f128_add, constrain_f128_multiply, enforce_f128_equal,
  f128::alloc_f128_constant,
};
use ix_stage4_trace::{
  F128JaggedDirectTableV0, F128JaggedEqualityNodeV0, F128JaggedRowNodeV0,
};

/// Enforce the exact original order: two scaled equality claims and the
/// packed-direct coefficient combination at the approved fixed addresses.
/// Every value is bound; no inherited/auxiliary folded claim is substituted.
/// Matrix authorization and completeness of the surrounding replay are the
/// setup owner's obligations. This component alone is not a full verifier.
pub fn constrain_f128_jagged_direct(
  builder: &mut R1csBuilder,
  table: &F128JaggedDirectTableV0,
  assertion: &F128JaggedAssertionVariablesV1,
  phase: ConstraintPhase,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  if assertion.matrix != table.matrix() || assertion.claims.len() != 3 {
    return Err(R1csError::InternalShape);
  }
  let shared = &assertion.claims[0].column_point;
  if shared.len() != table.matrix().column_variables as usize {
    return Err(R1csError::InternalShape);
  }
  for (index, claim) in assertion.claims.iter().enumerate() {
    if claim.column_point.len() != shared.len()
      || claim
        .column_point
        .iter()
        .zip(shared)
        .any(|(a, b)| a.bit_variables() != b.bit_variables())
    {
      return Err(R1csError::InternalShape);
    }
    match (&claim.row, index) {
      (F128JaggedRowWeightVariablesV1::Eq { point, .. }, 0 | 1)
        if point.len() == table.matrix().row_variables as usize => {},
      (F128JaggedRowWeightVariablesV1::Combo { terms }, 2)
        if terms.len() == table.combo().len()
          && terms
            .iter()
            .zip(table.combo())
            .all(|(term, (address, _))| term.address == *address) => {},
      _ => return Err(R1csError::InternalShape),
    }
  }

  let one = alloc_f128_constant(builder, 1u128.to_le_bytes(), phase)?;
  let zero = alloc_f128_constant(builder, [0; 16], phase)?;
  let mut complements: Vec<Option<F128VariablesV1>> = vec![None; shared.len()];
  let mut equality = Vec::with_capacity(table.equality_nodes().len());
  for node in table.equality_nodes() {
    equality.push(match *node {
      F128JaggedEqualityNodeV0::Factor { coordinate, complement } => {
        let index = coordinate as usize;
        if complement {
          if complements[index].is_none() {
            complements[index] =
              Some(constrain_f128_add(builder, &one, &shared[index], phase)?);
          }
          complements[index].as_ref().expect("initialized complement").clone()
        } else {
          shared[index].clone()
        }
      },
      F128JaggedEqualityNodeV0::Multiply { left, right } => {
        constrain_f128_multiply(
          builder,
          &equality[left as usize],
          &equality[right as usize],
          phase,
        )?
      },
    });
  }
  let pairs = table
    .pair_outputs()
    .iter()
    .map(|&index| equality[index as usize].clone())
    .collect::<Vec<_>>();
  let mut outputs = Vec::with_capacity(3);
  for claim in &assertion.claims {
    let output = match &claim.row {
      F128JaggedRowWeightVariablesV1::Eq { scale, point } => {
        let mut rows = Vec::with_capacity(table.row_nodes().len());
        for node in table.row_nodes() {
          rows.push(match *node {
            F128JaggedRowNodeV0::Pair(index) => pairs[index as usize].clone(),
            F128JaggedRowNodeV0::Branch { coordinate, low, high } => {
              let delta = constrain_f128_add(
                builder,
                &rows[low as usize],
                &rows[high as usize],
                phase,
              )?;
              let slope = constrain_f128_multiply(
                builder,
                &point[coordinate as usize],
                &delta,
                phase,
              )?;
              constrain_f128_add(builder, &rows[low as usize], &slope, phase)?
            },
          });
        }
        constrain_f128_multiply(
          builder,
          scale,
          &rows[table.row_root() as usize],
          phase,
        )?
      },
      F128JaggedRowWeightVariablesV1::Combo { terms } => {
        let mut sum = zero.clone();
        for (term, (_, pair)) in terms.iter().zip(table.combo()) {
          let product = constrain_f128_multiply(
            builder,
            &term.coefficient,
            &pairs[*pair as usize],
            phase,
          )?;
          sum = constrain_f128_add(builder, &sum, &product, phase)?;
        }
        sum
      },
    };
    enforce_f128_equal(builder, &output, &claim.value, phase);
    outputs.push(output);
  }
  builder.check_status()?;
  Ok(outputs)
}

#[cfg(test)]
#[path = "jagged_direct_tests.rs"]
mod tests;
