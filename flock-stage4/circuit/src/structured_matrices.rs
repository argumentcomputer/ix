//! Direct discharge of original Boolean-matrix claims at shared structured
//! weights. No auxiliary random fold, private table advice, or root sidecar.
//! This component is NOT by itself a complete Flock/Exec verifier.

use crate::{
  ConstraintPhase, F128DeferredMatrixClaimVariablesV1, F128VariablesV1,
  R1csBuilder, R1csError, constrain_f128_add, constrain_f128_multiply,
  enforce_f128_equal, f128::alloc_f128_constant,
};
use ix_stage4_trace::{F128StructuredMatricesV0, F128StructuredMatrixNodeV0};

/// Evaluate every setup-owned matrix at low-vector tensor equality weights.
/// Inputs must already be constrained F128 values. All addresses, pairs,
/// blocks and interpolation branches come exclusively from the immutable
/// program; no operation branches on a private field value.
///
/// This primitive does not approve the matrices or bind external claims;
/// use `constrain_f128_structured_matrix_claims` for exact claim binding.
pub fn constrain_f128_structured_matrices(
  builder: &mut R1csBuilder,
  program: &F128StructuredMatricesV0,
  row_low: &[F128VariablesV1],
  column_low: &[F128VariablesV1],
  row_high: &[F128VariablesV1],
  column_high: &[F128VariablesV1],
  phase: ConstraintPhase,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  let low = program.low_variables();
  let low_len = 1usize << low;
  let high_len = program.high_variables() as usize;
  if row_low.len() != low_len
    || column_low.len() != low_len
    || row_high.len() != high_len
    || column_high.len() != high_len
  {
    return Err(R1csError::InternalShape);
  }
  // At most 4096 slots (the compiler admits <= 6 low bits per side).
  let mut pairs = vec![None; low_len * low_len];
  for &pair in program.pairs() {
    let index = usize::from(pair);
    pairs[index] = Some(constrain_f128_multiply(
      builder,
      &row_low[index & (low_len - 1)],
      &column_low[index >> low],
      phase,
    )?);
  }
  let blocks = program
    .blocks()
    .iter()
    .map(|block| {
      // Setup compilation canonicalizes each nonempty block and retains
      // exactly its needed pair products, including XOR cancellation.
      let mut value =
        pairs[usize::from(block[0])].as_ref().expect("compiled pair").clone();
      for &pair in &block[1..] {
        value = constrain_f128_add(
          builder,
          &value,
          pairs[usize::from(pair)].as_ref().expect("compiled pair"),
          phase,
        )?;
      }
      Ok(value)
    })
    .collect::<Result<Vec<_>, R1csError>>()?;
  let mut nodes = Vec::with_capacity(program.nodes().len());
  for node in program.nodes() {
    let value = match *node {
      F128StructuredMatrixNodeV0::Zero => {
        alloc_f128_constant(builder, [0; 16], phase)?
      },
      F128StructuredMatrixNodeV0::Block(index) => {
        blocks[index as usize].clone()
      },
      F128StructuredMatrixNodeV0::Branch { column, bit, low, high } => {
        let low = &nodes[low as usize];
        let high = &nodes[high as usize];
        let delta = constrain_f128_add(builder, low, high, phase)?;
        let point = if column { column_high } else { row_high };
        let slope = constrain_f128_multiply(
          builder,
          &point[bit as usize],
          &delta,
          phase,
        )?;
        constrain_f128_add(builder, low, &slope, phase)?
      },
    };
    nodes.push(value);
  }
  Ok(
    program
      .outputs()
      .iter()
      .map(|(_, root)| nodes[*root as usize].clone())
      .collect(),
  )
}

/// Discharge EVERY supplied original matrix claim, in the exact setup order.
/// All low vectors must be the SAME constrained wires, and the high points
/// must be prefixes of the same wires. Equality of witness values alone does
/// not justify sharing and is never used to admit claims or select topology.
/// All identity/dimension/alias checks precede any circuit allocation.
///
/// The caller must approve the program's matrix identities and ensure these
/// are all original deferred claims; structure/jagged claims are separate.
pub fn constrain_f128_structured_matrix_claims(
  builder: &mut R1csBuilder,
  program: &F128StructuredMatricesV0,
  claims: &[F128DeferredMatrixClaimVariablesV1],
  phase: ConstraintPhase,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  if claims.len() != program.outputs().len() {
    return Err(R1csError::InternalShape);
  }
  let low_len = 1usize << program.low_variables();
  let high_len = program.high_variables() as usize;
  let shared = claims
    .iter()
    .find(|c| {
      c.matrix.variables == program.low_variables() + program.high_variables()
    })
    .ok_or(R1csError::InternalShape)?;
  if shared.row.low.len() != low_len
    || shared.column.low.len() != low_len
    || shared.row.point.len() != high_len
    || shared.column.point.len() != high_len
  {
    return Err(R1csError::InternalShape);
  }
  for (claim, (id, _)) in claims.iter().zip(program.outputs()) {
    if claim.matrix != *id {
      return Err(R1csError::InternalShape);
    }
    let high = (id.variables - program.low_variables()) as usize;
    if !same_wires(&claim.row.low, &shared.row.low)
      || !same_wires(&claim.column.low, &shared.column.low)
      || !same_wires(&claim.row.point, &shared.row.point[..high])
      || !same_wires(&claim.column.point, &shared.column.point[..high])
    {
      return Err(R1csError::InternalShape);
    }
  }
  let outputs = constrain_f128_structured_matrices(
    builder,
    program,
    &shared.row.low,
    &shared.column.low,
    &shared.row.point,
    &shared.column.point,
    phase,
  )?;
  for (output, claim) in outputs.iter().zip(claims) {
    enforce_f128_equal(builder, output, &claim.value, phase);
  }
  builder.check_status()?;
  Ok(outputs)
}

fn same_wires(a: &[F128VariablesV1], b: &[F128VariablesV1]) -> bool {
  a.len() == b.len()
    && a.iter().zip(b).all(|(a, b)| a.bit_variables() == b.bit_variables())
}

#[cfg(test)]
#[path = "structured_matrices_tests.rs"]
mod tests;
