//! Value-free completeness and geometry preflight for direct original claims.

use crate::ExecRootClosureError as Error;
use ix_stage4_trace::{
  ExecBindingV0, F128AlgebraTraceV1, F128MultipointTwistedAssistTraceV1,
  F128OriginalClaimTablesV0, F128WiringTraceV1,
};

/// Match every fixed program against the complete original replay BEFORE
/// emitting constraints. Symbolic reference equality justifies shared wiring;
/// the circuit gadgets check actual bit-wire identity again after emission.
pub fn validate_exec_original_claim_tables(
  tables: &F128OriginalClaimTablesV0,
  binding: &ExecBindingV0,
  algebra: &F128AlgebraTraceV1,
  wiring: &F128WiringTraceV1,
  multipoint: &F128MultipointTwistedAssistTraceV1,
) -> Result<(), Error> {
  if tables.registry_digest() != binding.registry_digest
    || tables.circuit_digest() != binding.circuit_digest
  {
    return Err(Error::Identity("original-claim statement setup"));
  }
  let program = tables.matrices();
  let claims = &algebra.deferred_matrix_claims;
  if claims.len() != program.outputs().len()
    || claims
      .iter()
      .zip(program.outputs())
      .any(|(claim, (id, _))| claim.matrix != *id)
  {
    return Err(Error::MatrixCoverage);
  }
  let shared = claims
    .iter()
    .find(|claim| {
      claim.matrix.variables
        == program.low_variables() + program.high_variables()
    })
    .ok_or(Error::MatrixCoverage)?;
  let low_len = 1usize << program.low_variables();
  let high_len = program.high_variables() as usize;
  if shared.row.low.len() != low_len
    || shared.column.low.len() != low_len
    || shared.row.point.len() != high_len
    || shared.column.point.len() != high_len
  {
    return Err(Error::PointShape("original matrix shared weights"));
  }
  for claim in claims {
    let high = (claim.matrix.variables - program.low_variables()) as usize;
    if claim.row.low != shared.row.low
      || claim.column.low != shared.column.low
      || claim.row.point != shared.row.point[..high]
      || claim.column.point != shared.column.point[..high]
    {
      return Err(Error::PointShape("original matrix shared wires"));
    }
  }
  let structure = tables.structure().0;
  if structure.circuit_digest != wiring.circuit_digest
    || structure.row_variables != wiring.row_variables
    || Some(structure.column_variables)
      != wiring.structure_base_variables.checked_add(3)
  {
    return Err(Error::Identity("original structure matrix"));
  }
  if tables.jagged().matrix() != multipoint.matrix {
    return Err(Error::Identity("original jagged matrix"));
  }
  if tables.jagged().combo().len() != multipoint.group_column_addresses.len()
    || tables
      .jagged()
      .combo()
      .iter()
      .zip(&multipoint.group_column_addresses)
      .any(|((address, _), expected)| address != expected)
  {
    return Err(Error::PointShape("original jagged combo address order"));
  }
  Ok(())
}
