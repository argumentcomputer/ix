//! Bind every deferred root to its setup-owned exact table evaluation.
//! These constraints use the replay's existing point and claim wires; there
//! is no new root witness, public sidecar, or native discharge callback.

use crate::{
  ConstraintPhase, F128CircuitStructureRootClaimVariablesV1,
  F128JaggedRootClaimVariablesV1, F128RootMatrixClaimVariablesV1,
  F128VariablesV1, R1csBuilder, R1csError, constrain_f128_binary_linear_table,
  constrain_f128_fixed_table, constrain_f128_fixed_table_basis,
  enforce_f128_equal,
};
use ix_stage4_trace::{
  ExecBindingV0, F128CircuitStructureAccumulatorTraceV1,
  F128FixedMatrixProgramV0, F128JaggedAccumulatorTraceV1,
  F128MatrixAccumulatorTraceV1, F128RootTableSetV0,
};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecRootClosureError {
  Identity(&'static str),
  MatrixCoverage,
  PointShape(&'static str),
  R1cs(R1csError),
}
impl fmt::Display for ExecRootClosureError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "Exec root closure: {self:?}")
  }
}
impl std::error::Error for ExecRootClosureError {}
impl From<R1csError> for ExecRootClosureError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Preflight the exact set/order against all approved fold identities and
/// statement binding. Run this before allocating or emitting the relation.
pub fn validate_exec_root_tables(
  tables: &F128RootTableSetV0,
  binding: &ExecBindingV0,
  matrices: &F128MatrixAccumulatorTraceV1,
  structure: &F128CircuitStructureAccumulatorTraceV1,
  jagged: &F128JaggedAccumulatorTraceV1,
) -> Result<(), ExecRootClosureError> {
  if tables.registry_digest() != binding.registry_digest
    || tables.circuit_digest() != binding.circuit_digest
    || matrices.registry_digest != tables.registry_digest()
  {
    return Err(ExecRootClosureError::Identity("statement setup"));
  }
  if tables.matrices().len() != matrices.folds.len()
    || tables
      .matrices()
      .iter()
      .zip(&matrices.folds)
      .any(|((id, _), fold)| *id != fold.matrix)
  {
    return Err(ExecRootClosureError::MatrixCoverage);
  }
  if tables.structure().0 != structure.matrix {
    return Err(ExecRootClosureError::Identity("structure fold"));
  }
  if tables.jagged().0 != jagged.matrix {
    return Err(ExecRootClosureError::Identity("jagged fold"));
  }
  Ok(())
}

/// Check coverage and all shapes before emitting any constraint, then bind
/// every Boolean-matrix claim. The order is fixed by the approved fold plan.
pub fn constrain_f128_matrix_root_tables(
  builder: &mut R1csBuilder,
  tables: &F128RootTableSetV0,
  roots: &[F128RootMatrixClaimVariablesV1],
) -> Result<Vec<F128VariablesV1>, ExecRootClosureError> {
  if roots.len() != tables.matrices().len() {
    return Err(ExecRootClosureError::MatrixCoverage);
  }
  for (root, (id, _)) in roots.iter().zip(tables.matrices()) {
    if root.matrix != *id {
      return Err(ExecRootClosureError::Identity("matrix root"));
    }
    if root.row_point.len() != id.variables as usize
      || root.column_point.len() != id.variables as usize
    {
      return Err(ExecRootClosureError::PointShape("matrix root"));
    }
  }
  roots
    .iter()
    .zip(tables.matrices())
    .map(|(root, (_, table))| {
      bind(builder, table, &root.row_point, &root.column_point, &root.value)
    })
    .collect()
}

pub fn constrain_f128_structure_root_table(
  builder: &mut R1csBuilder,
  tables: &F128RootTableSetV0,
  root: &F128CircuitStructureRootClaimVariablesV1,
) -> Result<F128VariablesV1, ExecRootClosureError> {
  let (id, table) = tables.structure();
  if root.matrix != *id {
    return Err(ExecRootClosureError::Identity("structure root"));
  }
  if root.row_point.len() != id.row_variables as usize
    || root.column_point.len() != id.column_variables as usize
  {
    return Err(ExecRootClosureError::PointShape("structure root"));
  }
  bind(builder, table, &root.row_point, &root.column_point, &root.value)
}

pub fn constrain_f128_jagged_root_table(
  builder: &mut R1csBuilder,
  tables: &F128RootTableSetV0,
  root: &F128JaggedRootClaimVariablesV1,
) -> Result<F128VariablesV1, ExecRootClosureError> {
  let (id, table) = tables.jagged();
  if root.matrix != *id {
    return Err(ExecRootClosureError::Identity("jagged root"));
  }
  if root.row_point.len() != id.row_variables as usize
    || root.column_point.len() != id.column_variables as usize
  {
    return Err(ExecRootClosureError::PointShape("jagged root"));
  }
  bind(builder, table, &root.row_point, &root.column_point, &root.value)
}

fn bind(
  builder: &mut R1csBuilder,
  table: &F128FixedMatrixProgramV0,
  row: &[F128VariablesV1],
  column: &[F128VariablesV1],
  claim: &F128VariablesV1,
) -> Result<F128VariablesV1, ExecRootClosureError> {
  let value = match table {
    F128FixedMatrixProgramV0::DecisionDiagram(table) => {
      let point = row.iter().chain(column).cloned().collect::<Vec<_>>();
      constrain_f128_fixed_table(builder, table, &point, PHASE)?
    },
    F128FixedMatrixProgramV0::BinaryLinear(map) => {
      constrain_f128_binary_linear_table(builder, map, row, column, PHASE)?
    },
    F128FixedMatrixProgramV0::CofactorBasis(table) => {
      let point = row.iter().chain(column).cloned().collect::<Vec<_>>();
      constrain_f128_fixed_table_basis(builder, table, &point, PHASE)?
    },
  };
  enforce_f128_equal(builder, &value, claim, PHASE);
  Ok(value)
}

#[cfg(test)]
#[path = "root_closure_tests.rs"]
mod tests;
