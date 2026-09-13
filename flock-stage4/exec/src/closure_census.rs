//! Bounded matrix-free measurement of the complete root-closed composition.
//! A refused prefix is deliberately a different type from a full census.

use crate::{CompiledExecRootClosure, ExecReplayWitness};
use anyhow::{Result, ensure};
use ix_fflonk::{
  FFLONK_BLINDING_ROWS, FFLONK_MAX_BASE_DOMAIN, PlonkGateCensusV1,
  PlonkGatePrefixV0, PlonkGateProjectionV1,
};
use ix_terminal_circuit::{
  ConstraintPhase, R1csBuilder, R1csError, R1csProjectionV1,
  Stage4PublicInputsV1,
};
use std::{cell::Cell, rc::Rc};

const PUBLIC_ROWS: u64 = 2;
const ROW_RESOURCE: &str = "FFLONK required domain rows";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecRootClosedCensusLimitsV0 {
  /// Hard cap including the two public limbs and backend blinding rows.
  /// Must not exceed `FFLONK_MAX_BASE_DOMAIN`. Smaller/zero diagnostic caps
  /// are permitted. This is NOT a RAM/disk/SRS admission or proving API.
  pub required_domain_rows: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExecRootClosedCensusPrefixV0 {
  pub plonk: PlonkGatePrefixV0,
  pub last_phase: Option<ConstraintPhase>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecRootClosedCensusV0 {
  pub composition_digest: [u8; 32],
  pub r1cs: R1csProjectionV1,
  pub plonk: PlonkGateCensusV1,
  pub public_scalar_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecRootClosedCensusOutcomeV0 {
  Complete(Box<ExecRootClosedCensusV0>),
  /// Includes the single R1CS constraint whose lowering crossed the cap.
  /// There is no complete R1CS digest, domain, key, or proof in this variant.
  /// `required_rows` includes the two reserved public and blinding rows,
  /// even when a cap below that reservation refuses emission at zero rows.
  RejectedBudget {
    prefix: ExecRootClosedCensusPrefixV0,
    limit: u64,
    required_rows: u64,
  },
}

/// Emit the same whole relation as `CompiledExecRootClosure::constrain`,
/// stopping when the supported PLONK row budget is exceeded. No SRS, matrices,
/// or full witness are retained. Successful completion still does NOT check
/// a satisfying assignment or produce a FFLONK proof. Native root comparisons
/// below are only differential diagnostics; root discharge is emitted by the
/// closed relation itself, not supplied by these comparisons.
pub fn census_exec_root_closed_observed(
  compiled: &CompiledExecRootClosure<'_, '_>,
  public: Stage4PublicInputsV1,
  witness: &ExecReplayWitness<'_>,
  limits: ExecRootClosedCensusLimitsV0,
  report: impl FnMut(ExecRootClosedCensusPrefixV0) + 'static,
) -> Result<ExecRootClosedCensusOutcomeV0> {
  compiled.validate_witness(witness)?;
  if let Some(rejected) = check_budget(limits)? {
    return Ok(rejected);
  }
  let (mut builder, projection, prefix) =
    bounded_projection(limits.required_domain_rows, report, false);
  let output = compiled.constrain(&mut builder, public, witness);
  let emitted = output.and_then(|output| {
    ensure!(
      output.root_tables_digest() == compiled.tables().digest(),
      "closed relation root-table identity mismatch"
    );
    crate::census::check_roots(
      output.replay(),
      &witness.diagnostic_public_inputs(),
    )
  });
  finish_census(compiled, builder, projection, prefix, emitted)
}

/// Proof-free counterpart: the approved setup is the ONLY relation input.
/// Calls the complete setup emitter, including all root families, with the
/// same hard PLONK limit as native diagnostics. No guest/proof/statement is
/// constructed or inspected. Completion means only a full constraint census,
/// NOT a checked assignment, materialized key, admission to prove, or proof.
pub fn census_exec_root_closed_setup_observed(
  compiled: &CompiledExecRootClosure<'_, '_>,
  source_payload_limit: u64,
  limits: ExecRootClosedCensusLimitsV0,
  report: impl FnMut(ExecRootClosedCensusPrefixV0) + 'static,
) -> Result<ExecRootClosedCensusOutcomeV0> {
  if let Some(rejected) = check_budget(limits)? {
    return Ok(rejected);
  }
  let (mut builder, projection, prefix) =
    bounded_projection(limits.required_domain_rows, report, true);
  let emitted = compiled.emit_setup(&mut builder, source_payload_limit);
  finish_census(compiled, builder, projection, prefix, emitted)
}

fn check_budget(
  limits: ExecRootClosedCensusLimitsV0,
) -> Result<Option<ExecRootClosedCensusOutcomeV0>> {
  ensure!(
    limits.required_domain_rows <= FFLONK_MAX_BASE_DOMAIN,
    "root-closed census budget exceeds the supported FFLONK size-4n FFT domain"
  );
  let reserved = PUBLIC_ROWS + FFLONK_BLINDING_ROWS;
  if limits.required_domain_rows < reserved {
    return Ok(Some(ExecRootClosedCensusOutcomeV0::RejectedBudget {
      prefix: ExecRootClosedCensusPrefixV0::default(),
      limit: limits.required_domain_rows,
      required_rows: reserved,
    }));
  }
  Ok(None)
}

fn finish_census(
  compiled: &CompiledExecRootClosure<'_, '_>,
  builder: R1csBuilder,
  projection: PlonkGateProjectionV1,
  prefix: Rc<Cell<ExecRootClosedCensusPrefixV0>>,
  emitted: Result<()>,
) -> Result<ExecRootClosedCensusOutcomeV0> {
  // Always finish the builder, including when the final infallible enforce
  // refused the stream without a later allocation to propagate that error.
  let r1cs = match builder.finish_projection() {
    Err(R1csError::ResourceLimit { resource: ROW_RESOURCE, limit, actual }) => {
      return Ok(ExecRootClosedCensusOutcomeV0::RejectedBudget {
        prefix: prefix.get(),
        limit,
        required_rows: actual,
      });
    },
    other => other?,
  };
  emitted?;
  ensure!(
    u64::from(r1cs.public_variables()) == PUBLIC_ROWS,
    "closed relation public identity mismatch"
  );
  let plonk = projection.finish(&r1cs)?;
  ensure!(
    plonk.domain_size <= FFLONK_MAX_BASE_DOMAIN,
    "closed relation exceeds the supported FFLONK polynomial FFT"
  );
  Ok(ExecRootClosedCensusOutcomeV0::Complete(Box::new(
    ExecRootClosedCensusV0 {
      composition_digest: compiled.digest(),
      r1cs,
      plonk,
      public_scalar_bytes: 32 * PUBLIC_ROWS,
    },
  )))
}

fn bounded_projection(
  row_limit: u64,
  mut report: impl FnMut(ExecRootClosedCensusPrefixV0) + 'static,
  shape_only: bool,
) -> (R1csBuilder, PlonkGateProjectionV1, Rc<Cell<ExecRootClosedCensusPrefixV0>>)
{
  let projection = PlonkGateProjectionV1::new();
  let progress = projection.clone();
  let mut project = projection.observer();
  let prefix = Rc::new(Cell::new(ExecRootClosedCensusPrefixV0::default()));
  let observed = Rc::clone(&prefix);
  let observer = move |c: &ix_terminal_circuit::Constraint| {
    project(c);
    let plonk = progress
      .prefix()
      .map_err(|error| R1csError::ObserverFailure(error.to_string()))?;
    let current =
      ExecRootClosedCensusPrefixV0 { plonk, last_phase: Some(c.phase) };
    let previous = observed.replace(current);
    let required = plonk
      .constraint_rows
      .checked_add(PUBLIC_ROWS + FFLONK_BLINDING_ROWS)
      .ok_or_else(|| R1csError::ObserverFailure("row count overflow".into()))?;
    if current.last_phase != previous.last_phase
      || plonk.r1cs_constraints.is_multiple_of(10_000_000)
      || required > row_limit
    {
      report(current);
    }
    if required > row_limit {
      return Err(R1csError::ResourceLimit {
        resource: ROW_RESOURCE,
        limit: row_limit,
        actual: required,
      });
    }
    Ok(())
  };
  let builder = if shape_only {
    R1csBuilder::new_shape_projection_observed_fallible(observer)
  } else {
    R1csBuilder::new_projection_observed_fallible(observer)
  };
  (builder, projection, prefix)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::Fr;

  #[test]
  fn row_budget_counts_public_and_blinding_rows_and_rejects_final_emit() {
    for (limit, shape_only) in [(5, false), (6, false), (5, true), (6, true)] {
      let (mut builder, projection, prefix) =
        bounded_projection(limit, |_| {}, shape_only);
      assert_eq!(builder.is_shape_only(), shape_only);
      let a = builder.alloc_public(Fr::from(1u64)).unwrap();
      let b = builder.alloc_public(Fr::from(0u64)).unwrap();
      builder.enforce_boolean(ConstraintPhase::Statement, a);
      builder.enforce_boolean(ConstraintPhase::Transcript, b);
      assert_eq!(prefix.get().plonk.r1cs_constraints, 2);
      assert_eq!(prefix.get().plonk.constraint_rows, 2);
      assert_eq!(prefix.get().last_phase, Some(ConstraintPhase::Transcript));
      if limit == 5 {
        assert_eq!(
          builder.finish_projection(),
          Err(R1csError::ResourceLimit {
            resource: ROW_RESOURCE,
            limit: 5,
            actual: 6,
          })
        );
      } else {
        let r1cs = builder.finish_projection().unwrap();
        let plonk = projection.finish(&r1cs).unwrap();
        assert_eq!(plonk.constraint_rows, prefix.get().plonk.constraint_rows);
        assert_eq!(plonk.public_input_rows, PUBLIC_ROWS);
        assert_eq!(plonk.domain_size, 8);
      }
    }
  }
}
