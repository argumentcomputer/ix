//! Generic IxBy execution to native Flock replay.
//!
//! Replay and census are diagnostics, not terminal acceptance. A complete
//! terminal proof additionally needs feasible closed-relation geometry,
//! proof-free key preprocessing and actual proving/isolated verification.
//! The setup-only R1CS emitter and closed-root prototype are not that proof.

mod blake3_table;
mod blueprint;
mod census;
mod closure;
mod closure_census;
mod materialization;
mod native;
mod original_closure;
pub mod replay;
mod root_tables;
mod setup;
mod setup_emission;

pub use blake3_table::{
  CompiledExecBlake3RootMaps, compile_exec_blake3_root_maps,
};
pub use census::{
  ExecReplayCensusV0, ExecReplayProgressV0, census_exec_replay,
  census_exec_replay_observed,
};
pub use closure::{
  CompiledExecRootClosure, ExecRootClosureCompilationLimitsV0,
  compile_exec_root_closure,
};
pub use closure_census::{
  ExecRootClosedCensusLimitsV0, ExecRootClosedCensusOutcomeV0,
  ExecRootClosedCensusPrefixV0, ExecRootClosedCensusV0,
  census_exec_original_claims_observed,
  census_exec_original_claims_setup_observed, census_exec_root_closed_observed,
  census_exec_root_closed_setup_observed,
};
pub use materialization::{
  ExecOriginalMaterializationProgressV0,
  check_exec_original_claims_streamed_observed,
  materialize_exec_original_claims_setup_observed,
};
pub use native::{ExecReplayWitness, compile_exec_binding, replay_exec};
pub use original_closure::{
  CompiledExecOriginalClaimsClosure, ExecOriginalClosureArithmeticV0,
  ExecOriginalClosureLimitsV0, compile_exec_original_claims_closure,
  compile_exec_original_claims_closure_with_arithmetic,
};
pub use root_tables::{CompiledExecRootTables, compile_exec_root_tables};
pub use setup::{
  CompiledExecReplay, ExecReplayIdentitiesV0, compile_exec_replay,
};
pub use setup_emission::{ExecSetupR1csLimitsV0, ExecSetupSourceSlotsV0};
