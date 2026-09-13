//! Generic IxBy execution to native Flock replay.
//!
//! Replay and census are diagnostics, not terminal acceptance. A complete
//! terminal proof additionally needs proof-free R1CS/key compilation and all
//! matrix, circuit-structure, and jagged roots closed inside its relation.

mod blake3_table;
mod blueprint;
mod census;
mod closure;
mod closure_census;
mod native;
pub mod replay;
mod root_tables;
mod setup;

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
  census_exec_root_closed_observed,
};
pub use native::{ExecReplayWitness, compile_exec_binding, replay_exec};
pub use root_tables::{CompiledExecRootTables, compile_exec_root_tables};
pub use setup::{
  CompiledExecReplay, ExecReplayIdentitiesV0, compile_exec_replay,
};
