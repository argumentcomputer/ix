//! Generic IxBy execution to native Flock replay.
//!
//! Replay and census are diagnostics, not terminal acceptance. A complete
//! terminal proof additionally needs proof-free R1CS/key compilation and all
//! matrix, circuit-structure, and jagged roots closed inside its relation.

mod blueprint;
mod census;
mod native;
pub mod replay;
mod root_tables;
mod setup;

pub use census::{
  ExecReplayCensusV0, ExecReplayProgressV0, census_exec_replay,
  census_exec_replay_observed,
};
pub use native::{ExecReplayWitness, compile_exec_binding, replay_exec};
pub use root_tables::{CompiledExecRootTables, compile_exec_root_tables};
pub use setup::{
  CompiledExecReplay, ExecReplayIdentitiesV0, compile_exec_replay,
};
