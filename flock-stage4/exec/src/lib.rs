//! Generic IxBy execution to native Flock replay.
//!
//! Replay and census are diagnostics, not terminal acceptance. A complete
//! terminal proof additionally needs approved proof-free topology and all
//! matrix, circuit-structure, and jagged roots closed inside its relation.

mod blueprint;
mod census;
mod native;
pub mod replay;

pub use census::{
  ExecReplayCensusV0, ExecReplayProgressV0, census_exec_replay,
  census_exec_replay_observed,
};
pub use native::{ExecReplayWitness, compile_exec_binding, replay_exec};
