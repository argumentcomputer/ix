//! Source admission for the paged execution memory layout. Each stage has
//! explicit source and memory endpoints. Whole-execution admission must link
//! these endpoints to grammar, code validation, initialization and execution.
pub mod code_capture;
pub mod commitment_bridge;
pub mod constructor_ids;
pub mod endpoints;
pub mod finalize;
pub mod initialize;
pub mod input_capture;
pub mod output_bytes;
pub mod references;
pub mod source_bytes;
mod synthesis;

pub(in crate::ixby) mod proof_support;
