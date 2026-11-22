//! Aiur's untrusted execution engine. Lean supplies execution bytecode; Rust
//! evaluates it and records memoized queries. Companion population plans fill
//! the final optimized circuit rows from these records.

pub mod artifact;
pub mod budget;
pub mod bytecode;
mod chunks;
pub mod execute;
mod ffi;
pub mod field;
#[cfg(feature = "function-profile")]
pub mod function_profile;
pub mod hints;
mod host;
mod index;
pub mod ixon;
pub mod library;
pub mod maps;
pub mod memory;
#[cfg(feature = "native")]
pub mod native;
mod prefetch;
pub mod query;
pub mod shared;
mod table;
pub mod trace;
pub mod value;

pub use bytecode::Program;
pub use execute::{Execution, ExecutionError, QueryInput, QueryOutput};
