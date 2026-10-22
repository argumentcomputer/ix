//! Aiur's untrusted execution engine. Lean supplies execution bytecode; Rust
//! evaluates it and records memoized queries. Companion population plans fill
//! the final optimized circuit rows from these records.

pub mod bytecode;
pub mod execute;
mod ffi;
pub mod field;
#[cfg(feature = "function-profile")]
pub mod function_profile;
pub mod hints;
mod host;
pub mod library;
pub mod maps;
pub mod memory;
pub mod query;
mod table;
pub mod trace;
pub mod value;

pub use bytecode::Program;
pub use execute::{Execution, ExecutionError, QueryInput, QueryOutput};
