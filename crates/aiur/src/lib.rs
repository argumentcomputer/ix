//! Aiur's untrusted execution engine. Lean supplies execution bytecode; Rust
//! evaluates it and records memoized queries. Companion population plans fill
//! the final optimized circuit rows from these records.

pub mod budget;
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
/// Decode a trusted compiler artifact. Wide constraint polynomials can exceed
/// serde_json's default nesting limit; witness/proof input retains normal bounds.
pub fn decode_artifact<T: serde::de::DeserializeOwned>(
  bytes: &[u8],
) -> Result<T, serde_json::Error> {
  let mut decoder = serde_json::Deserializer::from_slice(bytes);
  decoder.disable_recursion_limit();
  let artifact = T::deserialize(&mut decoder)?;
  decoder.end()?;
  Ok(artifact)
}
