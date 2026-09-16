//! Fixed-capacity scalar/control IxBy execution and reusable components.
//!
//! `exec` connects canonical bytes, the machine, commitments and direct Flock
//! proofs. Native constraint-to-reference refinement and the broader crypto
//! guest profile remain unfinished; this is not a Stage 4 compact proof.

pub mod access;
pub mod auth_memory;
mod bits;
pub mod bounded_hash;
pub mod byte_value;
pub mod commitment;
pub mod control;
pub mod decode;
pub mod exec;
pub mod hash_control;
pub mod io;
pub mod ixbf;
pub mod ixbf_decode;
pub mod length;
pub mod machine;
pub mod memory_log;
pub mod nat_value;
pub mod object_value;
pub mod primitive;
pub mod select;
pub mod value;
pub mod wide_fuel;

pub(crate) mod application;
#[cfg(test)]
mod commitment_proof_tests;
#[cfg(test)]
mod hash_proof_tests;
#[cfg(test)]
mod test_support;
