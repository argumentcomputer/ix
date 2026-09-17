//! IXBF runtime, canonical admission, and paged Flock proof components.

pub mod access;
pub mod auth_memory;
mod bits;
pub mod bounded_hash;
pub mod commitment;
pub mod execution_order;
pub mod hash_control;
pub mod io;
pub mod ixbf;
pub mod ixbf_decode;
pub mod length;
pub mod memory_log;
pub mod paged_code;
pub mod paged_exec;
pub mod paged_frame;
pub mod paged_nat;
pub mod paged_primitive;
pub mod paged_value;
pub mod primitive;
pub mod select;
pub mod value;
pub mod wide_fuel;

#[cfg(test)]
mod commitment_proof_tests;
#[cfg(test)]
mod hash_proof_tests;
#[cfg(test)]
mod test_support;
