//! Fixed-capacity components of the generic IxBy execution relation.
//!
//! These gates are interpreter building blocks, not an Exec proof or a host
//! execution oracle. The complete machine and its refinement remain in progress.

pub mod access;
mod bits;
pub mod bounded_hash;
pub mod commitment;
pub mod control;
pub mod hash_control;
pub mod io;
pub mod length;
pub mod select;
pub mod value;

#[cfg(test)]
mod commitment_proof_tests;
#[cfg(test)]
mod hash_proof_tests;
#[cfg(test)]
mod test_support;
