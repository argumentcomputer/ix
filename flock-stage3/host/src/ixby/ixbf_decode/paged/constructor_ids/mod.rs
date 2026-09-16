//! Full constructor-ID uniqueness at a source-admitted read-only memory root.
//! All 256 physical slots are read, including canonical undeclared zeros.
//! A fixed exact permutation sorts complete [enabled, 512-bit ID] records.
mod emission;
mod gate;
mod proof;
mod relation;
#[cfg(test)]
mod tests;
mod witness;
use super::synthesis::*;
use crate::ixby::{
  auth_memory::multi::MultiCapacity, memory_log::PermutationPlan,
};
use anyhow::{Result, ensure};
use flock_prover::field::F128;
pub use gate::{ConstructorIdGate, ConstructorIdKind, ConstructorIdRow};
pub use proof::{CompiledConstructorIds, VerifiedConstructorIds};
pub use witness::ConstructorIdsAdvice;
pub const CONSTRUCTORS: usize = 256;
pub const CELLS: usize = 512;
pub const PARENTS: usize = 1023;
pub const NU: usize = 12;
pub const PUBLIC_WORDS: usize = 3;
pub const DOMAIN: &[u8] =
  b"IxBy/Flock/paged-constructor-ids:ctors256:bits512:parents1023:v0";
fn capacity() -> MultiCapacity {
  MultiCapacity::new(CELLS, PARENTS).unwrap()
}
fn plan() -> PermutationPlan {
  PermutationPlan::new(CONSTRUCTORS).unwrap()
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorIdsStatement([F128; PUBLIC_WORDS]);
impl ConstructorIdsStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "constructor IDs public width");
    ensure!(
      words[0].hi == 0 && words[0].lo <= CONSTRUCTORS as u64,
      "constructor IDs count"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
}
