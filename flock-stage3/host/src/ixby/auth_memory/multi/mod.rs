//! Exact shared-path memory authentication. A whole-record permutation binds
//! all leaf/frontier/parent claims to all child requests and one expected root.
//! Strictly decreasing child levels rule out disconnected cycles or orphans.
mod gate;
#[cfg(test)]
mod proof_tests;
mod slots;
#[cfg(test)]
mod tests;
mod witness;

use crate::ixby::memory_log::PermutationPlan;
use anyhow::{Result, ensure};
pub use gate::{MultiGate, MultiKind, MultiRow};
pub use slots::{
  FrontierWires, LeafWires, MultiMemorySlots, MultiProofWires, ParentWires,
};
pub use witness::MultiAdvice;

pub const CLAIM_WORDS: usize = 6;

/// Setup-owned bounds. Unused parent/frontier slots have canonical zero data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MultiCapacity {
  pub leaves: usize,
  pub parents: usize,
}
impl MultiCapacity {
  pub fn new(leaves: usize, parents: usize) -> Result<Self> {
    ensure!(
      parents < 1 << 19 && leaves <= parents + 1,
      "memory multiproof capacity"
    );
    Ok(Self { leaves, parents })
  }
  pub fn frontier(self) -> usize {
    self.parents + 1 - self.leaves
  }
  pub fn plan(self) -> PermutationPlan {
    PermutationPlan::new((2 * self.parents + 1).next_power_of_two()).unwrap()
  }
  pub fn compressions(self) -> usize {
    2 * (self.leaves + self.parents)
  }
}
