//! Bounded declaration/header materialization from original-wire dispatch.
//!
//! Every step consumes the actual dispatcher event and carries the entire
//! registry. Constructor/function indices and block owners come from the
//! grammar, never from witness-selected insertion addresses. Completion binds
//! exact coverage, constructor uniqueness and function entry frames. Reads
//! select only present records using full-width indices.
//!
//! The caller still authenticates the dispatcher's exact byte requests to one
//! expected file. This is not whole-program semantic admission: instruction
//! bodies, references, alternatives and typed value arenas are not registered
//! here, and no native Exec factory accepts this component as admission.

mod evaluate;
#[cfg(test)]
pub(in crate::ixby::ixbf_decode) mod fixtures;
mod gate;
#[cfg(test)]
pub(in crate::ixby::ixbf_decode) mod proof_tests;
mod relation;
mod slots;
#[cfg(test)]
mod tests;

pub use gate::{RegistryGate, RegistryOp, RegistryRow};
pub use slots::{
  FinishedProgramRegistry, ProgramRegistrySlots, ProgramRegistryState,
  RegistryReadWires,
};

use anyhow::{Result, ensure};

/// Physical capacities for this separate component, not new Exec limits.
/// The dense per-step bank is intentionally a small-class prototype.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegistryCapacity {
  constructors: usize,
  functions: usize,
  blocks: usize,
}
impl RegistryCapacity {
  pub fn new(
    constructors: usize,
    functions: usize,
    blocks_per_function: usize,
  ) -> Result<Self> {
    ensure!(constructors <= 4, "registry constructor capacity");
    ensure!((1..=4).contains(&functions), "registry function capacity");
    ensure!((1..=8).contains(&blocks_per_function), "registry block capacity");
    Ok(Self { constructors, functions, blocks: blocks_per_function })
  }
  pub fn constructors(self) -> usize {
    self.constructors
  }
  pub fn functions(self) -> usize {
    self.functions
  }
  pub fn blocks_per_function(self) -> usize {
    self.blocks
  }
  /// Constructor: presence, 5 fields, range. Function: presence, 3 fields,
  /// range. Block: presence, 2 fields, range. Ranges have u64 start/end lanes
  /// and cover the decoded header only, not the full function/block body.
  pub fn words(self) -> usize {
    self.constructors * 7
      + self.functions * 5
      + self.functions * self.blocks * 4
  }
  pub(super) fn cells(self) -> Vec<Cell> {
    let mut cells = Vec::new();
    let mut offset = 0;
    for (kind, count, fields) in [
      (RegistryOp::Constructor, self.constructors, 5),
      (RegistryOp::Function, self.functions, 3),
      (RegistryOp::Block, self.functions * self.blocks, 2),
    ] {
      for index in 0..count {
        let (owner, index) = if kind == RegistryOp::Block {
          (index / self.blocks, index % self.blocks)
        } else {
          (0, index)
        };
        cells.push(Cell { kind, owner, index, fields, offset });
        offset += fields + 2;
      }
    }
    debug_assert_eq!(offset, self.words());
    cells
  }
  pub(super) fn function(self, index: usize) -> usize {
    self.constructors * 7 + index * 5
  }
  pub(super) fn block(self, owner: usize, index: usize) -> usize {
    self.constructors * 7
      + self.functions * 5
      + (owner * self.blocks + index) * 4
  }
}

#[derive(Clone, Copy)]
pub(super) struct Cell {
  kind: RegistryOp,
  owner: usize,
  index: usize,
  fields: usize,
  offset: usize,
}

// Capture: old grammar, actual committed/tag/13 fields/next, old bank.
pub(super) const COMMITTED: usize = 28;
pub(super) const TAG: usize = 29;
pub(super) const FIELDS: usize = 30;
pub(super) const NEXT: usize = 43;
pub(super) const CAPTURE_BANK: usize = 44;
pub(super) const FINISH_BANK: usize = 28;
pub(super) const READ_BANK: usize = 3;
