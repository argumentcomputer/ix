//! Bounded immutable constructor values. Physical cells contain arena indices;
//! declaration identities and ordered fields are authenticated at their
//! producers. This is not mutable memory or a free host object table.

use super::machine::MachineCapacities;
use anyhow::{Result, ensure};

pub(crate) mod bits;
mod dispatch;
mod output;
#[cfg(test)]
pub(crate) mod test_support;
#[cfg(test)]
mod tests;
pub(crate) use dispatch::ObjectDispatchGate;
pub(crate) use output::build as build_output;

/// Explicit constructor/input/output tree bounds for the object setup class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectCapacity {
  constructors: usize,
  depth: usize,
  nodes: usize,
}

impl ObjectCapacity {
  pub fn new(constructors: usize, depth: usize, nodes: usize) -> Result<Self> {
    ensure!(
      (1..=4).contains(&constructors),
      "constructor declaration capacity"
    );
    ensure!((1..=3).contains(&depth), "constructor codec depth capacity");
    ensure!((1..=32).contains(&nodes), "constructor forest node capacity");
    Ok(Self { constructors, depth, nodes })
  }
  pub fn constructors(self) -> usize {
    self.constructors
  }
  pub fn depth(self) -> usize {
    self.depth
  }
  pub fn nodes(self) -> usize {
    self.nodes
  }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ObjectLayout {
  pub applications: bool,
  pub nat_capacity: Option<crate::ixby::nat_value::NatCapacity>,
  pub capacity: ObjectCapacity,
  pub fields: usize,
  pub inputs: usize,
  pub functions: usize,
  pub blocks: usize,
  pub steps: usize,
}

impl ObjectLayout {
  pub(crate) fn new(
    c: MachineCapacities,
    capacity: ObjectCapacity,
  ) -> Result<Self> {
    ensure!((1..=4).contains(&c.program.operands), "object field capacity");
    let layout = Self {
      applications: false,
      nat_capacity: None,
      capacity,
      fields: c.program.operands,
      inputs: c.input.values,
      functions: c.program.functions,
      blocks: c.program.blocks,
      steps: c.steps,
    };
    ensure!(layout.input_slots() <= 64, "expanded input-tree slot capacity");
    ensure!(layout.entries() <= 128, "immutable constructor arena capacity");
    ensure!(
      layout.tree_slots(capacity.depth()) <= 32,
      "expanded output-tree slot capacity"
    );
    Ok(layout)
  }
  /// Includes scalar/erased leaves. Empty unused tree positions remain zero.
  pub(crate) fn tree_slots(self, depth: usize) -> usize {
    (0..depth).map(|level| self.fields.pow(level as u32)).sum()
  }
  pub(crate) fn input_slots(self) -> usize {
    self.inputs * self.tree_slots(self.capacity.depth())
  }
  pub(crate) fn entries(self) -> usize {
    self.input_slots() + self.steps
  }
  pub(crate) fn record_words(self) -> usize {
    1 + 2 * self.fields
  }
  /// Full 256-bit digest, u32 member/tag, and fields/presence metadata.
  pub(crate) fn declaration_words(self) -> usize {
    1 + 4 * self.capacity.constructors()
  }
  /// Application-capable codecs also authenticate the function headers used
  /// to validate every PAP, including unused input/output tree nodes.
  pub(crate) fn value_table_words(self) -> usize {
    self.declaration_words()
      + if self.applications { 1 + self.functions } else { 0 }
  }
  pub(crate) fn operand_slots(self) -> usize {
    self.fields + usize::from(self.applications)
  }
  pub(crate) fn case_words(self) -> usize {
    1 + self.capacity.constructors()
  }
  pub(crate) fn program_words(self) -> usize {
    self.declaration_words() + self.functions * self.blocks * self.case_words()
  }
  pub(crate) fn case_word(self, function: usize, block: usize) -> usize {
    self.declaration_words()
      + (function * self.blocks + block) * self.case_words()
  }
  pub(crate) fn program_byte_slots(self) -> usize {
    self.functions * self.blocks * self.operand_slots()
  }
  pub(crate) fn byte_entries(self) -> usize {
    self.program_byte_slots() + self.input_slots() + self.steps
  }
}
