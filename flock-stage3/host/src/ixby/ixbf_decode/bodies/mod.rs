//! Complete typed original-wire block bodies and their immutable consumers.
//!
//! Assembly consumes every actual event of the instruction-checked Program
//! parser. Setup owns capacities, and the caller authenticates source reads.
//! This component is not an Exec profile or a native refinement theorem.
mod bank;
mod evaluate;
mod finish;
#[cfg(test)]
mod fixtures;
mod gate;
mod operand;
#[cfg(test)]
mod proof_tests;
mod read;
mod slots;
mod step;
mod synthesis;
#[cfg(test)]
mod tests;

use super::{NaturalCapacity, registry::RegistryCapacity};
use anyhow::{Result, ensure};
pub use gate::{BodyGate, BodyOp, BodyRow};
pub use slots::{
  BodyReadWires, FinishedProgramBodies, ProgramBodySlots, ProgramBodyState,
};

/// Physical bounds for this separate dense component, not guest limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BodyCapacity {
  registry: RegistryCapacity,
  natural: NaturalCapacity,
  operands: usize,
}
impl BodyCapacity {
  pub fn new(
    registry: RegistryCapacity,
    natural: NaturalCapacity,
    operands: usize,
  ) -> Result<Self> {
    ensure!(
      registry.functions() * registry.blocks_per_function() <= 8,
      "body block capacity"
    );
    ensure!((1..=4).contains(&operands), "body operand capacity");
    Ok(Self { registry, natural, operands })
  }
  pub fn registry(self) -> RegistryCapacity {
    self.registry
  }
  pub fn natural(self) -> NaturalCapacity {
    self.natural
  }
  pub fn operands(self) -> usize {
    self.operands
  }
  pub fn blocks(self) -> usize {
    self.registry.functions() * self.registry.blocks_per_function()
  }
  pub fn operand_words(self) -> usize {
    O_MAGNITUDE + self.natural.magnitude_words()
  }
  pub fn block_words(self) -> usize {
    HEADER_WORDS
      + self.operands * self.operand_words()
      + self.registry.constructors() * ALT_WORDS
  }
  pub fn bank_words(self) -> usize {
    self.blocks() * self.block_words()
  }
  pub fn finished_words(self) -> usize {
    self.registry.functions() * FUNCTION_WORDS + self.bank_words()
  }
  pub(super) fn state_words(self) -> usize {
    CONTROL_WORDS + self.block_words()
  }
  pub(super) fn state(self) -> usize {
    NAT + self.natural.magnitude_words()
  }
  pub(super) fn alternatives(self) -> usize {
    HEADER_WORDS + self.operands * self.operand_words()
  }
  pub(super) fn registry_block(self, f: usize, b: usize) -> usize {
    self.registry.constructors() * 7
      + self.registry.functions() * 5
      + (f * self.registry.blocks_per_function() + b) * 4
  }
}
// One complete block, followed by its ordered fixed-capacity operands/alts.
pub(super) const PRESENT: usize = 0;
pub(super) const LOCALS: usize = 1;
pub(super) const INSTRUCTION: usize = 2;
pub(super) const OPERATION: usize = 3;
pub(super) const PRIMITIVE: usize = 4;
pub(super) const REFERENCE: usize = 5;
pub(super) const PROJECTION: usize = 6;
pub(super) const ARGUMENTS: usize = 7;
pub(super) const OPERANDS: usize = 8;
pub(super) const TARGET0: usize = 9;
pub(super) const TARGET1: usize = 10;
pub(super) const ALTERNATIVES: usize = 11;
pub(super) const SPAN: usize = 12;
pub(super) const HEADER_END: usize = 13;
pub(super) const HEADER_WORDS: usize = 14;
// Operand: presence, original kind (local0,literal1,erased2), local index,
// scalar subtype, whole operand span, payload(start,length), fixed, Nat limbs.
pub(super) const O_KIND: usize = 1;
pub(super) const O_LOCAL: usize = 2;
pub(super) const O_SCALAR: usize = 3;
pub(super) const O_SPAN: usize = 4;
pub(super) const O_PAYLOAD: usize = 5;
pub(super) const O_FIXED: usize = 6;
pub(super) const O_MAGNITUDE: usize = 7;
pub(super) const ALT_WORDS: usize = 4; // presence, constructor, target, own span
pub(super) const FUNCTION_WORDS: usize = 5; // presence, arity, entry, blocks, full span
// Step: old grammar[28], actual committed/tag/fields[13]/next, actual next
// grammar control, checked Nat/payload ranges, actual Nat limbs, carried state.
pub(super) const COMMITTED: usize = 28;
pub(super) const TAG: usize = 29;
pub(super) const FIELDS: usize = 30;
pub(super) const NEXT: usize = 43;
pub(super) const NEXT_CONTROL: usize = 44;
pub(super) const NAT_RANGE: usize = 45;
pub(super) const BYTE_RANGE: usize = 46;
pub(super) const NAT: usize = 47;
// State: owner, block index, pending scalar, prefix start, subtype (7=unset),
// then current block record. All state clears on genuine block completion.
pub(super) const CONTROL_WORDS: usize = 5;
