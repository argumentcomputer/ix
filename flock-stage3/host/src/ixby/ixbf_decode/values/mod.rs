//! Typed IXFI/IXFO forests from actual original-wire dispatcher events.
//!
//! Constructor identities and PAP arities use the completed, instruction-checked
//! program registry. Flat preorder records retain scalar payloads and original
//! ranges; completion derives every parent, ordinal, subtree and depth. Source
//! authentication is the caller's responsibility. This is not an Exec profile,
//! executable-body admission, or a native constraint/refinement theorem.

mod bank;
mod evaluate;
#[cfg(test)]
mod fixtures;
mod gate;
mod link;
mod node;
#[cfg(test)]
mod proof_tests;
mod slots;
mod synthesis;
#[cfg(test)]
mod tests;

use super::{GrammarKind, NaturalCapacity, registry::RegistryCapacity};
use anyhow::{Result, ensure};
pub use gate::{ValueGate, ValueOp, ValueRow};
pub use slots::{
  FinishedValueArena, ValueArenaSlots, ValueArenaState, ValueReadWires,
};

/// Physical arena bounds, independent of the original program's semantic limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueCapacity {
  nodes: usize,
  depth: usize,
  natural: NaturalCapacity,
}
impl ValueCapacity {
  pub fn new(
    nodes: usize,
    depth: usize,
    natural: NaturalCapacity,
  ) -> Result<Self> {
    ensure!((1..=8).contains(&nodes), "value arena node capacity");
    ensure!((1..=nodes).contains(&depth), "value arena depth capacity");
    Ok(Self { nodes, depth, natural })
  }
  pub fn nodes(self) -> usize {
    self.nodes
  }
  pub fn depth(self) -> usize {
    self.depth
  }
  pub fn natural(self) -> NaturalCapacity {
    self.natural
  }
  pub fn record_words(self) -> usize {
    MAGNITUDE + self.natural.magnitude_words()
  }
  pub fn finished_record_words(self) -> usize {
    self.record_words() + TREE_WORDS
  }
  pub fn bank_words(self) -> usize {
    self.nodes * self.record_words()
  }
  pub fn finished_bank_words(self) -> usize {
    self.nodes * self.finished_record_words()
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueConfig {
  pub kind: GrammarKind,
  pub registry: RegistryCapacity,
  pub arena: ValueCapacity,
}
impl ValueConfig {
  fn validate(self) -> Result<()> {
    ensure!(
      self.kind != GrammarKind::Program,
      "value arena requires IXFI or IXFO"
    );
    Ok(())
  }
}

// Raw node words. Presence is Boolean; kind follows the original Value tag.
// SPAN = (own encoding start,end), PAYLOAD = (payload start,length).
pub(super) const PRESENT: usize = 0;
pub(super) const KIND: usize = 1;
pub(super) const SCALAR: usize = 2;
pub(super) const REFERENCE: usize = 3;
pub(super) const CHILDREN: usize = 4;
pub(super) const SPAN: usize = 5;
pub(super) const PAYLOAD: usize = 6;
pub(super) const FIXED: usize = 7;
pub(super) const MAGNITUDE: usize = 8;
// Completion appends parent+1 (zero for roots), ordinal, exclusive subtree end
// index, depth (roots = 1), and full subtree (start,end).
pub(super) const TREE_WORDS: usize = 5;

// Node-step inputs: old grammar, actual event, checked payloads, resolved ref,
// actual Nat limbs, then carried scalar pending/start/tag and body start.
pub(super) const COMMIT: usize = 28;
pub(super) const TAG: usize = 29;
pub(super) const FIELDS: usize = 30;
pub(super) const NEXT: usize = 43;
pub(super) const NAT_RANGE: usize = 44;
pub(super) const BYTE_RANGE: usize = 45;
pub(super) const RESOLVED: usize = 46;
pub(super) const NAT: usize = 47;
pub(super) const ACC_WORDS: usize = 4;
// Node output: next accumulator, exact node ordinal, complete raw record,
// residual. The record's presence is the completion flag.
pub(super) const PACKET_INDEX: usize = ACC_WORDS;
pub(super) const PACKET_RECORD: usize = ACC_WORDS + 1;
// Link inputs: committed, tag, thirteen fields, complete program bank.
pub(super) const LINK_BANK: usize = 15;
