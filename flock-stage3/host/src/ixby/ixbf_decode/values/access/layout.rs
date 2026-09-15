use super::super::{GrammarKind, NaturalCapacity, ValueConfig};
use anyhow::{Result, ensure};

/// Setup-owned image geometry. Large dimensions permit address/path
/// components only; the existing arena loader remains bounded to eight nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueLayout {
  kind: GrammarKind,
  nodes: u64,
  max_depth: u64,
  natural: NaturalCapacity,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
  Manifest,
  Node,
  Child,
  Root,
}
impl ValueKind {
  pub const ALL: [Self; 4] =
    [Self::Manifest, Self::Node, Self::Child, Self::Root];
}
pub(super) const PREFIX: [u8; 16] = *b"IxBy/values/v0\0\0";
pub(super) const PREFIX_WORDS: usize = 5;
// Code digest[2], original transport digest[2], grammar[28], summary[3].
pub(super) const MANIFEST_WORDS: usize = 35;
impl ValueLayout {
  pub fn new(
    kind: GrammarKind,
    nodes: u64,
    max_depth: u64,
    natural: NaturalCapacity,
  ) -> Result<Self> {
    ensure!(kind != GrammarKind::Program, "value access transport kind");
    ensure!((1..=u32::MAX as u64).contains(&nodes), "value node address bound");
    ensure!((1..=nodes).contains(&max_depth), "value tree depth bound");
    Ok(Self { kind, nodes, max_depth, natural })
  }
  pub fn from_arena(c: ValueConfig) -> Self {
    Self::new(
      c.kind,
      c.arena.nodes() as u64,
      c.arena.depth() as u64,
      c.arena.natural(),
    )
    .unwrap()
  }
  pub fn kind(self) -> GrammarKind {
    self.kind
  }
  pub fn nodes(self) -> u64 {
    self.nodes
  }
  pub fn max_depth(self) -> u64 {
    self.max_depth
  }
  pub fn natural(self) -> NaturalCapacity {
    self.natural
  }
  pub fn node_words(self) -> usize {
    13 + self.natural.magnitude_words()
  }
  pub fn record_words(self, kind: ValueKind) -> usize {
    if kind == ValueKind::Manifest { MANIFEST_WORDS } else { self.node_words() }
  }
  pub fn window_words(self) -> usize {
    MANIFEST_WORDS.max(self.node_words())
  }
  pub fn words(self) -> u64 {
    // <= 40 + u32::MAX * 45, so both word count and byte size fit u64.
    (PREFIX_WORDS + MANIFEST_WORDS) as u64
      + self.nodes * self.node_words() as u64
  }
  pub fn bytes(self) -> u64 {
    16 * self.words()
  }
  pub fn depth(self) -> usize {
    let last = (self.bytes() - 1) / 1024;
    if last == 0 { 0 } else { last.ilog2() as usize + 1 }
  }
  pub(super) fn address(self, kind: ValueKind) -> [u64; 2] {
    if kind == ValueKind::Manifest {
      [16 * PREFIX_WORDS as u64, 0]
    } else {
      [
        16 * (PREFIX_WORDS + MANIFEST_WORDS) as u64,
        16 * self.node_words() as u64,
      ]
    }
  }
  pub(super) fn tree_start(self) -> usize {
    self.node_words() - 5
  }
}
