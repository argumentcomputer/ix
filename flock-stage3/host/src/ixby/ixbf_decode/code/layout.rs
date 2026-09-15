use super::super::{NaturalCapacity, bodies::BodyCapacity};
use anyhow::{Result, ensure};

/// The address convention is setup-owned. Large layouts admit address/path
/// components only; they do not enlarge the current canonical body loader.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CodeLayout {
  pub(super) constructors: u64,
  pub(super) functions: u64,
  pub(super) blocks: u64,
  pub(super) operands: u64,
  pub(super) natural: NaturalCapacity,
  words: u64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CodeKind {
  Program,
  Constructor,
  Function,
  Block,
  Operand,
  Alternative,
}
impl CodeKind {
  pub const ALL: [Self; 6] = [
    Self::Program,
    Self::Constructor,
    Self::Function,
    Self::Block,
    Self::Operand,
    Self::Alternative,
  ];
}
pub(super) const PREFIX_WORDS: u64 = 6;
pub(super) const PROGRAM_WORDS: u64 = 30; // original digest[2], final grammar[28]
pub(super) const CONSTRUCTOR_WORDS: u64 = 7;
pub(super) const FUNCTION_WORDS: u64 = 5;
pub(super) const BLOCK_WORDS: u64 = 14;
pub(super) const ALTERNATIVE_WORDS: u64 = 4;
pub(super) const PREFIX: [u8; 16] = *b"IxBy/code/v0\0\0\0\0";

impl CodeLayout {
  pub fn new(
    constructors: u64,
    functions: u64,
    blocks: u64,
    operands: u64,
    natural: NaturalCapacity,
  ) -> Result<Self> {
    ensure!(constructors <= u32::MAX as u64, "code constructor address bound");
    for n in [functions, blocks, operands] {
      ensure!((1..=u32::MAX as u64).contains(&n), "code address bound");
    }
    let mut c =
      Self { constructors, functions, blocks, operands, natural, words: 0 };
    // Compute using u128 so every admitted total and byte offset fits u64.
    let block_words = BLOCK_WORDS as u128
      + operands as u128 * c.operand_words() as u128
      + constructors as u128 * ALTERNATIVE_WORDS as u128;
    let words = PREFIX_WORDS as u128
      + PROGRAM_WORDS as u128
      + constructors as u128 * CONSTRUCTOR_WORDS as u128
      + functions as u128 * FUNCTION_WORDS as u128
      + functions as u128 * blocks as u128 * block_words;
    ensure!(words <= u64::MAX as u128 / 16, "code byte size overflow");
    c.words = words as u64;
    Ok(c)
  }
  pub fn from_bodies(c: BodyCapacity) -> Self {
    Self::new(
      c.registry().constructors() as u64,
      c.registry().functions() as u64,
      c.registry().blocks_per_function() as u64,
      c.operands() as u64,
      c.natural(),
    )
    .unwrap()
  }
  pub fn constructors(self) -> u64 {
    self.constructors
  }
  pub fn functions(self) -> u64 {
    self.functions
  }
  pub fn blocks_per_function(self) -> u64 {
    self.blocks
  }
  pub fn operands_per_block(self) -> u64 {
    self.operands
  }
  pub fn natural(self) -> NaturalCapacity {
    self.natural
  }
  pub fn words(self) -> u64 {
    self.words
  }
  pub fn bytes(self) -> u64 {
    self.words * 16
  }
  pub fn depth(self) -> usize {
    let last = (self.bytes() - 1) / 1024;
    if last == 0 { 0 } else { last.ilog2() as usize + 1 }
  }
  pub fn window_words(self) -> usize {
    self.operand_words().max(PROGRAM_WORDS) as usize
  }
  pub fn record_words(self, kind: CodeKind) -> usize {
    (match kind {
      CodeKind::Program => PROGRAM_WORDS,
      CodeKind::Constructor => CONSTRUCTOR_WORDS,
      CodeKind::Function => FUNCTION_WORDS,
      CodeKind::Block => BLOCK_WORDS,
      CodeKind::Operand => self.operand_words(),
      CodeKind::Alternative => ALTERNATIVE_WORDS,
    }) as usize
  }
  pub(super) fn operand_words(self) -> u64 {
    7 + self.natural.magnitude_words() as u64
  }
  pub(super) fn block_words(self) -> u64 {
    BLOCK_WORDS
      + self.operands * self.operand_words()
      + self.constructors * ALTERNATIVE_WORDS
  }
  pub(super) fn constructors_start(self) -> u64 {
    PREFIX_WORDS + PROGRAM_WORDS
  }
  pub(super) fn functions_start(self) -> u64 {
    self.constructors_start() + self.constructors * CONSTRUCTOR_WORDS
  }
  pub(super) fn blocks_start(self) -> u64 {
    self.functions_start() + self.functions * FUNCTION_WORDS
  }
  /// Byte offset = base + request[1]*owner_stride + request[2]*block_stride
  /// + request[3]*ordinal_stride. Full-width bounds are checked by CodeGate.
  pub(super) fn address(self, kind: CodeKind) -> [u64; 4] {
    let (base, owner, block, ordinal) = match kind {
      CodeKind::Program => (PREFIX_WORDS, 0, 0, 0),
      CodeKind::Constructor => {
        (self.constructors_start(), CONSTRUCTOR_WORDS, 0, 0)
      },
      CodeKind::Function => (self.functions_start(), FUNCTION_WORDS, 0, 0),
      CodeKind::Block => (
        self.blocks_start(),
        self.blocks * self.block_words(),
        self.block_words(),
        0,
      ),
      CodeKind::Operand => (
        self.blocks_start() + BLOCK_WORDS,
        self.blocks * self.block_words(),
        self.block_words(),
        self.operand_words(),
      ),
      CodeKind::Alternative => (
        self.blocks_start()
          + BLOCK_WORDS
          + self.operands * self.operand_words(),
        self.blocks * self.block_words(),
        self.block_words(),
        ALTERNATIVE_WORDS,
      ),
    };
    [base, owner, block, ordinal].map(|n| n * 16)
  }
  pub(super) fn bounds(self, kind: CodeKind) -> [u64; 3] {
    match kind {
      CodeKind::Program => [0, 0, 0],
      CodeKind::Constructor => [self.constructors, 0, 0],
      CodeKind::Function => [self.functions, 0, 0],
      CodeKind::Block => [self.functions, self.blocks, 0],
      CodeKind::Operand => [self.functions, self.blocks, self.operands],
      CodeKind::Alternative => [self.functions, self.blocks, self.constructors],
    }
  }
}
