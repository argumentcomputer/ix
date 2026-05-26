use crate::FxIndexMap;

use super::G;

pub struct Toplevel {
  pub functions: Vec<Function>,
  pub memory_sizes: Vec<usize>,
}

pub struct Function {
  pub body: Block,
  pub layout: FunctionLayout,
  pub entry: bool,
  pub constrained: bool,
}

#[derive(Clone, Copy)]
pub struct FunctionLayout {
  pub input_size: usize,
  pub selectors: usize,
  pub auxiliaries: usize,
  pub lookups: usize,
}

impl FunctionLayout {
  pub fn width(&self) -> usize {
    self.input_size + self.selectors + self.auxiliaries
  }
}

pub struct Block {
  pub ops: Vec<Op>,
  pub ctrl: Ctrl,
}

pub enum Op {
  Const(G),
  Add(ValIdx, ValIdx),
  Sub(ValIdx, ValIdx),
  Mul(ValIdx, ValIdx),
  EqZero(ValIdx),
  Call(FunIdx, Vec<ValIdx>, usize, bool),
  Store(Vec<ValIdx>),
  Load(usize, ValIdx),
  AssertEq(Vec<ValIdx>, Vec<ValIdx>),
  IOGetInfo(ValIdx, Vec<ValIdx>),
  IOSetInfo(ValIdx, Vec<ValIdx>, ValIdx, ValIdx),
  IORead(ValIdx, ValIdx, usize),
  IOWrite(ValIdx, Vec<ValIdx>),
  U8BitDecomposition(ValIdx),
  U8ShiftLeft(ValIdx),
  U8ShiftRight(ValIdx),
  U8Xor(ValIdx, ValIdx),
  U8Add(ValIdx, ValIdx),
  U8Mul(ValIdx, ValIdx),
  U8Sub(ValIdx, ValIdx),
  U8And(ValIdx, ValIdx),
  U8Or(ValIdx, ValIdx),
  U8LessThan(ValIdx, ValIdx),
  U32LessThan(ValIdx, ValIdx),
  U8ChainRotr7(ValIdx, ValIdx),
  U8ChainRotr4(ValIdx, ValIdx),
  Debug(String, Option<Vec<ValIdx>>),
  /// Range-check two values into `[0, 256)` via the byte chip. Produces no new
  /// values: its `u8` results alias the two inputs (cf. `AssertEq`).
  U8RangeCheck(ValIdx, ValIdx),
}

pub enum Ctrl {
  Match(ValIdx, FxIndexMap<G, Block>, Option<Box<Block>>),
  Return(SelIdx, Vec<ValIdx>),
  Yield(SelIdx, Vec<ValIdx>),
  MatchContinue(
    ValIdx,
    FxIndexMap<G, Block>,
    Option<Box<Block>>,
    usize,      // output_size
    usize,      // shared_auxiliaries
    usize,      // shared_lookups
    Box<Block>, // continuation
  ),
}

pub type SelIdx = usize;
pub type ValIdx = usize;
pub type FunIdx = usize;
