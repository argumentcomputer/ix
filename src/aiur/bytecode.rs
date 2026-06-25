use crate::FxIndexMap;

use super::G;

pub struct Toplevel {
  pub(crate) functions: Vec<Function>,
  pub(crate) memory_sizes: Vec<usize>,
}

pub struct Function {
  pub(crate) body: Block,
  pub(crate) layout: FunctionLayout,
  pub(crate) entry: bool,
  pub(crate) constrained: bool,
}

#[derive(Clone, Copy)]
pub struct FunctionLayout {
  pub(crate) input_size: usize,
  pub(crate) selectors: usize,
  pub(crate) auxiliaries: usize,
  pub(crate) lookups: usize,
}

impl FunctionLayout {
  pub fn width(&self) -> usize {
    self.input_size + self.selectors + self.auxiliaries
  }
}

pub struct Block {
  pub(crate) ops: Vec<Op>,
  pub(crate) ctrl: Ctrl,
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
  /// Unconstrained LE byte-list division-modulo hint. Inputs are two pointers
  /// to `ByteStream` (= `List<U8>`) values storing the dividend `a` and
  /// divisor `b` as little-endian byte sequences. Outputs two new pointers to
  /// `ByteStream` values for the quotient `q` and remainder `r` such that
  /// `q * b + r = a` with `0 ≤ r < b` (when `b > 0`). Computed natively by
  /// the runtime via `num_bigint::BigUint::div_rem`; no in-circuit recursion
  /// and no constraints generated. The caller is responsible for verifying
  /// the relation in constrained code.
  UnconstrainedBigUintDivMod(ValIdx, ValIdx),
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
