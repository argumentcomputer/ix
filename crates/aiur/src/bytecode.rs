use crate::FxIndexMap;

use super::G;

pub struct Toplevel {
  pub functions: Vec<Function>,
  pub memory_sizes: Vec<usize>,
  /// Circuit partition of the constrained functions, in first-occurrence
  /// order. Computed by the Lean compiler; every constrained function
  /// appears in exactly one circuit.
  pub circuits: Vec<Circuit>,
}

/// A circuit of the proving system, backing one or more functions. Ungrouped
/// functions get a singleton circuit; functions sharing a `#[group=...]` tag
/// share one circuit whose branching selects the member function.
///
/// `layout` is the merged layout: max `input_size`, sum of `selectors`, max
/// `auxiliaries` (which includes the single shared multiplicity column), max
/// `lookups` (slot 0 is the shared return lookup).
pub struct Circuit {
  pub members: Vec<FunIdx>,
  pub layout: FunctionLayout,
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
  /// Unconstrained `BigUint` division-modulo hint. Inputs are two pointers
  /// to `KLimbs` (= `List<U64>`) values storing the dividend `a` and divisor
  /// `b` as little-endian u64 limb chains. Outputs two new pointers to
  /// `KLimbs` values for the quotient `q` and remainder `r` such that
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
