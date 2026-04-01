use crate::FxIndexMap;

use super::G;

pub struct Toplevel {
  pub(crate) functions: Vec<Function>,
  pub(crate) memory_sizes: Vec<usize>,
}

pub struct Function {
  pub(crate) name: String,
  pub(crate) body: Block,
  pub(crate) layout: FunctionLayout,
  pub(crate) entry: bool,
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
  pub(crate) min_sel_included: SelIdx,
  pub(crate) max_sel_excluded: SelIdx,
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
  IOGetInfo(Vec<ValIdx>),
  IOSetInfo(Vec<ValIdx>, ValIdx, ValIdx),
  IORead(ValIdx, usize),
  IOWrite(Vec<ValIdx>),
  U8BitDecomposition(ValIdx),
  U8ShiftLeft(ValIdx),
  U8ShiftRight(ValIdx),
  U8Xor(ValIdx, ValIdx),
  U8Add(ValIdx, ValIdx),
  U8Sub(ValIdx, ValIdx),
  U8And(ValIdx, ValIdx),
  U8Or(ValIdx, ValIdx),
  U8LessThan(ValIdx, ValIdx),
  U32LessThan(ValIdx, ValIdx),
  Debug(String, Option<Vec<ValIdx>>),
}

pub enum Ctrl {
  Match(ValIdx, FxIndexMap<G, Block>, Option<Box<Block>>),
  Return(SelIdx, Vec<ValIdx>),
}

pub type SelIdx = usize;
pub type ValIdx = usize;
pub type FunIdx = usize;

impl Block {
  /// Recursively visits every `Op` in this block and its sub-blocks.
  pub fn for_each_op(&self, f: &mut impl FnMut(&Op)) {
    for op in &self.ops {
      f(op);
    }
    match &self.ctrl {
      Ctrl::Match(_, cases, default) => {
        for block in cases.values() {
          block.for_each_op(f);
        }
        if let Some(block) = default {
          block.for_each_op(f);
        }
      },
      Ctrl::Return(..) => {},
    }
  }
}

impl Toplevel {
  /// A function needs a circuit iff it is reachable from an entry point
  /// through a chain of constrained `Op::Call` edges. Unconstrained calls
  /// do NOT propagate circuit-need, because once execution enters
  /// unconstrained mode it cascades to all sub-calls.
  pub fn needs_circuit(&self) -> Vec<bool> {
    let n = self.functions.len();
    let mut needs = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();

    // Seed: every entry function needs a circuit
    for (i, f) in self.functions.iter().enumerate() {
      if f.entry {
        needs[i] = true;
        stack.push(i);
      }
    }

    // BFS along constrained Call edges (NOT unconstrained)
    while let Some(fi) = stack.pop() {
      self.functions[fi].body.for_each_op(&mut |op| {
        if let Op::Call(callee, _, _, false) = op
          && !needs[*callee]
        {
          needs[*callee] = true;
          stack.push(*callee);
        }
      });
    }
    needs
  }
}
