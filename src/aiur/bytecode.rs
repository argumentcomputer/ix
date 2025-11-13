use crate::FxIndexMap;

use super::G;

pub struct Toplevel {
    pub(crate) functions: Vec<Function>,
    pub(crate) memory_sizes: Vec<usize>,
}

pub struct Function {
    pub(crate) body: Block,
    pub(crate) layout: FunctionLayout,
    pub(crate) unconstrained: bool,
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
    Call(FunIdx, Vec<ValIdx>, usize),
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
    Debug(String, Option<Vec<ValIdx>>),
}

pub enum Ctrl {
    Match(ValIdx, FxIndexMap<G, Block>, Option<Box<Block>>),
    Return(SelIdx, Vec<ValIdx>),
}

pub type SelIdx = usize;
pub type ValIdx = usize;
pub type FunIdx = usize;
