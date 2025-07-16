use indexmap::IndexMap;
use rustc_hash::FxBuildHasher;

use super::G;

pub struct Toplevel {
    pub(crate) functions: Vec<Function>,
    pub(crate) memory_widths: Vec<usize>,
}

pub struct Function {
    pub(crate) body: Block,
    pub(crate) layout: FunctionLayout,
}

#[derive(Clone, Copy)]
pub struct FunctionLayout {
    pub(crate) input_size: usize,
    pub(crate) output_size: usize,
    pub(crate) selectors: usize,
    pub(crate) auxiliaries: usize,
    pub(crate) lookups: usize,
}

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

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
    Call(FunIdx, Vec<ValIdx>),
    Store(Vec<ValIdx>),
    Load(usize, ValIdx),
}

pub enum Ctrl {
    Match(ValIdx, FxIndexMap<G, Block>, Option<Box<Block>>),
    Return(SelIdx, Vec<ValIdx>),
}

pub type SelIdx = usize;
pub type ValIdx = usize;
pub type FunIdx = usize;
