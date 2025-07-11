// TODO: remove
#![allow(dead_code)]

use indexmap::IndexMap;
use p3_goldilocks::Goldilocks as G;
use rustc_hash::FxBuildHasher;

pub struct Toplevel {
    pub(crate) functions: Vec<Function>,
    pub(crate) memory_widths: Vec<usize>,
}

pub struct Function {
    pub(crate) input_size: usize,
    pub(crate) output_size: usize,
    pub(crate) body: Block,
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
