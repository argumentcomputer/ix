// TODO: remove
#![allow(dead_code)]

use indexmap::IndexMap;
use p3_goldilocks::Goldilocks as G;
use rustc_hash::FxBuildHasher;

pub struct Toplevel {
    pub(super) functions: Vec<Function>,
    pub(super) memory_widths: Vec<usize>,
}

pub struct Function {
    input_size: usize,
    output_size: usize,
    pub(super) body: Block,
}

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

pub struct Block {
    pub(super) ops: Vec<Op>,
    pub(super) ctrl: Ctrl,
    sel_range: SelRange,
}

pub enum Op {
    Const(G),
    Add(ValIdx, ValIdx),
    Mul(ValIdx, ValIdx),
    Call(FunIdx, Vec<ValIdx>),
    Store(Vec<ValIdx>),
    Load(usize, ValIdx),
}

pub enum Ctrl {
    Match(ValIdx, FxIndexMap<G, Block>, Option<Box<Block>>),
    Return(SelIdx, Vec<ValIdx>),
}

pub struct SelRange {
    min_included: SelIdx,
    max_excluded: SelIdx,
}

#[derive(Clone, Copy)]
pub struct SelIdx(usize);

impl SelIdx {
    #[inline]
    pub(super) fn to_usize(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
pub struct ValIdx(usize);

impl ValIdx {
    #[inline]
    pub(super) fn to_usize(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
pub struct FunIdx(usize);

impl FunIdx {
    #[inline]
    pub(super) fn to_usize(self) -> usize {
        self.0
    }
}
