pub mod compile;
pub mod ground;
pub mod ref_graph;
pub mod scc;

use rustc_hash::{FxHashMap, FxHasher};
use std::{
    hash::{Hash, Hasher},
    sync::Arc,
};

use crate::lean::nat::Nat;

pub type ConstMap = FxHashMap<Arc<Name>, ConstantInfo>;

#[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum Name {
    Anonymous,
    Str(Arc<Name>, String, u64),
    Num(Arc<Name>, Nat, u64),
}

impl Name {
    fn get_hash(&self) -> u64 {
        match self {
            Name::Anonymous => 0,
            Name::Str(.., h) | Name::Num(.., h) => *h,
        }
    }

    pub fn mk_str(pre: Arc<Name>, s: String) -> Name {
        let hasher = &mut FxHasher::default();
        (7, pre.get_hash(), &s).hash(hasher);
        Name::Str(pre, s, hasher.finish())
    }

    pub fn mk_num(pre: Arc<Name>, n: Nat) -> Name {
        let hasher = &mut FxHasher::default();
        (11, pre.get_hash(), &n).hash(hasher);
        Name::Num(pre, n, hasher.finish())
    }
}

impl Hash for Name {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_hash().hash(state);
    }
}

#[derive(Debug)]
pub enum ConstantInfo {
    AxiomInfo(AxiomVal),
    DefnInfo(DefinitionVal),
    ThmInfo(TheoremVal),
    OpaqueInfo(OpaqueVal),
    QuotInfo(QuotVal),
    InductInfo(InductiveVal),
    CtorInfo(ConstructorVal),
    RecInfo(RecursorVal),
}

#[derive(Debug)]
pub struct AxiomVal {
    pub constant_val: ConstantVal,
    pub is_unsafe: bool,
}

#[derive(Debug)]
pub struct DefinitionVal {
    pub constant_val: ConstantVal,
    pub value: Arc<Expr>,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    pub all: Vec<Arc<Name>>,
}

#[derive(Debug)]
pub struct TheoremVal {
    pub constant_val: ConstantVal,
    pub value: Arc<Expr>,
    pub all: Vec<Arc<Name>>,
}

#[derive(Debug)]
pub struct OpaqueVal {
    pub constant_val: ConstantVal,
    pub value: Arc<Expr>,
    pub is_unsafe: bool,
    pub all: Vec<Arc<Name>>,
}

#[derive(Debug)]
pub struct QuotVal {
    pub constant_val: ConstantVal,
    pub kind: QuotKind,
}

#[derive(Debug)]
pub struct InductiveVal {
    pub constant_val: ConstantVal,
    pub num_params: Nat,
    pub num_indices: Nat,
    pub all: Vec<Arc<Name>>,
    pub ctors: Vec<Arc<Name>>,
    pub num_nested: Nat,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

#[derive(Debug)]
pub struct ConstructorVal {
    pub constant_val: ConstantVal,
    pub induct: Arc<Name>,
    pub cidx: Nat,
    pub num_params: Nat,
    pub num_fields: Nat,
    pub is_unsafe: bool,
}

#[derive(Debug)]
pub struct RecursorVal {
    pub constant_val: ConstantVal,
    pub all: Vec<Arc<Name>>,
    pub num_params: Nat,
    pub num_indices: Nat,
    pub num_motives: Nat,
    pub num_minors: Nat,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

#[derive(Debug)]
pub struct ConstantVal {
    pub name: Arc<Name>,
    pub level_params: Vec<Arc<Name>>,
    pub typ: Arc<Expr>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Bvar(Nat, u64),
    Fvar(Arc<Name>, u64),
    Mvar(Arc<Name>, u64),
    Sort(Arc<Level>, u64),
    Const(Arc<Name>, Vec<Arc<Level>>, u64),
    App(Arc<Expr>, Arc<Expr>, u64),
    Lam(Arc<Name>, Arc<Expr>, Arc<Expr>, BinderInfo, u64),
    ForallE(Arc<Name>, Arc<Expr>, Arc<Expr>, BinderInfo, u64),
    LetE(Arc<Name>, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool, u64),
    Lit(Literal, u64),
    Mdata(Vec<(Arc<Name>, DataValue)>, Arc<Expr>, u64),
    Proj(Arc<Name>, Nat, Arc<Expr>, u64),
}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Expr::Bvar(_, h)
            | Expr::Fvar(_, h)
            | Expr::Mvar(_, h)
            | Expr::Sort(_, h)
            | Expr::Const(.., h)
            | Expr::App(.., h)
            | Expr::Lam(.., h)
            | Expr::ForallE(.., h)
            | Expr::LetE(.., h)
            | Expr::Lit(_, h)
            | Expr::Mdata(.., h)
            | Expr::Proj(.., h) => h.hash(state),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Level {
    Zero,
    Succ(Arc<Level>),
    Max(Arc<Level>, Arc<Level>),
    Imax(Arc<Level>, Arc<Level>),
    Param(Arc<Name>),
    Mvar(Arc<Name>),
}

#[derive(Debug)]
pub struct RecursorRule {
    pub ctor: Arc<Name>,
    pub n_fields: Nat,
    pub rhs: Arc<Expr>,
}

#[derive(Debug)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

#[derive(Debug)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

#[derive(Debug)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
    NatVal(Nat),
    StrVal(String),
}

#[derive(Debug, PartialEq, Eq)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Int {
    OfNat(Nat),
    NegSucc(Nat),
}

#[derive(Debug, PartialEq, Eq)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Arc<Name>),
    OfNat(Nat),
    OfInt(Int),
    OfSyntax(Box<Syntax>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Syntax {
    Missing,
    Node(SourceInfo, Arc<Name>, Vec<Syntax>),
    Atom(SourceInfo, String),
    Ident(SourceInfo, Substring, Arc<Name>, Vec<SyntaxPreresolved>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum SyntaxPreresolved {
    Namespace(Arc<Name>),
    Decl(Arc<Name>, Vec<String>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum SourceInfo {
    Original(Substring, Nat, Substring, Nat),
    Synthetic(Nat, Nat, bool),
    None,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Substring {
    pub str: String,
    pub start_pos: Nat,
    pub stop_pos: Nat,
}
