use std::{
    hash::{Hash, Hasher},
    sync::Arc,
};

use rustc_hash::FxHashMap;

use crate::lean::nat::Nat;

pub type ConstMap = FxHashMap<Name, ConstantInfo>;

#[derive(Hash, PartialEq, Eq, Debug)]
pub enum Name {
    Anonymous,
    Str(Box<Name>, String),
    Num(Box<Name>, Nat),
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
    pub all: Vec<Name>,
}

#[derive(Debug)]
pub struct TheoremVal {
    pub constant_val: ConstantVal,
    pub value: Arc<Expr>,
    pub all: Vec<Name>,
}

#[derive(Debug)]
pub struct OpaqueVal {
    pub constant_val: ConstantVal,
    pub value: Arc<Expr>,
    pub is_unsafe: bool,
    pub all: Vec<Name>,
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
    pub all: Vec<Name>,
    pub ctors: Vec<Name>,
    pub num_nested: Nat,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

#[derive(Debug)]
pub struct ConstructorVal {
    pub constant_val: ConstantVal,
    pub induct: Name,
    pub cidx: Nat,
    pub num_params: Nat,
    pub num_fields: Nat,
    pub is_unsafe: bool,
}

#[derive(Debug)]
pub struct RecursorVal {
    pub constant_val: ConstantVal,
    pub all: Vec<Name>,
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
    pub name: Name,
    pub level_params: Vec<Name>,
    pub typ: Arc<Expr>,
}

#[derive(Debug)]
pub enum Expr {
    Bvar(Nat, u64),
    Fvar(Name, u64),
    Mvar(Name, u64),
    Sort(Level, u64),
    Const(Name, Vec<Level>, u64),
    App(Arc<Expr>, Arc<Expr>, u64),
    Lam(Name, Arc<Expr>, Arc<Expr>, BinderInfo, u64),
    ForallE(Name, Arc<Expr>, Arc<Expr>, BinderInfo, u64),
    LetE(Name, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool, u64),
    Lit(Literal, u64),
    Mdata(Vec<(Name, DataValue)>, Arc<Expr>, u64),
    Proj(Name, Nat, Arc<Expr>, u64),
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

#[derive(Debug)]
pub enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    Imax(Box<Level>, Box<Level>),
    Param(Name),
    Mvar(Name),
}

#[derive(Debug)]
pub struct RecursorRule {
    pub ctor: Name,
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

#[derive(Debug)]
pub enum Literal {
    NatVal(Nat),
    StrVal(String),
}

#[derive(Debug)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

#[derive(Debug)]
pub enum Int {
    OfNat(Nat),
    NegSucc(Nat),
}

#[derive(Debug)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Name),
    OfNat(Nat),
    OfInt(Int),
    OfSyntax(Box<Syntax>),
}

#[derive(Debug)]
pub enum Syntax {
    Missing,
    Node(SourceInfo, Name, Vec<Syntax>),
    Atom(SourceInfo, String),
    Ident(SourceInfo, Substring, Name, Vec<SyntaxPreresolved>),
}

#[derive(Debug)]
pub enum SyntaxPreresolved {
    Namespace(Name),
    Decl(Name, Vec<String>),
}

#[derive(Debug)]
pub enum SourceInfo {
    Original(Substring, Nat, Substring, Nat),
    Synthetic(Nat, Nat, bool),
    None,
}

#[derive(Debug)]
pub struct Substring {
    pub str: String,
    pub start_pos: Nat,
    pub stop_pos: Nat,
}
