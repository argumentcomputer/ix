use std::{
  hash::{Hash, Hasher},
  sync::Arc,
};

use crate::lean::nat::Nat;
use rustc_hash::{FxHashMap, FxHasher};

#[derive(PartialEq, Eq, Debug, PartialOrd, Ord, Clone)]
pub struct Name(pub Arc<NameData>);

#[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum NameData {
  Anonymous,
  Str(Name, String, u64),
  Num(Name, Nat, u64),
}

impl Name {
  pub fn as_data(&self) -> &NameData {
    &self.0
  }

  pub fn get_hash(&self) -> u64 {
    match *self.0 {
      NameData::Anonymous => 0,
      NameData::Str(.., h) | NameData::Num(.., h) => h,
    }
  }
  pub fn anon() -> Self {
    Name(Arc::new(NameData::Anonymous))
  }

  pub fn str(pre: Name, s: String) -> Self {
    let hasher = &mut FxHasher::default();
    (7, pre.get_hash(), &s).hash(hasher);
    Name(Arc::new(NameData::Str(pre, s, hasher.finish())))
  }

  pub fn num(pre: Name, n: Nat) -> Name {
    let hasher = &mut FxHasher::default();
    (11, pre.get_hash(), &n).hash(hasher);
    Name(Arc::new(NameData::Num(pre, n, hasher.finish())))
  }
}

impl Hash for Name {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.get_hash().hash(state);
  }
}

#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub struct Level(pub Arc<LevelData>);

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum LevelData {
  Zero,
  Succ(Level),
  Max(Level, Level),
  Imax(Level, Level),
  Param(Name),
  Mvar(Name),
}

impl Level {
  pub fn as_data(&self) -> &LevelData {
    &self.0
  }
  pub fn zero() -> Self {
    Level(Arc::new(LevelData::Zero))
  }
  pub fn succ(x: Level) -> Self {
    Level(Arc::new(LevelData::Succ(x)))
  }
  pub fn max(x: Level, y: Level) -> Self {
    Level(Arc::new(LevelData::Max(x, y)))
  }
  pub fn imax(x: Level, y: Level) -> Self {
    Level(Arc::new(LevelData::Imax(x, y)))
  }
  pub fn param(x: Name) -> Self {
    Level(Arc::new(LevelData::Param(x)))
  }
  pub fn mvar(x: Name) -> Self {
    Level(Arc::new(LevelData::Mvar(x)))
  }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
  NatVal(Nat),
  StrVal(String),
}

impl PartialOrd for Literal {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

// should match Literal.lt here https://github.com/leanprover/lean4/blob/fe21b950586cde248dae4b2a0f59d43c1f19cd87/src/Lean/Expr.lean#L34
// TODO: test that Nat and String comparisons match
impl Ord for Literal {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    match (self, other) {
      (Literal::NatVal(a), Literal::NatVal(b)) => a.cmp(b),
      (Literal::StrVal(a), Literal::StrVal(b)) => a.cmp(b),
      (Literal::NatVal(_), Literal::StrVal(_)) => std::cmp::Ordering::Less,
      (Literal::StrVal(_), Literal::NatVal(_)) => std::cmp::Ordering::Greater,
    }
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplicit,
  InstImplicit,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Int {
  OfNat(Nat),
  NegSucc(Nat),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Substring {
  pub str: String,
  pub start_pos: Nat,
  pub stop_pos: Nat,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SourceInfo {
  Original(Substring, Nat, Substring, Nat),
  Synthetic(Nat, Nat, bool),
  None,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SyntaxPreresolved {
  Namespace(Name),
  Decl(Name, Vec<String>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Syntax {
  Missing,
  Node(SourceInfo, Name, Vec<Syntax>),
  Atom(SourceInfo, String),
  Ident(SourceInfo, Substring, Name, Vec<SyntaxPreresolved>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DataValue {
  OfString(String),
  OfBool(bool),
  OfName(Name),
  OfNat(Nat),
  OfInt(Int),
  OfSyntax(Box<Syntax>),
}

#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub struct Expr(pub Arc<ExprData>);

#[derive(Debug, PartialEq, Eq)]
pub enum ExprData {
  Bvar(Nat, u64),
  Fvar(Name, u64),
  Mvar(Name, u64),
  Sort(Level, u64),
  Const(Name, Vec<Level>, u64),
  App(Expr, Expr, u64),
  Lam(Name, Expr, Expr, BinderInfo, u64),
  ForallE(Name, Expr, Expr, BinderInfo, u64),
  LetE(Name, Expr, Expr, Expr, bool, u64),
  Lit(Literal, u64),
  Mdata(Vec<(Name, DataValue)>, Expr, u64),
  Proj(Name, Nat, Expr, u64),
}

impl Expr {
  pub fn as_data(&self) -> &ExprData {
    &self.0
  }
  pub fn bvar(x: Nat, h: u64) -> Self {
    Expr(Arc::new(ExprData::Bvar(x, h)))
  }
  pub fn fvar(x: Name, h: u64) -> Self {
    Expr(Arc::new(ExprData::Fvar(x, h)))
  }
  pub fn mvar(x: Name, h: u64) -> Self {
    Expr(Arc::new(ExprData::Mvar(x, h)))
  }
  pub fn sort(x: Level, h: u64) -> Self {
    Expr(Arc::new(ExprData::Sort(x, h)))
  }
  pub fn cnst(x: Name, us: Vec<Level>, h: u64) -> Self {
    Expr(Arc::new(ExprData::Const(x, us, h)))
  }
  pub fn app(x: Expr, y: Expr, h: u64) -> Self {
    Expr(Arc::new(ExprData::App(x, y, h)))
  }
  pub fn lam(n: Name, x: Expr, y: Expr, b: BinderInfo, h: u64) -> Self {
    Expr(Arc::new(ExprData::Lam(n, x, y, b, h)))
  }
  pub fn all(n: Name, x: Expr, y: Expr, b: BinderInfo, h: u64) -> Self {
    Expr(Arc::new(ExprData::ForallE(n, x, y, b, h)))
  }
  #[allow(non_snake_case)]
  pub fn letE(n: Name, x: Expr, y: Expr, z: Expr, b: bool, h: u64) -> Self {
    Expr(Arc::new(ExprData::LetE(n, x, y, z, b, h)))
  }
  pub fn lit(x: Literal, h: u64) -> Self {
    Expr(Arc::new(ExprData::Lit(x, h)))
  }
  pub fn mdata(xs: Vec<(Name, DataValue)>, x: Expr, h: u64) -> Self {
    Expr(Arc::new(ExprData::Mdata(xs, x, h)))
  }
  pub fn proj(n: Name, i: Nat, x: Expr, h: u64) -> Self {
    Expr(Arc::new(ExprData::Proj(n, i, x, h)))
  }
}

impl Hash for ExprData {
  fn hash<H: Hasher>(&self, state: &mut H) {
    match self {
      ExprData::Bvar(_, h)
      | ExprData::Fvar(_, h)
      | ExprData::Mvar(_, h)
      | ExprData::Sort(_, h)
      | ExprData::Const(.., h)
      | ExprData::App(.., h)
      | ExprData::Lam(.., h)
      | ExprData::ForallE(.., h)
      | ExprData::LetE(.., h)
      | ExprData::Lit(_, h)
      | ExprData::Mdata(.., h)
      | ExprData::Proj(.., h) => h.hash(state),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHints {
  Opaque,
  Abbrev,
  Regular(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
  Unsafe,
  Safe,
  Partial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantVal {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
}

#[derive(Debug, Clone)]
pub struct AxiomVal {
  pub cnst: ConstantVal,
  pub is_unsafe: bool,
}

#[derive(Debug, Clone)]
pub struct DefinitionVal {
  pub cnst: ConstantVal,
  pub value: Expr,
  pub hints: ReducibilityHints,
  pub safety: DefinitionSafety,
  pub all: Vec<Name>,
}

#[derive(Debug, Clone)]
pub struct TheoremVal {
  pub cnst: ConstantVal,
  pub value: Expr,
  pub all: Vec<Name>,
}

#[derive(Debug, Clone)]
pub struct OpaqueVal {
  pub cnst: ConstantVal,
  pub value: Expr,
  pub is_unsafe: bool,
  pub all: Vec<Name>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

#[derive(Debug, Clone)]
pub struct QuotVal {
  pub cnst: ConstantVal,
  pub kind: QuotKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveVal {
  pub cnst: ConstantVal,
  pub num_params: Nat,
  pub num_indices: Nat,
  pub all: Vec<Name>,
  pub ctors: Vec<Name>,
  pub num_nested: Nat,
  pub is_rec: bool,
  pub is_unsafe: bool,
  pub is_reflexive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorVal {
  pub cnst: ConstantVal,
  pub induct: Name,
  pub cidx: Nat,
  pub num_params: Nat,
  pub num_fields: Nat,
  pub is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorRule {
  pub ctor: Name,
  pub n_fields: Nat,
  pub rhs: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorVal {
  pub cnst: ConstantVal,
  pub all: Vec<Name>,
  pub num_params: Nat,
  pub num_indices: Nat,
  pub num_motives: Nat,
  pub num_minors: Nat,
  pub rules: Vec<RecursorRule>,
  pub k: bool,
  pub is_unsafe: bool,
}

#[derive(Debug, Clone)]
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

pub type Env = FxHashMap<Name, ConstantInfo>;
