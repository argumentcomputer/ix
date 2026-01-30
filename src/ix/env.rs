use blake3::Hash;
use std::{
  hash::{Hash as StdHash, Hasher},
  sync::Arc,
};

use crate::lean::nat::Nat;
use rustc_hash::FxHashMap;

// LEON: Lean Environment Objective Notation
// These tags roughly correspond to Ixon tags
pub const NANON: u8 = 0x00;
pub const NSTR: u8 = 0x01;
pub const NNUM: u8 = 0x02;
pub const UZERO: u8 = 0x03;
pub const USUCC: u8 = 0x04;
pub const UMAX: u8 = 0x05;
pub const UIMAX: u8 = 0x06;
pub const UPARAM: u8 = 0x10;
pub const UMVAR: u8 = 0x70;
pub const EVAR: u8 = 0x20;
pub const ESORT: u8 = 0x80;
pub const EREF: u8 = 0x30;
pub const EPRJ: u8 = 0x50;
pub const ESTR: u8 = 0x81;
pub const ENAT: u8 = 0x82;
pub const EAPP: u8 = 0x83;
pub const ELAM: u8 = 0x84;
pub const EALL: u8 = 0x85;
pub const ELET: u8 = 0x86;
pub const EFVAR: u8 = 0x72;
pub const EMVAR: u8 = 0x73;
pub const EMDATA: u8 = 0x74;
pub const DEFN: u8 = 0xA0;
pub const RECR: u8 = 0xA1;
pub const AXIO: u8 = 0xA2;
pub const QUOT: u8 = 0xA3;
pub const INDC: u8 = 0xA6;
pub const CTOR: u8 = 0xC0;
pub const THEO: u8 = 0xC1;
pub const OPAQ: u8 = 0xC2;
pub const MINT: u8 = 0xF1;
pub const MSSTR: u8 = 0xF2;
pub const MSINFO: u8 = 0xF3;
pub const MSPRE: u8 = 0xF4;
pub const MSYN: u8 = 0xF5;
pub const MDVAL: u8 = 0xF6;

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Name(pub Arc<NameData>);

impl PartialOrd for Name {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for Name {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.get_hash().as_bytes().cmp(other.get_hash().as_bytes())
  }
}

#[derive(PartialEq, Eq, Debug)]
pub enum NameData {
  Anonymous(Hash),
  Str(Name, String, Hash),
  Num(Name, Nat, Hash),
}

impl Name {
  pub fn as_data(&self) -> &NameData {
    &self.0
  }

  pub fn get_hash(&self) -> Hash {
    match *self.0 {
      NameData::Anonymous(h) | NameData::Str(.., h) | NameData::Num(.., h) => h,
    }
  }
  pub fn anon() -> Self {
    let hash = blake3::hash(&[NANON]);
    Name(Arc::new(NameData::Anonymous(hash)))
  }

  pub fn str(pre: Name, s: String) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[NSTR]);
    hasher.update(pre.get_hash().as_bytes());
    hasher.update(s.as_bytes());
    let hash = hasher.finalize();
    Name(Arc::new(NameData::Str(pre, s, hash)))
  }

  pub fn num(pre: Name, n: Nat) -> Name {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[NNUM]);
    hasher.update(pre.get_hash().as_bytes());
    hasher.update(&n.to_le_bytes());
    let hash = hasher.finalize();
    Name(Arc::new(NameData::Num(pre, n, hash)))
  }
  pub fn pretty(&self) -> String {
    let mut components = Vec::new();
    let mut current = self;

    loop {
      match current.as_data() {
        NameData::Anonymous(_) => break,
        NameData::Str(pre, s, _) => {
          components.push(s.as_str().to_owned());
          current = pre;
        },
        NameData::Num(pre, n, _) => {
          components.push(n.0.to_string());
          current = pre;
        },
      }
    }

    components.reverse();
    components.join(".")
  }
}

impl StdHash for Name {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.get_hash().hash(state);
  }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Level(pub Arc<LevelData>);

#[derive(Debug, PartialEq, Eq)]
pub enum LevelData {
  Zero(Hash),
  Succ(Level, Hash),
  Max(Level, Level, Hash),
  Imax(Level, Level, Hash),
  Param(Name, Hash),
  Mvar(Name, Hash),
}

impl Level {
  pub fn as_data(&self) -> &LevelData {
    &self.0
  }

  pub fn get_hash(&self) -> &Hash {
    match &*self.0 {
      LevelData::Zero(h)
      | LevelData::Succ(_, h)
      | LevelData::Max(.., h)
      | LevelData::Imax(.., h)
      | LevelData::Param(_, h)
      | LevelData::Mvar(_, h) => h,
    }
  }
  pub fn zero() -> Self {
    Level(Arc::new(LevelData::Zero(blake3::hash(&[UZERO]))))
  }
  pub fn succ(x: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[USUCC]);
    hasher.update(x.get_hash().as_bytes());
    Level(Arc::new(LevelData::Succ(x, hasher.finalize())))
  }
  pub fn max(x: Level, y: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UMAX]);
    hasher.update(x.get_hash().as_bytes());
    hasher.update(y.get_hash().as_bytes());
    Level(Arc::new(LevelData::Max(x, y, hasher.finalize())))
  }
  pub fn imax(x: Level, y: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UIMAX]);
    hasher.update(x.get_hash().as_bytes());
    hasher.update(y.get_hash().as_bytes());
    Level(Arc::new(LevelData::Imax(x, y, hasher.finalize())))
  }
  pub fn param(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UPARAM]);
    hasher.update(x.get_hash().as_bytes());
    Level(Arc::new(LevelData::Param(x, hasher.finalize())))
  }
  pub fn mvar(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UMVAR]);
    hasher.update(x.get_hash().as_bytes());
    Level(Arc::new(LevelData::Mvar(x, hasher.finalize())))
  }
}

impl StdHash for Level {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.get_hash().as_bytes().hash(state);
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

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum BinderInfo {
  Default,
  Implicit,
  StrictImplicit,
  InstImplicit,
}

fn binder_info_tag(bi: &BinderInfo) -> u8 {
  match bi {
    BinderInfo::Default => 0,
    BinderInfo::Implicit => 1,
    BinderInfo::StrictImplicit => 2,
    BinderInfo::InstImplicit => 3,
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Int {
  OfNat(Nat),
  NegSucc(Nat),
}

fn hash_int(i: &Int, hasher: &mut blake3::Hasher) {
  hasher.update(&[MINT]);
  match i {
    Int::OfNat(n) => {
      hasher.update(&[0]);
      hasher.update(&n.to_le_bytes());
    },
    Int::NegSucc(n) => {
      hasher.update(&[1]);
      hasher.update(&n.to_le_bytes());
    },
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Substring {
  pub str: String,
  pub start_pos: Nat,
  pub stop_pos: Nat,
}

fn hash_substring(ss: &Substring, hasher: &mut blake3::Hasher) {
  hasher.update(&[MSSTR]);
  hasher.update(ss.str.as_bytes());
  hasher.update(&ss.start_pos.to_le_bytes());
  hasher.update(&ss.stop_pos.to_le_bytes());
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SourceInfo {
  Original(Substring, Nat, Substring, Nat),
  Synthetic(Nat, Nat, bool),
  None,
}

fn hash_source_info(si: &SourceInfo, hasher: &mut blake3::Hasher) {
  hasher.update(&[MSINFO]);
  match si {
    SourceInfo::Original(leading, leading_pos, trailing, trailing_pos) => {
      hasher.update(&[0]);
      hash_substring(leading, hasher);
      hasher.update(&leading_pos.to_le_bytes());
      hash_substring(trailing, hasher);
      hasher.update(&trailing_pos.to_le_bytes());
    },
    SourceInfo::Synthetic(start, stop, canonical) => {
      hasher.update(&[1]);
      hasher.update(&start.to_le_bytes());
      hasher.update(&stop.to_le_bytes());
      hasher.update(&[*canonical as u8]);
    },
    SourceInfo::None => {
      hasher.update(&[2]);
    },
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SyntaxPreresolved {
  Namespace(Name),
  Decl(Name, Vec<String>),
}

fn hash_syntax_preresolved(
  sp: &SyntaxPreresolved,
  hasher: &mut blake3::Hasher,
) {
  hasher.update(&[MSPRE]);
  match sp {
    SyntaxPreresolved::Namespace(name) => {
      hasher.update(&[0]);
      hasher.update(name.get_hash().as_bytes());
    },
    SyntaxPreresolved::Decl(name, aliases) => {
      hasher.update(&[1]);
      hasher.update(name.get_hash().as_bytes());
      for alias in aliases {
        hasher.update(alias.as_bytes());
        hasher.update(&[0]); // null terminator for each string
      }
    },
  }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Syntax {
  Missing,
  Node(SourceInfo, Name, Vec<Syntax>),
  Atom(SourceInfo, String),
  Ident(SourceInfo, Substring, Name, Vec<SyntaxPreresolved>),
}

fn hash_syntax(syn: &Syntax, hasher: &mut blake3::Hasher) {
  hasher.update(&[MSYN]);
  match syn {
    Syntax::Missing => {
      hasher.update(&[0]);
    },
    Syntax::Node(info, kind, args) => {
      hasher.update(&[1]);
      hash_source_info(info, hasher);
      hasher.update(kind.get_hash().as_bytes());
      hasher.update(&Nat::from(args.len() as u64).to_le_bytes());
      for arg in args {
        hash_syntax(arg, hasher);
      }
    },
    Syntax::Atom(info, val) => {
      hasher.update(&[2]);
      hash_source_info(info, hasher);
      hasher.update(val.as_bytes());
    },
    Syntax::Ident(info, raw_val, val, preresolved) => {
      hasher.update(&[3]);
      hash_source_info(info, hasher);
      hash_substring(raw_val, hasher);
      hasher.update(val.get_hash().as_bytes());
      hasher.update(&Nat::from(preresolved.len() as u64).to_le_bytes());
      for pr in preresolved {
        hash_syntax_preresolved(pr, hasher);
      }
    },
  }
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

fn hash_data_value(dv: &DataValue, hasher: &mut blake3::Hasher) {
  hasher.update(&[MDVAL]);
  match dv {
    DataValue::OfString(s) => {
      hasher.update(&[0]);
      hasher.update(s.as_bytes());
    },
    DataValue::OfBool(b) => {
      hasher.update(&[1]);
      hasher.update(&[*b as u8]);
    },
    DataValue::OfName(name) => {
      hasher.update(&[2]);
      hasher.update(name.get_hash().as_bytes());
    },
    DataValue::OfNat(n) => {
      hasher.update(&[3]);
      hasher.update(&n.to_le_bytes());
    },
    DataValue::OfInt(i) => {
      hasher.update(&[4]);
      hash_int(i, hasher);
    },
    DataValue::OfSyntax(syn) => {
      hasher.update(&[5]);
      hash_syntax(syn, hasher);
    },
  }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Expr(pub Arc<ExprData>);

#[derive(Debug, PartialEq, Eq)]
pub enum ExprData {
  Bvar(Nat, Hash),
  Fvar(Name, Hash),
  Mvar(Name, Hash),
  Sort(Level, Hash),
  Const(Name, Vec<Level>, Hash),
  App(Expr, Expr, Hash),
  Lam(Name, Expr, Expr, BinderInfo, Hash),
  ForallE(Name, Expr, Expr, BinderInfo, Hash),
  LetE(Name, Expr, Expr, Expr, bool, Hash),
  Lit(Literal, Hash),
  Mdata(Vec<(Name, DataValue)>, Expr, Hash),
  Proj(Name, Nat, Expr, Hash),
}

impl Expr {
  pub fn as_data(&self) -> &ExprData {
    &self.0
  }

  pub fn get_hash(&self) -> &Hash {
    match &*self.0 {
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
      | ExprData::Proj(.., h) => h,
    }
  }
  pub fn bvar(x: Nat) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EVAR]);
    hasher.update(&x.to_le_bytes());
    Expr(Arc::new(ExprData::Bvar(x, hasher.finalize())))
  }

  pub fn fvar(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EFVAR]);
    hasher.update(x.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Fvar(x, hasher.finalize())))
  }

  pub fn mvar(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EMVAR]);
    hasher.update(x.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Mvar(x, hasher.finalize())))
  }

  pub fn sort(x: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[ESORT]);
    hasher.update(x.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Sort(x, hasher.finalize())))
  }

  pub fn cnst(x: Name, us: Vec<Level>) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EREF]);
    hasher.update(x.get_hash().as_bytes());
    for u in &us {
      hasher.update(u.get_hash().as_bytes());
    }
    Expr(Arc::new(ExprData::Const(x, us, hasher.finalize())))
  }

  pub fn app(f: Expr, a: Expr) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EAPP]);
    hasher.update(f.get_hash().as_bytes());
    hasher.update(a.get_hash().as_bytes());
    Expr(Arc::new(ExprData::App(f, a, hasher.finalize())))
  }

  pub fn lam(n: Name, t: Expr, b: Expr, bi: BinderInfo) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[ELAM]);
    hasher.update(n.get_hash().as_bytes());
    hasher.update(t.get_hash().as_bytes());
    hasher.update(b.get_hash().as_bytes());
    hasher.update(&[binder_info_tag(&bi)]);
    Expr(Arc::new(ExprData::Lam(n, t, b, bi, hasher.finalize())))
  }

  pub fn all(n: Name, t: Expr, b: Expr, bi: BinderInfo) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EALL]);
    hasher.update(n.get_hash().as_bytes());
    hasher.update(t.get_hash().as_bytes());
    hasher.update(b.get_hash().as_bytes());
    hasher.update(&[binder_info_tag(&bi)]);
    Expr(Arc::new(ExprData::ForallE(n, t, b, bi, hasher.finalize())))
  }

  #[allow(non_snake_case)]
  pub fn letE(n: Name, t: Expr, v: Expr, b: Expr, nd: bool) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[ELET]);
    hasher.update(n.get_hash().as_bytes());
    hasher.update(t.get_hash().as_bytes());
    hasher.update(v.get_hash().as_bytes());
    hasher.update(b.get_hash().as_bytes());
    hasher.update(&[nd as u8]);
    Expr(Arc::new(ExprData::LetE(n, t, v, b, nd, hasher.finalize())))
  }

  pub fn lit(x: Literal) -> Self {
    let mut hasher = blake3::Hasher::new();
    match &x {
      Literal::NatVal(n) => {
        hasher.update(&[ENAT]);
        hasher.update(&n.to_le_bytes());
      },
      Literal::StrVal(s) => {
        hasher.update(&[ESTR]);
        hasher.update(s.as_bytes());
      },
    };
    Expr(Arc::new(ExprData::Lit(x, hasher.finalize())))
  }

  pub fn mdata(xs: Vec<(Name, DataValue)>, e: Expr) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EMDATA]);
    hasher.update(&Nat::from(xs.len() as u64).to_le_bytes());
    for (name, dv) in &xs {
      hasher.update(name.get_hash().as_bytes());
      hash_data_value(dv, &mut hasher);
    }
    hasher.update(e.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Mdata(xs, e, hasher.finalize())))
  }

  pub fn proj(n: Name, i: Nat, e: Expr) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EPRJ]);
    hasher.update(n.get_hash().as_bytes());
    hasher.update(&i.to_le_bytes());
    hasher.update(e.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Proj(n, i, e, hasher.finalize())))
  }
}

impl StdHash for Expr {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.get_hash().as_bytes().hash(state);
  }
}

impl StdHash for ExprData {
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
      | ExprData::Proj(.., h) => h.as_bytes().hash(state),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ReducibilityHints {
  #[default]
  Opaque,
  Abbrev,
  Regular(u32),
}

fn hash_reducibility_hints(
  hints: &ReducibilityHints,
  hasher: &mut blake3::Hasher,
) {
  match hints {
    ReducibilityHints::Opaque => {
      hasher.update(&[0]);
    },
    ReducibilityHints::Abbrev => {
      hasher.update(&[1]);
    },
    ReducibilityHints::Regular(h) => {
      hasher.update(&[2]);
      hasher.update(&h.to_le_bytes());
    },
  };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
  Unsafe,
  Safe,
  Partial,
}

fn hash_definition_safety(
  safety: &DefinitionSafety,
  hasher: &mut blake3::Hasher,
) {
  match safety {
    DefinitionSafety::Unsafe => hasher.update(&[0]),
    DefinitionSafety::Safe => hasher.update(&[1]),
    DefinitionSafety::Partial => hasher.update(&[2]),
  };
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantVal {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
}

fn hash_constant_val(cv: &ConstantVal, hasher: &mut blake3::Hasher) {
  hasher.update(cv.name.get_hash().as_bytes());
  hasher.update(&(cv.level_params.len() as u64).to_le_bytes());
  for lp in &cv.level_params {
    hasher.update(lp.get_hash().as_bytes());
  }
  hasher.update(cv.typ.get_hash().as_bytes());
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

fn hash_quot_kind(kind: &QuotKind, hasher: &mut blake3::Hasher) {
  match kind {
    QuotKind::Type => hasher.update(&[0]),
    QuotKind::Ctor => hasher.update(&[1]),
    QuotKind::Lift => hasher.update(&[2]),
    QuotKind::Ind => hasher.update(&[3]),
  };
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

fn hash_recursor_rule(rule: &RecursorRule, hasher: &mut blake3::Hasher) {
  hasher.update(rule.ctor.get_hash().as_bytes());
  hasher.update(&rule.n_fields.to_le_bytes());
  hasher.update(rule.rhs.get_hash().as_bytes());
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

impl ConstantInfo {
  pub fn get_hash(&self) -> Hash {
    let mut hasher = blake3::Hasher::new();
    match self {
      ConstantInfo::AxiomInfo(v) => {
        hasher.update(&[AXIO]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(&[v.is_unsafe as u8]);
      },
      ConstantInfo::DefnInfo(v) => {
        hasher.update(&[DEFN]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(v.value.get_hash().as_bytes());
        hash_reducibility_hints(&v.hints, &mut hasher);
        hash_definition_safety(&v.safety, &mut hasher);
        hasher.update(&(v.all.len() as u64).to_le_bytes());
        for name in &v.all {
          hasher.update(name.get_hash().as_bytes());
        }
      },
      ConstantInfo::ThmInfo(v) => {
        hasher.update(&[THEO]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(v.value.get_hash().as_bytes());
        hasher.update(&(v.all.len() as u64).to_le_bytes());
        for name in &v.all {
          hasher.update(name.get_hash().as_bytes());
        }
      },
      ConstantInfo::OpaqueInfo(v) => {
        hasher.update(&[OPAQ]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(v.value.get_hash().as_bytes());
        hasher.update(&[v.is_unsafe as u8]);
        hasher.update(&(v.all.len() as u64).to_le_bytes());
        for name in &v.all {
          hasher.update(name.get_hash().as_bytes());
        }
      },
      ConstantInfo::QuotInfo(v) => {
        hasher.update(&[QUOT]);
        hash_constant_val(&v.cnst, &mut hasher);
        hash_quot_kind(&v.kind, &mut hasher);
      },
      ConstantInfo::InductInfo(v) => {
        hasher.update(&[INDC]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(&v.num_params.to_le_bytes());
        hasher.update(&v.num_indices.to_le_bytes());
        hasher.update(&(v.all.len() as u64).to_le_bytes());
        for name in &v.all {
          hasher.update(name.get_hash().as_bytes());
        }
        hasher.update(&(v.ctors.len() as u64).to_le_bytes());
        for name in &v.ctors {
          hasher.update(name.get_hash().as_bytes());
        }
        hasher.update(&v.num_nested.to_le_bytes());
        hasher.update(&[v.is_rec as u8]);
        hasher.update(&[v.is_unsafe as u8]);
        hasher.update(&[v.is_reflexive as u8]);
      },
      ConstantInfo::CtorInfo(v) => {
        hasher.update(&[CTOR]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(v.induct.get_hash().as_bytes());
        hasher.update(&v.cidx.to_le_bytes());
        hasher.update(&v.num_params.to_le_bytes());
        hasher.update(&v.num_fields.to_le_bytes());
        hasher.update(&[v.is_unsafe as u8]);
      },
      ConstantInfo::RecInfo(v) => {
        hasher.update(&[RECR]);
        hash_constant_val(&v.cnst, &mut hasher);
        hasher.update(&(v.all.len() as u64).to_le_bytes());
        for name in &v.all {
          hasher.update(name.get_hash().as_bytes());
        }
        hasher.update(&v.num_params.to_le_bytes());
        hasher.update(&v.num_indices.to_le_bytes());
        hasher.update(&v.num_motives.to_le_bytes());
        hasher.update(&v.num_minors.to_le_bytes());
        hasher.update(&(v.rules.len() as u64).to_le_bytes());
        for rule in &v.rules {
          hash_recursor_rule(rule, &mut hasher);
        }
        hasher.update(&[v.k as u8]);
        hasher.update(&[v.is_unsafe as u8]);
      },
    }
    hasher.finalize()
  }

  pub fn get_name(&self) -> &Name {
    match self {
      ConstantInfo::AxiomInfo(v) => &v.cnst.name,
      ConstantInfo::DefnInfo(v) => &v.cnst.name,
      ConstantInfo::ThmInfo(v) => &v.cnst.name,
      ConstantInfo::OpaqueInfo(v) => &v.cnst.name,
      ConstantInfo::QuotInfo(v) => &v.cnst.name,
      ConstantInfo::InductInfo(v) => &v.cnst.name,
      ConstantInfo::CtorInfo(v) => &v.cnst.name,
      ConstantInfo::RecInfo(v) => &v.cnst.name,
    }
  }

  pub fn get_type(&self) -> &Expr {
    match self {
      ConstantInfo::AxiomInfo(v) => &v.cnst.typ,
      ConstantInfo::DefnInfo(v) => &v.cnst.typ,
      ConstantInfo::ThmInfo(v) => &v.cnst.typ,
      ConstantInfo::OpaqueInfo(v) => &v.cnst.typ,
      ConstantInfo::QuotInfo(v) => &v.cnst.typ,
      ConstantInfo::InductInfo(v) => &v.cnst.typ,
      ConstantInfo::CtorInfo(v) => &v.cnst.typ,
      ConstantInfo::RecInfo(v) => &v.cnst.typ,
    }
  }

  pub fn get_level_params(&self) -> &Vec<Name> {
    match self {
      ConstantInfo::AxiomInfo(v) => &v.cnst.level_params,
      ConstantInfo::DefnInfo(v) => &v.cnst.level_params,
      ConstantInfo::ThmInfo(v) => &v.cnst.level_params,
      ConstantInfo::OpaqueInfo(v) => &v.cnst.level_params,
      ConstantInfo::QuotInfo(v) => &v.cnst.level_params,
      ConstantInfo::InductInfo(v) => &v.cnst.level_params,
      ConstantInfo::CtorInfo(v) => &v.cnst.level_params,
      ConstantInfo::RecInfo(v) => &v.cnst.level_params,
    }
  }
}

pub type Env = FxHashMap<Name, ConstantInfo>;
