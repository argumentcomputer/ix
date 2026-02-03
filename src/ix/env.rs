//! LEON (Lean Environment Objective Notation) types.
//!
//! This module defines a content-addressed representation of the Lean 4 kernel
//! type system. Every term, name, universe level, and constant is hashed with
//! Blake3 to produce a deterministic content address.
//!
//! Constructor tags (`NANON`, `NSTR`, `EVAR`, `DEFN`, etc.) are single-byte
//! discriminants prepended to the hasher input so that structurally identical
//! subtrees in different syntactic categories never collide.

use blake3::Hash;
use std::{
  hash::{Hash as StdHash, Hasher},
  sync::Arc,
};

use crate::lean::nat::Nat;
use rustc_hash::FxHashMap;

// -- Name tags ----------------------------------------------------------------

/// Tag for the anonymous (root) name.
pub const NANON: u8 = 0x00;
/// Tag for a string name component.
pub const NSTR: u8 = 0x01;
/// Tag for a numeric name component.
pub const NNUM: u8 = 0x02;

// -- Level tags ---------------------------------------------------------------

/// Tag for universe level zero.
pub const UZERO: u8 = 0x03;
/// Tag for universe level successor.
pub const USUCC: u8 = 0x04;
/// Tag for universe level max.
pub const UMAX: u8 = 0x05;
/// Tag for universe level imax.
pub const UIMAX: u8 = 0x06;
/// Tag for a universe level parameter.
pub const UPARAM: u8 = 0x10;
/// Tag for a universe level metavariable.
pub const UMVAR: u8 = 0x70;

// -- Expr tags ----------------------------------------------------------------

/// Tag for a bound variable (de Bruijn index).
pub const EVAR: u8 = 0x20;
/// Tag for a sort expression.
pub const ESORT: u8 = 0x80;
/// Tag for a constant reference.
pub const EREF: u8 = 0x30;
/// Tag for a projection expression.
pub const EPRJ: u8 = 0x50;
/// Tag for a string literal expression.
pub const ESTR: u8 = 0x81;
/// Tag for a natural number literal expression.
pub const ENAT: u8 = 0x82;
/// Tag for a function application.
pub const EAPP: u8 = 0x83;
/// Tag for a lambda abstraction.
pub const ELAM: u8 = 0x84;
/// Tag for a dependent function type (forall / Pi).
pub const EALL: u8 = 0x85;
/// Tag for a let-binding.
pub const ELET: u8 = 0x86;
/// Tag for a free variable.
pub const EFVAR: u8 = 0x72;
/// Tag for an expression metavariable.
pub const EMVAR: u8 = 0x73;
/// Tag for metadata-annotated expressions.
pub const EMDATA: u8 = 0x74;

// -- Constant tags ------------------------------------------------------------

/// Tag for a definition constant.
pub const DEFN: u8 = 0xA0;
/// Tag for a recursor constant.
pub const RECR: u8 = 0xA1;
/// Tag for an axiom constant.
pub const AXIO: u8 = 0xA2;
/// Tag for a quotient constant.
pub const QUOT: u8 = 0xA3;
/// Tag for an inductive type constant.
pub const INDC: u8 = 0xA6;
/// Tag for a constructor constant.
pub const CTOR: u8 = 0xC0;
/// Tag for a theorem constant.
pub const THEO: u8 = 0xC1;
/// Tag for an opaque constant.
pub const OPAQ: u8 = 0xC2;

// -- Metadata tags ------------------------------------------------------------

/// Tag for an integer metadata value.
pub const MINT: u8 = 0xF1;
/// Tag for a substring metadata value.
pub const MSSTR: u8 = 0xF2;
/// Tag for source info metadata.
pub const MSINFO: u8 = 0xF3;
/// Tag for syntax pre-resolution metadata.
pub const MSPRE: u8 = 0xF4;
/// Tag for syntax tree metadata.
pub const MSYN: u8 = 0xF5;
/// Tag for a generic data value in metadata.
pub const MDVAL: u8 = 0xF6;

/// A content-addressed hierarchical name.
///
/// Names are interned via `Arc` and compared/hashed by their Blake3 digest.
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

/// The underlying data for a [`Name`].
///
/// Each variant carries its precomputed Blake3 hash as the last field.
#[derive(PartialEq, Eq, Debug)]
pub enum NameData {
  /// The root (empty) name.
  Anonymous(Hash),
  /// A string component appended to a prefix name.
  Str(Name, String, Hash),
  /// A numeric component appended to a prefix name.
  Num(Name, Nat, Hash),
}

impl Name {
  /// Returns a reference to the inner [`NameData`].
  pub fn as_data(&self) -> &NameData {
    &self.0
  }

  /// Returns the precomputed Blake3 hash of this name.
  pub fn get_hash(&self) -> &Hash {
    match self.0.as_ref() {
      NameData::Anonymous(h) | NameData::Str(.., h) | NameData::Num(.., h) => h,
    }
  }
  /// Constructs the anonymous (root) name.
  pub fn anon() -> Self {
    let hash = blake3::hash(&[NANON]);
    Name(Arc::new(NameData::Anonymous(hash)))
  }

  /// Constructs a name by appending a string component to `pre`.
  pub fn str(pre: Name, s: String) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[NSTR]);
    hasher.update(pre.get_hash().as_bytes());
    hasher.update(s.as_bytes());
    let hash = hasher.finalize();
    Name(Arc::new(NameData::Str(pre, s, hash)))
  }

  /// Constructs a name by appending a numeric component to `pre`.
  pub fn num(pre: Name, n: Nat) -> Name {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[NNUM]);
    hasher.update(pre.get_hash().as_bytes());
    hasher.update(&n.to_le_bytes());
    let hash = hasher.finalize();
    Name(Arc::new(NameData::Num(pre, n, hash)))
  }
  /// Returns a dot-separated human-readable representation of this name.
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

/// A content-addressed universe level.
///
/// Levels are interned via `Arc` and compared/hashed by their Blake3 digest.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Level(pub Arc<LevelData>);

/// The underlying data for a [`Level`].
///
/// Each variant carries its precomputed Blake3 hash as the last field.
#[derive(Debug, PartialEq, Eq)]
pub enum LevelData {
  /// Universe level 0 (Prop).
  Zero(Hash),
  /// Successor of a universe level.
  Succ(Level, Hash),
  /// Maximum of two universe levels.
  Max(Level, Level, Hash),
  /// Impredicative maximum of two universe levels.
  Imax(Level, Level, Hash),
  /// A named universe parameter.
  Param(Name, Hash),
  /// A universe-level metavariable.
  Mvar(Name, Hash),
}

impl Level {
  /// Returns a reference to the inner [`LevelData`].
  pub fn as_data(&self) -> &LevelData {
    &self.0
  }

  /// Returns the precomputed Blake3 hash of this level.
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
  /// Constructs universe level 0.
  pub fn zero() -> Self {
    Level(Arc::new(LevelData::Zero(blake3::hash(&[UZERO]))))
  }
  /// Constructs the successor of universe level `x`.
  pub fn succ(x: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[USUCC]);
    hasher.update(x.get_hash().as_bytes());
    Level(Arc::new(LevelData::Succ(x, hasher.finalize())))
  }
  /// Constructs `max x y`.
  pub fn max(x: Level, y: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UMAX]);
    hasher.update(x.get_hash().as_bytes());
    hasher.update(y.get_hash().as_bytes());
    Level(Arc::new(LevelData::Max(x, y, hasher.finalize())))
  }
  /// Constructs `imax x y` (impredicative max).
  pub fn imax(x: Level, y: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UIMAX]);
    hasher.update(x.get_hash().as_bytes());
    hasher.update(y.get_hash().as_bytes());
    Level(Arc::new(LevelData::Imax(x, y, hasher.finalize())))
  }
  /// Constructs a universe parameter with the given name.
  pub fn param(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[UPARAM]);
    hasher.update(x.get_hash().as_bytes());
    Level(Arc::new(LevelData::Param(x, hasher.finalize())))
  }
  /// Constructs a universe-level metavariable with the given name.
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

/// A literal value embedded in an expression.
#[derive(Debug, PartialEq, Eq)]
pub enum Literal {
  /// A natural number literal.
  NatVal(Nat),
  /// A string literal.
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

/// Binder annotation kind, mirroring Lean 4's `BinderInfo`.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum BinderInfo {
  /// Explicit binder `(x : A)`.
  Default,
  /// Implicit binder `{x : A}`.
  Implicit,
  /// Strict implicit binder `{{x : A}}`.
  StrictImplicit,
  /// Instance implicit binder `[x : A]`.
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

/// A substring reference: a string together with start and stop byte positions.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Substring {
  /// The underlying string.
  pub str: String,
  /// The start byte position (inclusive).
  pub start_pos: Nat,
  /// The stop byte position (exclusive).
  pub stop_pos: Nat,
}

fn hash_substring(ss: &Substring, hasher: &mut blake3::Hasher) {
  hasher.update(&[MSSTR]);
  hasher.update(ss.str.as_bytes());
  hasher.update(&ss.start_pos.to_le_bytes());
  hasher.update(&ss.stop_pos.to_le_bytes());
}

/// Source location metadata attached to syntax nodes.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SourceInfo {
  /// Original source with leading whitespace, leading position, trailing whitespace, trailing position.
  Original(Substring, Nat, Substring, Nat),
  /// Synthetic source span with start position, stop position, and canonical flag.
  Synthetic(Nat, Nat, bool),
  /// No source information available.
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

/// Pre-resolved reference attached to a syntax identifier.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SyntaxPreresolved {
  /// A pre-resolved namespace reference.
  Namespace(Name),
  /// A pre-resolved declaration reference with alias strings.
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

/// A Lean 4 concrete syntax tree node.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Syntax {
  /// Placeholder for missing syntax.
  Missing,
  /// An interior syntax node with a kind name and child nodes.
  Node(SourceInfo, Name, Vec<Syntax>),
  /// An atomic token (keyword, symbol, etc.).
  Atom(SourceInfo, String),
  /// An identifier with optional pre-resolved references.
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

/// A dynamically-typed value stored in expression metadata (`KVMap` entries).
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum DataValue {
  /// A string value.
  OfString(String),
  /// A boolean value.
  OfBool(bool),
  /// A name value.
  OfName(Name),
  /// A natural number value.
  OfNat(Nat),
  /// An integer value.
  OfInt(Int),
  /// A syntax tree value.
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

/// A content-addressed Lean 4 kernel expression.
///
/// Expressions are interned via `Arc` and compared/hashed by their Blake3 digest.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Expr(pub Arc<ExprData>);

/// The underlying data for an [`Expr`].
///
/// Each variant carries its precomputed Blake3 hash as the last field.
#[derive(Debug, PartialEq, Eq)]
pub enum ExprData {
  /// Bound variable (de Bruijn index).
  Bvar(Nat, Hash),
  /// Free variable.
  Fvar(Name, Hash),
  /// Metavariable.
  Mvar(Name, Hash),
  /// Sort (universe).
  Sort(Level, Hash),
  /// Reference to a named constant with universe level arguments.
  Const(Name, Vec<Level>, Hash),
  /// Function application.
  App(Expr, Expr, Hash),
  /// Lambda abstraction.
  Lam(Name, Expr, Expr, BinderInfo, Hash),
  /// Dependent function type (Pi / forall).
  ForallE(Name, Expr, Expr, BinderInfo, Hash),
  /// Let-binding (name, type, value, body, non-dep flag).
  LetE(Name, Expr, Expr, Expr, bool, Hash),
  /// Literal value (nat or string).
  Lit(Literal, Hash),
  /// Metadata-annotated expression with key-value pairs.
  Mdata(Vec<(Name, DataValue)>, Expr, Hash),
  /// Projection from a structure (type name, field index, struct expr).
  Proj(Name, Nat, Expr, Hash),
}

impl Expr {
  /// Returns a reference to the inner [`ExprData`].
  pub fn as_data(&self) -> &ExprData {
    &self.0
  }

  /// Returns the precomputed Blake3 hash of this expression.
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
  /// Constructs a bound variable expression from a de Bruijn index.
  pub fn bvar(x: Nat) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EVAR]);
    hasher.update(&x.to_le_bytes());
    Expr(Arc::new(ExprData::Bvar(x, hasher.finalize())))
  }

  /// Constructs a free variable expression.
  pub fn fvar(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EFVAR]);
    hasher.update(x.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Fvar(x, hasher.finalize())))
  }

  /// Constructs a metavariable expression.
  pub fn mvar(x: Name) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EMVAR]);
    hasher.update(x.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Mvar(x, hasher.finalize())))
  }

  /// Constructs a sort expression from a universe level.
  pub fn sort(x: Level) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[ESORT]);
    hasher.update(x.get_hash().as_bytes());
    Expr(Arc::new(ExprData::Sort(x, hasher.finalize())))
  }

  /// Constructs a constant reference with universe level arguments.
  pub fn cnst(x: Name, us: Vec<Level>) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EREF]);
    hasher.update(x.get_hash().as_bytes());
    for u in &us {
      hasher.update(u.get_hash().as_bytes());
    }
    Expr(Arc::new(ExprData::Const(x, us, hasher.finalize())))
  }

  /// Constructs a function application `f a`.
  pub fn app(f: Expr, a: Expr) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EAPP]);
    hasher.update(f.get_hash().as_bytes());
    hasher.update(a.get_hash().as_bytes());
    Expr(Arc::new(ExprData::App(f, a, hasher.finalize())))
  }

  /// Constructs a lambda abstraction `fun (n : t) => b`.
  pub fn lam(n: Name, t: Expr, b: Expr, bi: BinderInfo) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[ELAM]);
    hasher.update(n.get_hash().as_bytes());
    hasher.update(t.get_hash().as_bytes());
    hasher.update(b.get_hash().as_bytes());
    hasher.update(&[binder_info_tag(&bi)]);
    Expr(Arc::new(ExprData::Lam(n, t, b, bi, hasher.finalize())))
  }

  /// Constructs a dependent function type (forall / Pi).
  pub fn all(n: Name, t: Expr, b: Expr, bi: BinderInfo) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&[EALL]);
    hasher.update(n.get_hash().as_bytes());
    hasher.update(t.get_hash().as_bytes());
    hasher.update(b.get_hash().as_bytes());
    hasher.update(&[binder_info_tag(&bi)]);
    Expr(Arc::new(ExprData::ForallE(n, t, b, bi, hasher.finalize())))
  }

  /// Constructs a let-binding `let n : t := v in b`.
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

  /// Constructs a literal expression (nat or string).
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

  /// Constructs a metadata-annotated expression.
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

  /// Constructs a projection expression (type name, field index, struct expr).
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

/// Hints that control how aggressively the kernel unfolds a definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ReducibilityHints {
  /// Never unfold.
  #[default]
  Opaque,
  /// Always unfold (abbreviation).
  Abbrev,
  /// Unfold with the given priority height.
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

/// Safety classification of a definition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
  /// Marked `unsafe`; no termination or totality guarantees.
  Unsafe,
  /// Fully safe and total.
  Safe,
  /// Partial definition; may not terminate on all inputs.
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

/// Fields common to every constant declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantVal {
  /// The fully-qualified name of the constant.
  pub name: Name,
  /// Universe-polymorphic level parameter names.
  pub level_params: Vec<Name>,
  /// The type of the constant.
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

/// An axiom declaration (no definitional body).
#[derive(Debug, Clone)]
pub struct AxiomVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// Whether this axiom is marked `unsafe`.
  pub is_unsafe: bool,
}

/// A definition with a computable body.
#[derive(Debug, Clone)]
pub struct DefinitionVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// The definition body.
  pub value: Expr,
  /// Reducibility hints for the kernel.
  pub hints: ReducibilityHints,
  /// Safety classification.
  pub safety: DefinitionSafety,
  /// Names of all constants in the same mutual block.
  pub all: Vec<Name>,
}

/// A theorem declaration (proof-irrelevant; body is never reduced).
#[derive(Debug, Clone)]
pub struct TheoremVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// The proof term.
  pub value: Expr,
  /// Names of all constants in the same mutual block.
  pub all: Vec<Name>,
}

/// An opaque constant (body exists but is not unfolded by the kernel).
#[derive(Debug, Clone)]
pub struct OpaqueVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// The opaque body.
  pub value: Expr,
  /// Whether this opaque constant is marked `unsafe`.
  pub is_unsafe: bool,
  /// Names of all constants in the same mutual block.
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

/// A quotient-type related constant.
#[derive(Debug, Clone)]
pub struct QuotVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// Which quotient primitive this constant represents.
  pub kind: QuotKind,
}

/// An inductive type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// Number of parameters.
  pub num_params: Nat,
  /// Number of indices.
  pub num_indices: Nat,
  /// Names of all types in the same mutual inductive block.
  pub all: Vec<Name>,
  /// Names of the constructors for this type.
  pub ctors: Vec<Name>,
  /// Number of nested (non-mutual) inductives.
  pub num_nested: Nat,
  /// Whether this inductive type is recursive.
  pub is_rec: bool,
  /// Whether this inductive type is marked `unsafe`.
  pub is_unsafe: bool,
  /// Whether this inductive type is reflexive.
  pub is_reflexive: bool,
}

/// A constructor of an inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstructorVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// Name of the parent inductive type.
  pub induct: Name,
  /// Constructor index within the inductive type.
  pub cidx: Nat,
  /// Number of parameters inherited from the inductive type.
  pub num_params: Nat,
  /// Number of fields (non-parameter arguments).
  pub num_fields: Nat,
  /// Whether this constructor is marked `unsafe`.
  pub is_unsafe: bool,
}

/// A single reduction rule for a recursor, mapping a constructor to its branch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorRule {
  /// The constructor this rule applies to.
  pub ctor: Name,
  /// Number of fields the constructor has.
  pub n_fields: Nat,
  /// The right-hand side expression for this branch.
  pub rhs: Expr,
}

fn hash_recursor_rule(rule: &RecursorRule, hasher: &mut blake3::Hasher) {
  hasher.update(rule.ctor.get_hash().as_bytes());
  hasher.update(&rule.n_fields.to_le_bytes());
  hasher.update(rule.rhs.get_hash().as_bytes());
}

/// A recursor (eliminator) for an inductive type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursorVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// Names of all types in the same mutual inductive block.
  pub all: Vec<Name>,
  /// Number of parameters.
  pub num_params: Nat,
  /// Number of indices.
  pub num_indices: Nat,
  /// Number of motive arguments.
  pub num_motives: Nat,
  /// Number of minor premise arguments.
  pub num_minors: Nat,
  /// Reduction rules, one per constructor.
  pub rules: Vec<RecursorRule>,
  /// Whether this is a K-like recursor (proof-irrelevant elimination).
  pub k: bool,
  /// Whether this recursor is marked `unsafe`.
  pub is_unsafe: bool,
}

/// A top-level constant declaration in the Lean environment.
#[derive(Debug, Clone)]
pub enum ConstantInfo {
  /// An axiom.
  AxiomInfo(AxiomVal),
  /// A definition with a computable body.
  DefnInfo(DefinitionVal),
  /// A theorem (proof-irrelevant).
  ThmInfo(TheoremVal),
  /// An opaque constant.
  OpaqueInfo(OpaqueVal),
  /// A quotient primitive.
  QuotInfo(QuotVal),
  /// An inductive type.
  InductInfo(InductiveVal),
  /// A constructor of an inductive type.
  CtorInfo(ConstructorVal),
  /// A recursor (eliminator).
  RecInfo(RecursorVal),
}

impl ConstantInfo {
  /// Computes the Blake3 content hash of this constant declaration.
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

  /// Returns the name of this constant.
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

  /// Returns the type of this constant.
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

  /// Returns the universe level parameter names of this constant.
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

/// The Lean kernel environment: a map from names to their constant declarations.
pub type Env = FxHashMap<Name, ConstantInfo>;
