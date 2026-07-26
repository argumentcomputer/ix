//! Surface AST for the Ixon text format (`.ixon`).
//!
//! The AST is the hub shared by the parser and the pretty-printer. It
//! mirrors the *named* Ix level (`ix_common::env::Expr`) minus
//! `fvar`/`mvar`/`mdata`, plus source spans and the three reference
//! forms (`Name`, `#hash`, `Name#hash`). Nothing here knows about the
//! pack format: no tables, no de Bruijn indices, no blob addresses.
//!
//! Every node carries a byte-offset [`Span`]. Spans participate in
//! derived `PartialEq`; roundtrip tests therefore compare at the text
//! level (`print ∘ parse ∘ print = print`), not by AST equality.

use bignat::Nat;
use ix_common::env::{BinderInfo, NameComponent};

/// Byte-offset span into the source text: `start` inclusive, `end`
/// exclusive.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
  pub start: usize,
  pub end: usize,
}

impl Span {
  pub fn new(start: usize, end: usize) -> Self {
    Span { start, end }
  }

  /// Smallest span covering both `self` and `other`.
  pub fn to(&self, other: Span) -> Span {
    Span { start: self.start.min(other.start), end: self.end.max(other.end) }
  }
}

/// A surface (dotted) name: raw components, no hashing. Numeric
/// components are legal only in non-leading position (a leading digit
/// run lexes as a nat literal); names with a leading numeric component
/// are unspellable by name and use `#addr` instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SName {
  pub parts: Vec<NameComponent>,
  pub span: Span,
}

/// A `#hex` reference: 4–64 lowercase hex digits (exactly 64 in import
/// position). Stored as the raw hex string; address resolution belongs
/// to the resolve stage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashRef {
  pub hex: String,
  pub span: Span,
}

/// Universe-level expression.
#[derive(Debug, Clone, PartialEq)]
pub enum UnivExpr {
  /// Literal level: `0`, `1`, …
  Nat(u64, Span),
  /// Universe parameter by name (single component).
  Var(NameComponent, Span),
  /// `u + n`.
  Add(Box<UnivExpr>, u64, Span),
  /// `max u v`.
  Max(Box<UnivExpr>, Box<UnivExpr>, Span),
  /// `imax u v`.
  IMax(Box<UnivExpr>, Box<UnivExpr>, Span),
}

impl UnivExpr {
  pub fn span(&self) -> Span {
    match self {
      UnivExpr::Nat(_, s)
      | UnivExpr::Var(_, s)
      | UnivExpr::Add(_, _, s)
      | UnivExpr::Max(_, _, s)
      | UnivExpr::IMax(_, _, s) => *s,
    }
  }
}

/// A constant reference: `Name`, `#hash`, or the pinned `Name#hash`.
/// Invariant: at least one of `name`/`hash` is present. `levels: None`
/// is the bare form (zero-default, arity read from the resolved
/// constant); `Some(vs)` is the explicit `.{…}` form, `vs` nonempty.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstRef {
  pub name: Option<SName>,
  pub hash: Option<HashRef>,
  pub levels: Option<Vec<UnivExpr>>,
  pub span: Span,
}

/// `Prop` | `Type u?` | `Sort u` — the surface distinction is kept for
/// exact printing; the resolve stage normalizes.
#[derive(Debug, Clone, PartialEq)]
pub enum SortKind {
  Prop,
  Type(Option<UnivExpr>),
  Sort(UnivExpr),
}

/// A binder name: an identifier component or `_` (fresh anonymous).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinderName {
  Ident(NameComponent, Span),
  Anon(Span),
}

impl BinderName {
  pub fn span(&self) -> Span {
    match self {
      BinderName::Ident(_, s) | BinderName::Anon(s) => *s,
    }
  }
}

/// One bracketed binder group, e.g. `(x y : A)`, `{α : Type u}`,
/// `[inst : C]`, `⦃p : P⦄`. The bracket shape is recorded as
/// [`BinderInfo`] — metadata only, never address-relevant. For the
/// unnamed instance form `[C]`, `names` is empty.
#[derive(Debug, Clone, PartialEq)]
pub struct BinderGroup {
  pub info: BinderInfo,
  pub names: Vec<BinderName>,
  pub ty: Term,
  pub span: Span,
}

/// Surface term.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
  /// Reference (bound variable or constant — resolved later).
  Ref(ConstRef),
  /// `Prop` / `Type u` / `Sort u`.
  Sort(SortKind, Span),
  /// Application spine `f a b c` (`args` nonempty). The canonical
  /// printer flattens nested spines.
  App { head: Box<Term>, args: Vec<Term>, span: Span },
  /// `fun (x : A) (y : B) => e`.
  Fun { binders: Vec<BinderGroup>, body: Box<Term>, span: Span },
  /// Dependent function type `(x : A) (y : B) → C`.
  Pi { binders: Vec<BinderGroup>, body: Box<Term>, span: Span },
  /// Non-dependent function type `A → B`.
  Arrow { dom: Box<Term>, cod: Box<Term>, span: Span },
  /// `let x : T := v; b` (`non_dep = false`) or
  /// `have x : T := v; b` (`non_dep = true`) — address-relevant.
  Let {
    non_dep: bool,
    name: BinderName,
    ty: Box<Term>,
    val: Box<Term>,
    body: Box<Term>,
    span: Span,
  },
  /// Nat literal.
  NatLit(Nat, Span),
  /// String literal (decoded value; escapes re-applied on print).
  StrLit(String, Span),
  /// `proj S i e` structure projection.
  Proj { type_ref: ConstRef, idx: u64, val: Box<Term>, span: Span },
}

impl Term {
  pub fn span(&self) -> Span {
    match self {
      Term::Ref(r) => r.span,
      Term::Sort(_, s) | Term::NatLit(_, s) | Term::StrLit(_, s) => *s,
      Term::App { span, .. }
      | Term::Fun { span, .. }
      | Term::Pi { span, .. }
      | Term::Arrow { span, .. }
      | Term::Let { span, .. }
      | Term::Proj { span, .. } => *span,
    }
  }
}

/// Universe parameter binder in `.{u, v}` declaration position.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UParam {
  pub name: NameComponent,
  pub span: Span,
}

/// `def` / `theorem` / `opaque` — address-relevant (`Ixon.DefKind`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefKw {
  Def,
  Theorem,
  Opaque,
}

/// Declaration modifiers — address-relevant (`DefinitionSafety`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Modifiers {
  pub unsafe_: bool,
  pub partial_: bool,
}

/// `def`-like declaration: `def Name.{u} : T := v`.
#[derive(Debug, Clone, PartialEq)]
pub struct DefDecl {
  pub kw: DefKw,
  pub mods: Modifiers,
  pub name: Option<SName>,
  pub uparams: Vec<UParam>,
  pub ty: Term,
  pub value: Term,
  pub span: Span,
}

/// `axiom Name.{u} : T`.
#[derive(Debug, Clone, PartialEq)]
pub struct AxiomDecl {
  pub unsafe_: bool,
  pub name: Option<SName>,
  pub uparams: Vec<UParam>,
  pub ty: Term,
  pub span: Span,
}

/// The four quotient primitives.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKindKw {
  Type,
  Ctor,
  Lift,
  Ind,
}

/// `quot type|ctor|lift|ind Name.{u} : T`.
#[derive(Debug, Clone, PartialEq)]
pub struct QuotDecl {
  pub kind: QuotKindKw,
  pub name: Option<SName>,
  pub uparams: Vec<UParam>,
  pub ty: Term,
  pub span: Span,
}

/// Constructor inside an `inductive … where` block.
#[derive(Debug, Clone, PartialEq)]
pub struct CtorDecl {
  pub name: Option<SName>,
  pub params: u64,
  pub fields: u64,
  pub ty: Term,
  pub span: Span,
}

/// `inductive Name.{u} (params := n) (indices := m) : T where …`.
#[derive(Debug, Clone, PartialEq)]
pub struct IndDecl {
  pub unsafe_: bool,
  pub name: Option<SName>,
  pub uparams: Vec<UParam>,
  pub params: u64,
  pub indices: u64,
  pub ty: Term,
  pub ctors: Vec<CtorDecl>,
  pub span: Span,
}

/// Recursor rule: `| rule (fields := n) := rhs`.
#[derive(Debug, Clone, PartialEq)]
pub struct RuleDecl {
  pub fields: u64,
  pub rhs: Term,
  pub span: Span,
}

/// `recursor Name.{u} (params := …) … : T where …`.
#[derive(Debug, Clone, PartialEq)]
pub struct RecrDecl {
  pub unsafe_: bool,
  pub name: Option<SName>,
  pub uparams: Vec<UParam>,
  pub params: u64,
  pub indices: u64,
  pub motives: u64,
  pub minors: u64,
  pub k: bool,
  pub ty: Term,
  pub rules: Vec<RuleDecl>,
  pub span: Span,
}

/// The four projection-constant kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrjKind {
  DPrj,
  IPrj,
  CPrj,
  RPrj,
}

/// Projection constant: `cprj Name := #block i c` etc. — a `{idx,
/// block}` pointer into a muts block; the one decl form with no
/// expressions. `cidx` is present iff `kind == CPrj`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrjDecl {
  pub kind: PrjKind,
  pub name: Option<SName>,
  pub block: HashRef,
  pub idx: u64,
  pub cidx: Option<u64>,
  pub span: Span,
}

/// Top-level declaration.
#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
  Def(DefDecl),
  Axiom(AxiomDecl),
  Quot(QuotDecl),
  Ind(IndDecl),
  Recr(RecrDecl),
  /// `mutual … end`; members restricted to `Def`/`Ind`/`Recr`.
  Mutual(Vec<Decl>, Span),
  Prj(PrjDecl),
}

impl Decl {
  pub fn span(&self) -> Span {
    match self {
      Decl::Def(d) => d.span,
      Decl::Axiom(d) => d.span,
      Decl::Quot(d) => d.span,
      Decl::Ind(d) => d.span,
      Decl::Recr(d) => d.span,
      Decl::Mutual(_, s) => *s,
      Decl::Prj(d) => d.span,
    }
  }
}

/// `import Foo.Bar#hash` (mount under prefix) or `import #hash` (mount
/// at root). Import hashes are always full 64-hex.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
  pub prefix: Option<SName>,
  pub hash: HashRef,
  pub span: Span,
}

/// The file's main expression: a trailing `value : type` item. The
/// annotation is mandatory (it is the constant's `typ` — inference
/// would be elaboration, R4). Compiles like an anonymous
/// `def : T := v` (defn-kind, safe, monomorphic) and marks the result
/// as the file's `main` constant. At most one, and it must be the
/// last item (consecutive bare expressions absorb each other).
#[derive(Debug, Clone, PartialEq)]
pub struct MainExpr {
  pub value: Term,
  pub ty: Term,
  pub span: Span,
}

/// A parsed `.ixon` file: `ixon <version>` header, imports, decls,
/// optional trailing main expression.
#[derive(Debug, Clone, PartialEq)]
pub struct File {
  pub version: u64,
  pub imports: Vec<ImportDecl>,
  pub decls: Vec<Decl>,
  pub main: Option<MainExpr>,
  pub span: Span,
}

/// Node counting for the `max_nodes` limit (R2). Every counted node
/// consumes at least one source byte, so `max_bytes` already bounds
/// this; the explicit count is the number the resolve/compile stages
/// meter against.
pub fn count_term_nodes(t: &Term) -> usize {
  let mut n = 1;
  match t {
    Term::Ref(r) => n += count_ref_nodes(r) - 1,
    Term::Sort(k, _) => {
      if let SortKind::Type(Some(u)) | SortKind::Sort(u) = k {
        n += count_univ_nodes(u);
      }
    },
    Term::App { head, args, .. } => {
      n += count_term_nodes(head);
      for a in args {
        n += count_term_nodes(a);
      }
    },
    Term::Fun { binders, body, .. } | Term::Pi { binders, body, .. } => {
      for b in binders {
        n += 1 + count_term_nodes(&b.ty);
      }
      n += count_term_nodes(body);
    },
    Term::Arrow { dom, cod, .. } => {
      n += count_term_nodes(dom) + count_term_nodes(cod);
    },
    Term::Let { ty, val, body, .. } => {
      n +=
        count_term_nodes(ty) + count_term_nodes(val) + count_term_nodes(body);
    },
    Term::NatLit(..) | Term::StrLit(..) => {},
    Term::Proj { type_ref, val, .. } => {
      n += count_ref_nodes(type_ref) + count_term_nodes(val);
    },
  }
  n
}

fn count_ref_nodes(r: &ConstRef) -> usize {
  let mut n = 1;
  if let Some(ls) = &r.levels {
    for l in ls {
      n += count_univ_nodes(l);
    }
  }
  n
}

fn count_univ_nodes(u: &UnivExpr) -> usize {
  match u {
    UnivExpr::Nat(..) | UnivExpr::Var(..) => 1,
    UnivExpr::Add(a, _, _) => 1 + count_univ_nodes(a),
    UnivExpr::Max(a, b, _) | UnivExpr::IMax(a, b, _) => {
      1 + count_univ_nodes(a) + count_univ_nodes(b)
    },
  }
}

/// Total node count for a declaration.
pub fn count_decl_nodes(d: &Decl) -> usize {
  match d {
    Decl::Def(x) => 1 + count_term_nodes(&x.ty) + count_term_nodes(&x.value),
    Decl::Axiom(x) => 1 + count_term_nodes(&x.ty),
    Decl::Quot(x) => 1 + count_term_nodes(&x.ty),
    Decl::Ind(x) => {
      let mut n = 1 + count_term_nodes(&x.ty);
      for c in &x.ctors {
        n += 1 + count_term_nodes(&c.ty);
      }
      n
    },
    Decl::Recr(x) => {
      let mut n = 1 + count_term_nodes(&x.ty);
      for r in &x.rules {
        n += 1 + count_term_nodes(&r.rhs);
      }
      n
    },
    Decl::Mutual(ds, _) => 1 + ds.iter().map(count_decl_nodes).sum::<usize>(),
    Decl::Prj(_) => 1,
  }
}

/// Total node count for a file.
pub fn count_file_nodes(f: &File) -> usize {
  1 + f.imports.len()
    + f.decls.iter().map(count_decl_nodes).sum::<usize>()
    + f
      .main
      .as_ref()
      .map_or(0, |m| 1 + count_term_nodes(&m.value) + count_term_nodes(&m.ty))
}
