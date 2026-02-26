//! Lean kernel types without content addressing.
//!
//! This module defines the Lean 4 kernel type system without Blake3 hashing.
//! These are the core datatypes used for type checking and reduction.

use crate::lean::nat::Nat;

// ============================================================================
// Name
// ============================================================================

/// A hierarchical name without content addressing.
#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Name {
  /// The root (empty) name.
  Anonymous,
  /// A string component appended to a prefix name.
  Str(Box<Name>, String),
  /// A numeric component appended to a prefix name.
  Num(Box<Name>, Nat),
}

// ============================================================================
// Level
// ============================================================================

/// A universe level without content addressing.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Level {
  /// Universe level 0 (Prop).
  Zero,
  /// Successor of a universe level.
  Succ(Box<Level>),
  /// Maximum of two universe levels.
  Max(Box<Level>, Box<Level>),
  /// Impredicative maximum of two universe levels.
  Imax(Box<Level>, Box<Level>),
  /// A named universe parameter.
  Param(Name),
  /// A universe-level metavariable.
  Mvar(Name),
}

// ============================================================================
// Literal
// ============================================================================

/// A literal value embedded in an expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Literal {
  /// A natural number literal.
  NatVal(Nat),
  /// A string literal.
  StrVal(String),
}

// ============================================================================
// BinderInfo
// ============================================================================

/// Binder annotation kind, mirroring Lean 4's `BinderInfo`.
#[derive(Debug, PartialEq, Eq, Clone)]
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

// ============================================================================
// Metadata Types
// ============================================================================

/// An integer value.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Int {
  OfNat(Nat),
  NegSucc(Nat),
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

/// Pre-resolved reference attached to a syntax identifier.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SyntaxPreresolved {
  /// A pre-resolved namespace reference.
  Namespace(Name),
  /// A pre-resolved declaration reference with alias strings.
  Decl(Name, Vec<String>),
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

// ============================================================================
// Expr
// ============================================================================

/// A Lean 4 kernel expression without content addressing.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
  /// Bound variable (de Bruijn index).
  Bvar(Nat),
  /// Free variable.
  Fvar(Name),
  /// Metavariable.
  Mvar(Name),
  /// Sort (universe).
  Sort(Level),
  /// Reference to a named constant with universe level arguments.
  Const(Name, Vec<Level>),
  /// Function application.
  App(Box<Expr>, Box<Expr>),
  /// Lambda abstraction.
  Lam(Name, Box<Expr>, Box<Expr>, BinderInfo),
  /// Dependent function type (Pi / forall).
  ForallE(Name, Box<Expr>, Box<Expr>, BinderInfo),
  /// Let-binding (name, type, value, body, non-dep flag).
  LetE(Name, Box<Expr>, Box<Expr>, Box<Expr>, bool),
  /// Literal value (nat or string).
  Lit(Literal),
  /// Metadata-annotated expression with key-value pairs.
  Mdata(Vec<(Name, DataValue)>, Box<Expr>),
  /// Projection from a structure (type name, field index, struct expr).
  Proj(Name, Nat, Box<Expr>),
}

// ============================================================================
// Constants
// ============================================================================

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

/// An axiom declaration (no definitional body).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AxiomVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// Whether this axiom is marked `unsafe`.
  pub is_unsafe: bool,
}

/// A definition with a computable body.
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoremVal {
  /// Common constant fields.
  pub cnst: ConstantVal,
  /// The proof term.
  pub value: Expr,
  /// Names of all constants in the same mutual block.
  pub all: Vec<Name>,
}

/// An opaque constant (body exists but is not unfolded by the kernel).
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// Quotient type kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
  Type,
  Ctor,
  Lift,
  Ind,
}

/// A quotient-type related constant.
#[derive(Debug, Clone, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
