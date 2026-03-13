//! Kernel-specific types for Kernel2.
//!
//! These types mirror `Ix.Kernel.Types` from Lean: they use `Address` for
//! constant references and positional indices for level parameters, unlike
//! the `env` module's `Name`-based types.
//!
//! Types are parameterized by `MetaMode`: in `Meta` mode, metadata fields
//! (names, binder info) are preserved; in `Anon` mode, they become `()`
//! for cache-friendly sharing.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use crate::ix::address::Address;
pub use crate::ix::env::{
  BinderInfo, DefinitionSafety, Literal, Name, QuotKind,
  ReducibilityHints,
};
use super::helpers::lift_bvars;

// ============================================================================
// MetaMode — parameterize metadata (names, binder info) for anon caching
// ============================================================================

/// Trait for parameterizing metadata fields in kernel types.
///
/// In `Meta` mode, metadata fields (names, binder info) retain their values.
/// In `Anon` mode, they become `()`, enabling better expression caching
/// since expressions differing only in metadata share cache entries.
pub trait MetaMode: 'static + Clone + Default + fmt::Debug {
  type Field<T: Default + PartialEq + Clone + fmt::Debug + Hash>:
    Default + PartialEq + Clone + fmt::Debug + Hash;
  fn mk_field<T: Default + PartialEq + Clone + fmt::Debug + Hash>(
    val: T,
  ) -> Self::Field<T>;
}

/// Full metadata mode: names and binder info are preserved.
#[derive(Clone, Default, Debug)]
pub struct Meta;

/// Anonymous mode: metadata becomes `()` for cache-friendly sharing.
#[derive(Clone, Default, Debug)]
pub struct Anon;

impl MetaMode for Meta {
  type Field<T: Default + PartialEq + Clone + fmt::Debug + Hash> = T;
  fn mk_field<T: Default + PartialEq + Clone + fmt::Debug + Hash>(
    val: T,
  ) -> T {
    val
  }
}

impl MetaMode for Anon {
  type Field<T: Default + PartialEq + Clone + fmt::Debug + Hash> = ();
  fn mk_field<T: Default + PartialEq + Clone + fmt::Debug + Hash>(
    _: T,
  ) -> () {
  }
}

// ============================================================================
// MetaId — constant identifier (address + metadata name)
// ============================================================================

/// Constant identifier: bundles a content address with a metadata name.
/// In Meta mode, both fields participate in equality/hashing.
/// In Anon mode, name is () so only address matters.
#[derive(Clone, Debug)]
pub struct MetaId<M: MetaMode> {
  pub addr: Address,
  pub name: M::Field<Name>,
}

impl<M: MetaMode> MetaId<M> {
  pub fn new(addr: Address, name: M::Field<Name>) -> Self {
    MetaId { addr, name }
  }

  pub fn from_addr(addr: Address) -> Self {
    MetaId {
      addr,
      name: M::Field::<Name>::default(),
    }
  }
}

impl<M: MetaMode> PartialEq for MetaId<M> {
  fn eq(&self, other: &Self) -> bool {
    self.addr == other.addr && self.name == other.name
  }
}

impl<M: MetaMode> Eq for MetaId<M> {}

impl<M: MetaMode> Hash for MetaId<M> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.addr.hash(state);
    self.name.hash(state);
  }
}

impl<M: MetaMode> fmt::Display for MetaId<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let s = format!("{:?}", self.name);
    let hex = self.addr.hex();
    let short = &hex[..8.min(hex.len())];
    if let Some(inner) =
      s.strip_prefix("Name(").and_then(|s| s.strip_suffix(')'))
    {
      if inner != "anonymous" {
        return write!(f, "{}@{}", inner, short);
      }
    }
    write!(f, "{}", short)
  }
}

// ============================================================================
// KLevel — kernel universe level with positional params
// ============================================================================

/// A kernel universe level with positional parameters.
#[derive(Clone, Debug)]
pub struct KLevel<M: MetaMode>(pub Rc<KLevelData<M>>);

/// The underlying data for a kernel level.
#[derive(Debug)]
pub enum KLevelData<M: MetaMode> {
  Zero,
  Succ(KLevel<M>),
  Max(KLevel<M>, KLevel<M>),
  IMax(KLevel<M>, KLevel<M>),
  /// Positional parameter: `idx` is the position in the constant's
  /// universe parameter list, `name` is kept for debugging.
  Param(usize, M::Field<Name>),
}

impl<M: MetaMode> KLevel<M> {
  pub fn zero() -> Self {
    KLevel(Rc::new(KLevelData::Zero))
  }

  pub fn succ(l: KLevel<M>) -> Self {
    KLevel(Rc::new(KLevelData::Succ(l)))
  }

  pub fn max(l: KLevel<M>, r: KLevel<M>) -> Self {
    KLevel(Rc::new(KLevelData::Max(l, r)))
  }

  pub fn imax(l: KLevel<M>, r: KLevel<M>) -> Self {
    KLevel(Rc::new(KLevelData::IMax(l, r)))
  }

  pub fn param(idx: usize, name: M::Field<Name>) -> Self {
    KLevel(Rc::new(KLevelData::Param(idx, name)))
  }

  pub fn data(&self) -> &KLevelData<M> {
    &self.0
  }

  /// Returns the pointer identity for caching.
  pub fn ptr_id(&self) -> usize {
    Rc::as_ptr(&self.0) as usize
  }
}

impl<M: MetaMode> PartialEq for KLevel<M> {
  fn eq(&self, other: &Self) -> bool {
    match (self.data(), other.data()) {
      (KLevelData::Zero, KLevelData::Zero) => true,
      (KLevelData::Succ(a), KLevelData::Succ(b)) => a == b,
      (KLevelData::Max(a1, a2), KLevelData::Max(b1, b2))
      | (KLevelData::IMax(a1, a2), KLevelData::IMax(b1, b2)) => {
        a1 == b1 && a2 == b2
      }
      (KLevelData::Param(a, _), KLevelData::Param(b, _)) => a == b,
      _ => false,
    }
  }
}

impl<M: MetaMode> Eq for KLevel<M> {}

impl<M: MetaMode> Hash for KLevel<M> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    std::mem::discriminant(self.data()).hash(state);
    match self.data() {
      KLevelData::Zero => {}
      KLevelData::Succ(l) => l.hash(state),
      KLevelData::Max(a, b) | KLevelData::IMax(a, b) => {
        a.hash(state);
        b.hash(state);
      }
      KLevelData::Param(idx, _) => idx.hash(state),
    }
  }
}

impl<M: MetaMode> fmt::Display for KLevel<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.data() {
      KLevelData::Zero => write!(f, "0"),
      KLevelData::Succ(l) => {
        // Count successive succs for readability
        let mut count = 1u64;
        let mut cur = l;
        while let KLevelData::Succ(inner) = cur.data() {
          count += 1;
          cur = inner;
        }
        if matches!(cur.data(), KLevelData::Zero) {
          write!(f, "{count}")
        } else {
          write!(f, "{cur}+{count}")
        }
      }
      KLevelData::Max(a, b) => write!(f, "max({a}, {b})"),
      KLevelData::IMax(a, b) => write!(f, "imax({a}, {b})"),
      KLevelData::Param(idx, name) => {
        let s = format!("{:?}", name);
        if let Some(inner) = s.strip_prefix("Name(").and_then(|s| s.strip_suffix(')')) {
          if inner != "anonymous" {
            return write!(f, "{inner}");
          }
        }
        write!(f, "u{idx}")
      }
    }
  }
}

// ============================================================================
// KExpr — kernel expression with Address-based const refs
// ============================================================================

/// A kernel expression using content-addressed (`Address`) constant references.
#[derive(Clone, Debug)]
pub struct KExpr<M: MetaMode>(pub Rc<KExprData<M>>);

/// The underlying data for a kernel expression.
#[derive(Debug)]
pub enum KExprData<M: MetaMode> {
  /// Bound variable (de Bruijn index).
  BVar(usize, M::Field<Name>),
  /// Sort (universe level).
  Sort(KLevel<M>),
  /// Constant reference by MetaId, with universe level arguments.
  Const(MetaId<M>, Vec<KLevel<M>>),
  /// Function application.
  App(KExpr<M>, KExpr<M>),
  /// Lambda abstraction: domain type, body, binder name, binder info.
  Lam(KExpr<M>, KExpr<M>, M::Field<Name>, M::Field<BinderInfo>),
  /// Dependent function type (Pi/forall): domain type, body, binder name,
  /// binder info.
  ForallE(KExpr<M>, KExpr<M>, M::Field<Name>, M::Field<BinderInfo>),
  /// Let binding: type, value, body, binder name.
  LetE(KExpr<M>, KExpr<M>, KExpr<M>, M::Field<Name>),
  /// Literal value (nat or string).
  Lit(Literal),
  /// Projection: type MetaId, field index, struct expr.
  Proj(MetaId<M>, usize, KExpr<M>),
}

impl<M: MetaMode> KExpr<M> {
  pub fn data(&self) -> &KExprData<M> {
    &self.0
  }

  /// Returns the pointer identity for caching.
  pub fn ptr_id(&self) -> usize {
    Rc::as_ptr(&self.0) as usize
  }

  // Smart constructors

  pub fn bvar(idx: usize, name: M::Field<Name>) -> Self {
    KExpr(Rc::new(KExprData::BVar(idx, name)))
  }

  pub fn sort(level: KLevel<M>) -> Self {
    KExpr(Rc::new(KExprData::Sort(level)))
  }

  pub fn cnst(
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
  ) -> Self {
    KExpr(Rc::new(KExprData::Const(id, levels)))
  }

  pub fn app(f: KExpr<M>, a: KExpr<M>) -> Self {
    KExpr(Rc::new(KExprData::App(f, a)))
  }

  pub fn lam(
    ty: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
  ) -> Self {
    KExpr(Rc::new(KExprData::Lam(ty, body, name, bi)))
  }

  pub fn forall_e(
    ty: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
  ) -> Self {
    KExpr(Rc::new(KExprData::ForallE(ty, body, name, bi)))
  }

  pub fn let_e(
    ty: KExpr<M>,
    val: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
  ) -> Self {
    KExpr(Rc::new(KExprData::LetE(ty, val, body, name)))
  }

  pub fn lit(l: Literal) -> Self {
    KExpr(Rc::new(KExprData::Lit(l)))
  }

  pub fn proj(
    type_id: MetaId<M>,
    idx: usize,
    strct: KExpr<M>,
  ) -> Self {
    KExpr(Rc::new(KExprData::Proj(type_id, idx, strct)))
  }

  /// Collect the function and all arguments from a nested App spine.
  /// Returns (function, [arg0, arg1, ...]) where the original expr is
  /// `((function arg0) arg1) ...`.
  pub fn get_app_args(&self) -> (&KExpr<M>, Vec<&KExpr<M>>) {
    let mut args = Vec::new();
    let mut cur = self;
    while let KExprData::App(f, a) = cur.data() {
      args.push(a);
      cur = f;
    }
    args.reverse();
    (cur, args)
  }

  /// Get the head function of a nested App spine (owned clone).
  pub fn get_app_fn(&self) -> KExpr<M> {
    let mut cur = self;
    while let KExprData::App(f, _) = cur.data() {
      cur = f;
    }
    cur.clone()
  }

  /// Get all arguments from a nested App spine (owned clones).
  pub fn get_app_args_owned(&self) -> Vec<KExpr<M>> {
    let mut args = Vec::new();
    let mut cur = self;
    while let KExprData::App(f, a) = cur.data() {
      args.push(a.clone());
      cur = f;
    }
    args.reverse();
    args
  }

  /// Get the const MetaId if this is a Const expression.
  pub fn const_id(&self) -> Option<&MetaId<M>> {
    match self.data() {
      KExprData::Const(id, _) => Some(id),
      _ => None,
    }
  }

  /// Get the const address if this is a Const expression.
  pub fn const_addr(&self) -> Option<&Address> {
    match self.data() {
      KExprData::Const(id, _) => Some(&id.addr),
      _ => None,
    }
  }

  /// Get the const levels if this is a Const expression.
  pub fn const_levels(&self) -> Option<&Vec<KLevel<M>>> {
    match self.data() {
      KExprData::Const(_, levels) => Some(levels),
      _ => None,
    }
  }

  /// Check if this is a Const with the given address.
  pub fn is_const_of(&self, addr: &Address) -> bool {
    matches!(self.data(), KExprData::Const(id, _) if id.addr == *addr)
  }

  /// Create Prop (Sort 0).
  pub fn prop() -> Self {
    KExpr::sort(KLevel::zero())
  }

  /// Create a non-dependent arrow type: `a → b`.
  /// Implemented as `∀ (_ : a), lift(b)` where b's free bvars are lifted.
  pub fn mk_arrow(a: KExpr<M>, b: KExpr<M>) -> Self {
    KExpr::forall_e(
      a,
      lift_bvars(&b, 1, 0),
      M::Field::<Name>::default(),
      M::Field::<BinderInfo>::default(),
    )
  }
}

impl<M: MetaMode> PartialEq for KExpr<M> {
  fn eq(&self, other: &Self) -> bool {
    // Fast pointer check
    if Rc::ptr_eq(&self.0, &other.0) {
      return true;
    }
    match (self.data(), other.data()) {
      (KExprData::BVar(a, _), KExprData::BVar(b, _)) => a == b,
      (KExprData::Sort(a), KExprData::Sort(b)) => a == b,
      (KExprData::Const(id1, l1), KExprData::Const(id2, l2)) => {
        id1.addr == id2.addr && l1 == l2
      }
      (KExprData::App(f1, a1), KExprData::App(f2, a2)) => {
        f1 == f2 && a1 == a2
      }
      (
        KExprData::Lam(t1, b1, _, _),
        KExprData::Lam(t2, b2, _, _),
      )
      | (
        KExprData::ForallE(t1, b1, _, _),
        KExprData::ForallE(t2, b2, _, _),
      ) => t1 == t2 && b1 == b2,
      (
        KExprData::LetE(t1, v1, b1, _),
        KExprData::LetE(t2, v2, b2, _),
      ) => t1 == t2 && v1 == v2 && b1 == b2,
      (KExprData::Lit(a), KExprData::Lit(b)) => a == b,
      (
        KExprData::Proj(id1, i1, s1),
        KExprData::Proj(id2, i2, s2),
      ) => id1.addr == id2.addr && i1 == i2 && s1 == s2,
      _ => false,
    }
  }
}

impl<M: MetaMode> Eq for KExpr<M> {}

impl<M: MetaMode> Hash for KExpr<M> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    std::mem::discriminant(self.data()).hash(state);
    match self.data() {
      KExprData::BVar(idx, _) => idx.hash(state),
      KExprData::Sort(l) => l.hash(state),
      KExprData::Const(id, levels) => {
        id.addr.hash(state);
        levels.hash(state);
      }
      KExprData::App(f, a) => {
        f.hash(state);
        a.hash(state);
      }
      KExprData::Lam(t, b, _, _) | KExprData::ForallE(t, b, _, _) => {
        t.hash(state);
        b.hash(state);
      }
      KExprData::LetE(t, v, b, _) => {
        t.hash(state);
        v.hash(state);
        b.hash(state);
      }
      KExprData::Lit(l) => {
        match l {
          Literal::NatVal(n) => {
            0u8.hash(state);
            n.hash(state);
          }
          Literal::StrVal(s) => {
            1u8.hash(state);
            s.hash(state);
          }
        }
      }
      KExprData::Proj(id, idx, s) => {
        id.addr.hash(state);
        idx.hash(state);
        s.hash(state);
      }
    }
  }
}

/// Helper: collect an App spine into (head, [args]).
fn collect_app_spine<M: MetaMode>(e: &KExpr<M>) -> (&KExpr<M>, Vec<&KExpr<M>>) {
  let mut args = Vec::new();
  let mut cur = e;
  while let KExprData::App(fun, arg) = cur.data() {
    args.push(arg);
    cur = fun;
  }
  args.reverse();
  (cur, args)
}

/// Format a MetaMode field name: shows the pretty name for Meta, `_` for Anon.
pub fn fmt_field_name<M: MetaMode>(name: &M::Field<Name>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
  let s = format!("{:?}", name);
  // Meta mode Debug: "Name(Foo.Bar)" → extract inner; Anon mode: "()" → "_"
  if let Some(inner) = s.strip_prefix("Name(").and_then(|s| s.strip_suffix(')')) {
    if inner == "anonymous" {
      write!(f, "_")
    } else {
      write!(f, "{inner}")
    }
  } else if s == "()" {
    write!(f, "_")
  } else {
    write!(f, "{s}")
  }
}

impl<M: MetaMode> fmt::Display for KExpr<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.data() {
      KExprData::BVar(idx, name) => {
        let s = format!("{:?}", name);
        if let Some(inner) = s.strip_prefix("Name(").and_then(|s| s.strip_suffix(')')) {
          if inner != "anonymous" {
            return write!(f, "{inner}");
          }
        }
        write!(f, "#{idx}")
      }
      KExprData::Sort(l) => write!(f, "Sort {l}"),
      KExprData::Const(id, levels) => {
        fmt_field_name::<M>(&id.name, f)?;
        if levels.is_empty() {
          Ok(())
        } else {
          write!(f, ".{{{}}}", levels.iter().map(|l| format!("{l}")).collect::<Vec<_>>().join(", "))
        }
      }
      KExprData::App(_, _) => {
        let (head, args) = collect_app_spine::<M>(self);
        write!(f, "({head}")?;
        for arg in args {
          write!(f, " {arg}")?;
        }
        write!(f, ")")
      }
      KExprData::Lam(ty, body, name, _) => {
        write!(f, "(fun (")?;
        fmt_field_name::<M>(name, f)?;
        write!(f, " : {ty}) => {body})")
      }
      KExprData::ForallE(ty, body, name, _) => {
        write!(f, "((")?;
        fmt_field_name::<M>(name, f)?;
        write!(f, " : {ty}) -> {body})")
      }
      KExprData::LetE(ty, val, body, name) => {
        write!(f, "(let ")?;
        fmt_field_name::<M>(name, f)?;
        write!(f, " : {ty} := {val} in {body})")
      }
      KExprData::Lit(Literal::NatVal(n)) => write!(f, "{n}"),
      KExprData::Lit(Literal::StrVal(s)) => write!(f, "\"{s}\""),
      KExprData::Proj(id, idx, s) => {
        write!(f, "{s}.")?;
        fmt_field_name::<M>(&id.name, f)?;
        write!(f, "[{idx}]")
      }
    }
  }
}

// ============================================================================
// ConstantInfo — kernel constant declarations
// ============================================================================

/// Common fields for all kernel constant declarations.
#[derive(Debug, Clone)]
pub struct KConstantVal<M: MetaMode> {
  /// Number of universe level parameters.
  pub num_levels: usize,
  /// The type of the constant.
  pub typ: KExpr<M>,
  /// Name (for debugging/display).
  pub name: M::Field<Name>,
  /// Universe level parameter names (for debugging).
  pub level_params: M::Field<Vec<Name>>,
}

/// An axiom declaration.
#[derive(Debug, Clone)]
pub struct KAxiomVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub is_unsafe: bool,
}

/// A definition with a computable body.
#[derive(Debug, Clone)]
pub struct KDefinitionVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub value: KExpr<M>,
  pub hints: ReducibilityHints,
  pub safety: DefinitionSafety,
  /// All constants in the same mutual block.
  pub all: Vec<MetaId<M>>,
}

/// A theorem declaration.
#[derive(Debug, Clone)]
pub struct KTheoremVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub value: KExpr<M>,
  /// All constants in the same mutual block.
  pub all: Vec<MetaId<M>>,
}

/// An opaque constant.
#[derive(Debug, Clone)]
pub struct KOpaqueVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub value: KExpr<M>,
  pub is_unsafe: bool,
  /// All constants in the same mutual block.
  pub all: Vec<MetaId<M>>,
}

/// A quotient primitive.
#[derive(Debug, Clone)]
pub struct KQuotVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub kind: QuotKind,
}

/// An inductive type declaration.
#[derive(Debug, Clone)]
pub struct KInductiveVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub num_params: usize,
  pub num_indices: usize,
  /// All types in the same mutual inductive block.
  pub all: Vec<MetaId<M>>,
  /// Constructors for this type.
  pub ctors: Vec<MetaId<M>>,
  pub num_nested: usize,
  pub is_rec: bool,
  pub is_unsafe: bool,
  pub is_reflexive: bool,
}

/// A constructor of an inductive type.
#[derive(Debug, Clone)]
pub struct KConstructorVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  /// Parent inductive type.
  pub induct: MetaId<M>,
  /// Constructor index within the inductive type.
  pub cidx: usize,
  pub num_params: usize,
  pub num_fields: usize,
  pub is_unsafe: bool,
}

/// A single reduction rule for a recursor.
#[derive(Debug, Clone)]
pub struct KRecursorRule<M: MetaMode> {
  /// The constructor this rule applies to.
  pub ctor: MetaId<M>,
  /// Number of fields the constructor has.
  pub nfields: usize,
  /// The right-hand side expression for this branch.
  pub rhs: KExpr<M>,
}

/// A recursor (eliminator) for an inductive type.
#[derive(Debug, Clone)]
pub struct KRecursorVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  /// All types in the same mutual inductive block.
  pub all: Vec<MetaId<M>>,
  pub num_params: usize,
  pub num_indices: usize,
  pub num_motives: usize,
  pub num_minors: usize,
  pub rules: Vec<KRecursorRule<M>>,
  pub k: bool,
  pub is_unsafe: bool,
}

/// A top-level constant declaration in the kernel environment.
#[derive(Debug, Clone)]
pub enum KConstantInfo<M: MetaMode> {
  Axiom(KAxiomVal<M>),
  Definition(KDefinitionVal<M>),
  Theorem(KTheoremVal<M>),
  Opaque(KOpaqueVal<M>),
  Quotient(KQuotVal<M>),
  Inductive(KInductiveVal<M>),
  Constructor(KConstructorVal<M>),
  Recursor(KRecursorVal<M>),
}

impl<M: MetaMode> KConstantInfo<M> {
  /// Returns the common constant fields.
  pub fn cv(&self) -> &KConstantVal<M> {
    match self {
      KConstantInfo::Axiom(v) => &v.cv,
      KConstantInfo::Definition(v) => &v.cv,
      KConstantInfo::Theorem(v) => &v.cv,
      KConstantInfo::Opaque(v) => &v.cv,
      KConstantInfo::Quotient(v) => &v.cv,
      KConstantInfo::Inductive(v) => &v.cv,
      KConstantInfo::Constructor(v) => &v.cv,
      KConstantInfo::Recursor(v) => &v.cv,
    }
  }

  /// Returns the type of the constant.
  pub fn typ(&self) -> &KExpr<M> {
    &self.cv().typ
  }

  /// Returns the name of the constant (for debugging).
  pub fn name(&self) -> &M::Field<Name> {
    &self.cv().name
  }

  /// Returns a human-readable kind name.
  pub fn kind_name(&self) -> &'static str {
    match self {
      KConstantInfo::Axiom(_) => "axiom",
      KConstantInfo::Definition(_) => "definition",
      KConstantInfo::Theorem(_) => "theorem",
      KConstantInfo::Opaque(_) => "opaque",
      KConstantInfo::Quotient(_) => "quotient",
      KConstantInfo::Inductive(_) => "inductive",
      KConstantInfo::Constructor(_) => "constructor",
      KConstantInfo::Recursor(_) => "recursor",
    }
  }

  /// Returns the safety level of this constant.
  pub fn safety(&self) -> DefinitionSafety {
    match self {
      KConstantInfo::Axiom(v) => {
        if v.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        }
      }
      KConstantInfo::Definition(v) => v.safety,
      KConstantInfo::Theorem(_) => DefinitionSafety::Safe,
      KConstantInfo::Opaque(v) => {
        if v.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        }
      }
      KConstantInfo::Quotient(_) => DefinitionSafety::Safe,
      KConstantInfo::Inductive(v) => {
        if v.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        }
      }
      KConstantInfo::Constructor(v) => {
        if v.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        }
      }
      KConstantInfo::Recursor(v) => {
        if v.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        }
      }
    }
  }
}

// ============================================================================
// KEnv — kernel environment
// ============================================================================

// ============================================================================
// KEnv — kernel environment
// ============================================================================

/// The kernel environment: a map from MetaId to constant info,
/// with an address index for content-only lookups.
pub struct KEnv<M: MetaMode> {
  pub consts: FxHashMap<MetaId<M>, KConstantInfo<M>>,
  /// Address → MetaId index for content-only lookups.
  pub addr_index: FxHashMap<Address, MetaId<M>>,
}

impl<M: MetaMode> Clone for KEnv<M> {
  fn clone(&self) -> Self {
    KEnv {
      consts: self.consts.clone(),
      addr_index: self.addr_index.clone(),
    }
  }
}

impl<M: MetaMode> fmt::Debug for KEnv<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "KEnv({} consts)", self.consts.len())
  }
}

impl<M: MetaMode> Default for KEnv<M> {
  fn default() -> Self {
    KEnv {
      consts: FxHashMap::default(),
      addr_index: FxHashMap::default(),
    }
  }
}

impl<M: MetaMode> KEnv<M> {
  /// Look up a constant by MetaId.
  pub fn find(&self, id: &MetaId<M>) -> Option<&KConstantInfo<M>> {
    self.consts.get(id)
  }

  /// Look up a constant by address (content-only, may return any name).
  pub fn find_by_addr(&self, addr: &Address) -> Option<&KConstantInfo<M>> {
    self.addr_index.get(addr).and_then(|id| self.consts.get(id))
  }

  /// Get a MetaId for an address (content-only lookup).
  pub fn get_id_by_addr(&self, addr: &Address) -> Option<&MetaId<M>> {
    self.addr_index.get(addr)
  }

  /// Get a constant by MetaId, or return None.
  pub fn get(&self, id: &MetaId<M>) -> Option<&KConstantInfo<M>> {
    self.consts.get(id)
  }

  /// Insert a constant.
  pub fn insert(&mut self, id: MetaId<M>, ci: KConstantInfo<M>) {
    self.addr_index.insert(id.addr.clone(), id.clone());
    self.consts.insert(id, ci);
  }

  /// Number of constants.
  pub fn len(&self) -> usize {
    self.consts.len()
  }

  /// Check if the env is empty.
  pub fn is_empty(&self) -> bool {
    self.consts.is_empty()
  }

  /// Iterate over (MetaId, ConstantInfo) pairs.
  pub fn iter(
    &self,
  ) -> impl Iterator<Item = (&MetaId<M>, &KConstantInfo<M>)> {
    self.consts.iter()
  }

  /// Check if a MetaId is present.
  pub fn contains_key(&self, id: &MetaId<M>) -> bool {
    self.consts.contains_key(id)
  }

  /// Check if an address is present.
  pub fn contains_addr(&self, addr: &Address) -> bool {
    self.addr_index.contains_key(addr)
  }
}

// ============================================================================
// Primitives — addresses of known primitive types and operations
// ============================================================================

/// Primitive types and operations needed by the kernel.
#[derive(Debug, Clone)]
pub struct Primitives<M: MetaMode> {
  // Core types
  pub nat: Option<MetaId<M>>,
  pub nat_zero: Option<MetaId<M>>,
  pub nat_succ: Option<MetaId<M>>,

  // Nat arithmetic
  pub nat_add: Option<MetaId<M>>,
  pub nat_pred: Option<MetaId<M>>,
  pub nat_sub: Option<MetaId<M>>,
  pub nat_mul: Option<MetaId<M>>,
  pub nat_pow: Option<MetaId<M>>,
  pub nat_gcd: Option<MetaId<M>>,
  pub nat_mod: Option<MetaId<M>>,
  pub nat_div: Option<MetaId<M>>,
  pub nat_bitwise: Option<MetaId<M>>,

  // Nat comparisons
  pub nat_beq: Option<MetaId<M>>,
  pub nat_ble: Option<MetaId<M>>,

  // Nat bitwise
  pub nat_land: Option<MetaId<M>>,
  pub nat_lor: Option<MetaId<M>>,
  pub nat_xor: Option<MetaId<M>>,
  pub nat_shift_left: Option<MetaId<M>>,
  pub nat_shift_right: Option<MetaId<M>>,

  // Bool
  pub bool_type: Option<MetaId<M>>,
  pub bool_true: Option<MetaId<M>>,
  pub bool_false: Option<MetaId<M>>,

  // String/Char
  pub string: Option<MetaId<M>>,
  pub string_mk: Option<MetaId<M>>,
  pub char_type: Option<MetaId<M>>,
  pub char_mk: Option<MetaId<M>>,
  pub string_of_list: Option<MetaId<M>>,

  // List
  pub list: Option<MetaId<M>>,
  pub list_nil: Option<MetaId<M>>,
  pub list_cons: Option<MetaId<M>>,

  // Equality
  pub eq: Option<MetaId<M>>,
  pub eq_refl: Option<MetaId<M>>,

  // Quotient
  pub quot_type: Option<MetaId<M>>,
  pub quot_ctor: Option<MetaId<M>>,
  pub quot_lift: Option<MetaId<M>>,
  pub quot_ind: Option<MetaId<M>>,

  // Special reduction markers
  pub reduce_bool: Option<MetaId<M>>,
  pub reduce_nat: Option<MetaId<M>>,
  pub eager_reduce: Option<MetaId<M>>,

  // Platform-dependent constants
  pub system_platform_num_bits: Option<MetaId<M>>,
}

/// Word size mode for platform-dependent reduction.
/// Controls what `System.Platform.numBits` reduces to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum WordSize {
  #[default]
  Word64,
  Word32,
}

impl WordSize {
  pub fn num_bits(self) -> u64 {
    match self {
      WordSize::Word64 => 64,
      WordSize::Word32 => 32,
    }
  }
}

impl<M: MetaMode> Default for Primitives<M> {
  fn default() -> Self {
    Primitives {
      nat: None,
      nat_zero: None,
      nat_succ: None,
      nat_add: None,
      nat_pred: None,
      nat_sub: None,
      nat_mul: None,
      nat_pow: None,
      nat_gcd: None,
      nat_mod: None,
      nat_div: None,
      nat_bitwise: None,
      nat_beq: None,
      nat_ble: None,
      nat_land: None,
      nat_lor: None,
      nat_xor: None,
      nat_shift_left: None,
      nat_shift_right: None,
      bool_type: None,
      bool_true: None,
      bool_false: None,
      string: None,
      string_mk: None,
      char_type: None,
      char_mk: None,
      string_of_list: None,
      list: None,
      list_nil: None,
      list_cons: None,
      eq: None,
      eq_refl: None,
      quot_type: None,
      quot_ctor: None,
      quot_lift: None,
      quot_ind: None,
      reduce_bool: None,
      reduce_nat: None,
      eager_reduce: None,
      system_platform_num_bits: None,
    }
  }
}

impl<M: MetaMode> Primitives<M> {
  /// Get the address for a primitive field.
  pub fn addr_of(
    field: &Option<MetaId<M>>,
  ) -> Option<&Address> {
    field.as_ref().map(|id| &id.addr)
  }

  /// Check if a primitive field matches the given address.
  pub fn addr_matches(
    field: &Option<MetaId<M>>,
    addr: &Address,
  ) -> bool {
    field.as_ref().is_some_and(|id| id.addr == *addr)
  }

  /// Count how many primitive fields are resolved (Some) and which are missing.
  pub fn count_resolved(&self) -> (usize, Vec<&'static str>) {
    let fields: &[(&'static str, &Option<MetaId<M>>)] = &[
      ("Nat", &self.nat),
      ("Nat.zero", &self.nat_zero),
      ("Nat.succ", &self.nat_succ),
      ("Nat.add", &self.nat_add),
      ("Nat.pred", &self.nat_pred),
      ("Nat.sub", &self.nat_sub),
      ("Nat.mul", &self.nat_mul),
      ("Nat.pow", &self.nat_pow),
      ("Nat.gcd", &self.nat_gcd),
      ("Nat.mod", &self.nat_mod),
      ("Nat.div", &self.nat_div),
      ("Nat.bitwise", &self.nat_bitwise),
      ("Nat.beq", &self.nat_beq),
      ("Nat.ble", &self.nat_ble),
      ("Nat.land", &self.nat_land),
      ("Nat.lor", &self.nat_lor),
      ("Nat.xor", &self.nat_xor),
      ("Nat.shiftLeft", &self.nat_shift_left),
      ("Nat.shiftRight", &self.nat_shift_right),
      ("Bool", &self.bool_type),
      ("Bool.true", &self.bool_true),
      ("Bool.false", &self.bool_false),
      ("String", &self.string),
      ("String.mk", &self.string_mk),
      ("Char", &self.char_type),
      ("Char.mk", &self.char_mk),
      ("String.ofList", &self.string_of_list),
      ("List", &self.list),
      ("List.nil", &self.list_nil),
      ("List.cons", &self.list_cons),
      ("Eq", &self.eq),
      ("Eq.refl", &self.eq_refl),
      ("Quot", &self.quot_type),
      ("Quot.mk", &self.quot_ctor),
      ("Quot.lift", &self.quot_lift),
      ("Quot.ind", &self.quot_ind),
      ("reduceBool", &self.reduce_bool),
      ("reduceNat", &self.reduce_nat),
      ("eagerReduce", &self.eager_reduce),
      ("System.Platform.numBits", &self.system_platform_num_bits),
    ];
    let mut count = 0;
    let mut missing = Vec::new();
    for (name, opt) in fields {
      if opt.is_some() {
        count += 1;
      } else {
        missing.push(*name);
      }
    }
    (count, missing)
  }
}

// ============================================================================
// TypeInfo, TypedExpr, TypedConst — post-type-check representation
// ============================================================================

/// Classification of a type for optimization purposes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeInfo<M: MetaMode> {
  /// The type is a unit-like type (single constructor, no fields).
  Unit,
  /// The type is a proof (lives in Prop / Sort 0).
  Proof,
  /// No special classification.
  None,
  /// The type is itself a sort at the given level.
  Sort(KLevel<M>),
}

/// An expression annotated with type information.
#[derive(Debug, Clone)]
pub struct TypedExpr<M: MetaMode> {
  pub info: TypeInfo<M>,
  pub body: KExpr<M>,
}

/// Post-type-checking constant representation, carrying extracted metadata
/// needed for WHNF reduction.
#[derive(Debug, Clone)]
pub enum TypedConst<M: MetaMode> {
  Axiom {
    typ: TypedExpr<M>,
  },
  Theorem {
    typ: TypedExpr<M>,
    value: TypedExpr<M>,
  },
  Inductive {
    typ: TypedExpr<M>,
    is_struct: bool,
  },
  Opaque {
    typ: TypedExpr<M>,
    value: TypedExpr<M>,
  },
  Definition {
    typ: TypedExpr<M>,
    value: TypedExpr<M>,
    is_partial: bool,
  },
  Constructor {
    typ: TypedExpr<M>,
    cidx: usize,
    num_fields: usize,
  },
  Recursor {
    typ: TypedExpr<M>,
    num_params: usize,
    num_motives: usize,
    num_minors: usize,
    num_indices: usize,
    k: bool,
    induct_addr: Address,
    /// Rules: (nfields, typed rhs)
    rules: Vec<(usize, TypedExpr<M>)>,
  },
  Quotient {
    typ: TypedExpr<M>,
    kind: QuotKind,
  },
}

impl<M: MetaMode> TypedConst<M> {
  /// Returns the typed type expression.
  pub fn typ(&self) -> &TypedExpr<M> {
    match self {
      TypedConst::Axiom { typ }
      | TypedConst::Theorem { typ, .. }
      | TypedConst::Inductive { typ, .. }
      | TypedConst::Opaque { typ, .. }
      | TypedConst::Definition { typ, .. }
      | TypedConst::Constructor { typ, .. }
      | TypedConst::Recursor { typ, .. }
      | TypedConst::Quotient { typ, .. } => typ,
    }
  }
}
