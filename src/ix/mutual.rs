//! Types for representing mutual definition blocks in the compilation pipeline.
//!
//! Mutual blocks are groups of definitions that reference each other cyclically.
//! [`MutCtx`] maps names to their indices within a mutual block, and the
//! [`ctx_to_all`] / [`all_to_ctx`] functions convert between ordered name
//! vectors and index maps.

use crate::{
  ix::env::{
    ConstructorVal, DefinitionSafety, DefinitionVal, Expr, InductiveVal, Name,
    OpaqueVal, RecursorVal, ReducibilityHints, TheoremVal,
  },
  ix::ixon::constant::DefKind,
  lean::nat::Nat,
};

use rustc_hash::FxHashMap;

/// A definition-like constant (definition, theorem, or opaque) unified into a
/// single representation for mutual block processing.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Def {
  /// Fully-qualified name of the definition.
  pub name: Name,
  /// Universe-polymorphic level parameter names.
  pub level_params: Vec<Name>,
  /// The type of the definition.
  pub typ: Expr,
  /// The kind of definition (definition, theorem, or opaque).
  pub kind: DefKind,
  /// The definition body.
  pub value: Expr,
  /// Reducibility hints for the kernel.
  pub hints: ReducibilityHints,
  /// Safety classification.
  pub safety: DefinitionSafety,
  /// Names of all constants in the same mutual block.
  pub all: Vec<Name>,
}

impl Def {
  /// Constructs a `Def` from a [`DefinitionVal`].
  pub fn mk_defn(val: &DefinitionVal) -> Self {
    let DefinitionVal { cnst, value, hints, safety, all } = val;
    Self {
      name: cnst.name.clone(),
      level_params: cnst.level_params.clone(),
      typ: cnst.typ.clone(),
      kind: DefKind::Definition,
      value: value.clone(),
      hints: *hints,
      safety: *safety,
      all: all.clone(),
    }
  }
  /// Constructs a `Def` from a [`TheoremVal`].
  pub fn mk_theo(val: &TheoremVal) -> Self {
    let TheoremVal { cnst, value, all } = val;
    Self {
      name: cnst.name.clone(),
      level_params: cnst.level_params.clone(),
      typ: cnst.typ.clone(),
      kind: DefKind::Theorem,
      value: value.clone(),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: all.clone(),
    }
  }
  /// Constructs a `Def` from an [`OpaqueVal`].
  pub fn mk_opaq(val: &OpaqueVal) -> Self {
    let OpaqueVal { cnst, value, is_unsafe, all } = val;
    Self {
      name: cnst.name.clone(),
      level_params: cnst.level_params.clone(),
      typ: cnst.typ.clone(),
      kind: DefKind::Opaque,
      value: value.clone(),
      hints: ReducibilityHints::Opaque,
      safety: if *is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      },
      all: all.clone(),
    }
  }
}

/// An inductive type bundled with its constructors for mutual block processing.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ind {
  /// The inductive type declaration.
  pub ind: InductiveVal,
  /// The constructors belonging to this inductive type.
  pub ctors: Vec<ConstructorVal>,
}

/// Type alias for a recursor value within a mutual block.
pub type Rec = RecursorVal;

/// A constant within a mutual definition block.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum MutConst {
  /// A definition, theorem, or opaque constant.
  Defn(Def),
  /// An inductive type with its constructors.
  Indc(Ind),
  /// A recursor (eliminator).
  Recr(Rec),
}

/// Maps names to their index within a mutual block.
pub type MutCtx = FxHashMap<Name, Nat>;

/// Convert a MutCtx to a Vec<Name> ordered by index.
/// Position i contains the name with Nat value i.
pub fn ctx_to_all(ctx: &MutCtx) -> Vec<Name> {
  let mut pairs: Vec<_> = ctx.iter().collect();
  pairs.sort_by(|(n1, i1), (n2, i2)| {
    i1.to_u64()
      .unwrap_or(0)
      .cmp(&i2.to_u64().unwrap_or(0))
      .then_with(|| n1.cmp(n2))
  });
  pairs.into_iter().map(|(name, _)| name.clone()).collect()
}

/// Convert a Vec<Name> to a MutCtx.
/// Each name gets its position as the Nat value.
pub fn all_to_ctx(all: &[Name]) -> MutCtx {
  let mut ctx = FxHashMap::default();
  for (i, name) in all.iter().enumerate() {
    ctx.insert(name.clone(), Nat(i.into()));
  }
  ctx
}

impl MutConst {
  /// Returns the name of this mutual constant.
  pub fn name(&self) -> Name {
    match self {
      Self::Defn(x) => x.name.clone(),
      Self::Recr(x) => x.cnst.name.clone(),
      Self::Indc(x) => x.ind.cnst.name.clone(),
    }
  }

  /// Returns the constructors if this is an inductive, or an empty vec otherwise.
  pub fn ctors(&self) -> Vec<ConstructorVal> {
    match self {
      Self::Indc(ind) => ind.ctors.clone(),
      _ => vec![],
    }
  }
  /// Returns `true` if this mutual constant contains the given name
  /// (including constructor names for inductives).
  pub fn contains(&self, name: &Name) -> bool {
    match self {
      Self::Defn(x) => x.name == *name,
      Self::Recr(x) => x.cnst.name == *name,
      Self::Indc(x) => {
        x.ind.cnst.name == *name || x.ctors.iter().any(|c| c.cnst.name == *name)
      },
    }
  }
  /// Creates a [`MutCtx`] with a single name at index 0.
  pub fn single_ctx(name: Name) -> MutCtx {
    let mut mut_ctx = FxHashMap::default();
    mut_ctx.insert(name, Nat(0u64.into()));
    mut_ctx
  }

  /// Builds a [`MutCtx`] from grouped mutual constant classes, assigning
  /// indices to types first and then to constructors.
  pub fn ctx(classes: &[Vec<&MutConst>]) -> MutCtx {
    let mut mut_ctx = FxHashMap::default();
    let mut i = classes.len();
    for (j, consts) in classes.iter().enumerate() {
      let mut max_ctors = 0;
      for cnst in consts {
        mut_ctx.insert(cnst.name(), Nat(j.into()));
        max_ctors = usize::max(max_ctors, cnst.ctors().len());
        for (cidx, c) in cnst.ctors().iter().enumerate() {
          mut_ctx.insert(c.cnst.name.clone(), Nat((i + cidx).into()));
        }
      }
      i += max_ctors;
    }
    mut_ctx
  }
}
