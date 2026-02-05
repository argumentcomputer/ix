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

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{ConstantVal, Level};

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn sort0() -> Expr {
    Expr::sort(Level::zero())
  }

  fn mk_constant_val(name: &str) -> ConstantVal {
    ConstantVal { name: n(name), level_params: vec![], typ: sort0() }
  }

  fn mk_def(name: &str) -> MutConst {
    MutConst::Defn(Def {
      name: n(name),
      level_params: vec![],
      typ: sort0(),
      kind: DefKind::Definition,
      value: Expr::bvar(Nat(0u64.into())),
      hints: ReducibilityHints::Opaque,
      safety: DefinitionSafety::Safe,
      all: vec![n(name)],
    })
  }

  fn mk_ind(name: &str, ctor_names: &[&str]) -> MutConst {
    let ctors = ctor_names
      .iter()
      .enumerate()
      .map(|(i, cn)| ConstructorVal {
        cnst: mk_constant_val(cn),
        induct: n(name),
        cidx: Nat::from(i as u64),
        num_params: Nat(0u64.into()),
        num_fields: Nat(0u64.into()),
        is_unsafe: false,
      })
      .collect();
    MutConst::Indc(Ind {
      ind: InductiveVal {
        cnst: mk_constant_val(name),
        num_params: Nat(0u64.into()),
        num_indices: Nat(0u64.into()),
        all: vec![n(name)],
        ctors: ctor_names.iter().map(|c| n(c)).collect(),
        num_nested: Nat(0u64.into()),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      },
      ctors,
    })
  }

  fn mk_rec(name: &str) -> MutConst {
    MutConst::Recr(RecursorVal {
      cnst: mk_constant_val(name),
      all: vec![n(name)],
      num_params: Nat(0u64.into()),
      num_indices: Nat(0u64.into()),
      num_motives: Nat(1u64.into()),
      num_minors: Nat(0u64.into()),
      rules: vec![],
      k: false,
      is_unsafe: false,
    })
  }

  #[test]
  fn all_to_ctx_assigns_indices() {
    let names = vec![n("A"), n("B"), n("C")];
    let ctx = all_to_ctx(&names);
    assert_eq!(ctx.get(&n("A")), Some(&Nat(0u64.into())));
    assert_eq!(ctx.get(&n("B")), Some(&Nat(1u64.into())));
    assert_eq!(ctx.get(&n("C")), Some(&Nat(2u64.into())));
    assert_eq!(ctx.len(), 3);
  }

  #[test]
  fn ctx_to_all_roundtrip() {
    let names = vec![n("X"), n("Y"), n("Z")];
    let ctx = all_to_ctx(&names);
    let recovered = ctx_to_all(&ctx);
    assert_eq!(recovered, names);
  }

  #[test]
  fn single_ctx_has_one_entry() {
    let ctx = MutConst::single_ctx(n("Foo"));
    assert_eq!(ctx.len(), 1);
    assert_eq!(ctx.get(&n("Foo")), Some(&Nat(0u64.into())));
  }

  #[test]
  fn ctx_single_class_defs_only() {
    let d1 = mk_def("f");
    let d2 = mk_def("g");
    let classes: Vec<Vec<&MutConst>> = vec![vec![&d1, &d2]];
    let ctx = MutConst::ctx(&classes);
    // Both defs get the class index (0) since they're in class 0
    assert_eq!(ctx.get(&n("f")), Some(&Nat(0u64.into())));
    assert_eq!(ctx.get(&n("g")), Some(&Nat(0u64.into())));
  }

  #[test]
  fn ctx_class_with_ctors() {
    let ind = mk_ind("Bool", &["Bool.true", "Bool.false"]);
    let classes: Vec<Vec<&MutConst>> = vec![vec![&ind]];
    let ctx = MutConst::ctx(&classes);
    // The type gets class index 0
    assert_eq!(ctx.get(&n("Bool")), Some(&Nat(0u64.into())));
    // Ctors start at classes.len() = 1
    assert_eq!(ctx.get(&n("Bool.true")), Some(&Nat(1u64.into())));
    assert_eq!(ctx.get(&n("Bool.false")), Some(&Nat(2u64.into())));
  }

  #[test]
  fn ctx_two_classes() {
    // Class 0: inductive with 2 ctors
    let ind = mk_ind("A", &["A.mk1", "A.mk2"]);
    // Class 1: definition (no ctors)
    let def = mk_def("f");
    let classes: Vec<Vec<&MutConst>> = vec![vec![&ind], vec![&def]];
    let ctx = MutConst::ctx(&classes);
    // Class 0: A at index 0
    assert_eq!(ctx.get(&n("A")), Some(&Nat(0u64.into())));
    // Class 1: f at index 1
    assert_eq!(ctx.get(&n("f")), Some(&Nat(1u64.into())));
    // i starts at classes.len()=2. Class 0 has 2 ctors, so:
    assert_eq!(ctx.get(&n("A.mk1")), Some(&Nat(2u64.into())));
    assert_eq!(ctx.get(&n("A.mk2")), Some(&Nat(3u64.into())));
  }

  #[test]
  fn contains_defn() {
    let d = mk_def("f");
    assert!(d.contains(&n("f")));
    assert!(!d.contains(&n("g")));
  }

  #[test]
  fn contains_indc_and_ctors() {
    let ind = mk_ind("Nat", &["Nat.zero", "Nat.succ"]);
    assert!(ind.contains(&n("Nat")));
    assert!(ind.contains(&n("Nat.zero")));
    assert!(ind.contains(&n("Nat.succ")));
    assert!(!ind.contains(&n("Bool")));
  }

  #[test]
  fn contains_recr() {
    let r = mk_rec("Nat.rec");
    assert!(r.contains(&n("Nat.rec")));
    assert!(!r.contains(&n("Bool.rec")));
  }

  #[test]
  fn name_returns_correct_name() {
    assert_eq!(mk_def("f").name(), n("f"));
    assert_eq!(mk_ind("T", &["T.mk"]).name(), n("T"));
    assert_eq!(mk_rec("T.rec").name(), n("T.rec"));
  }

  #[test]
  fn ctors_returns_empty_for_non_inductive() {
    assert!(mk_def("f").ctors().is_empty());
    assert!(mk_rec("r").ctors().is_empty());
  }

  #[test]
  fn ctors_returns_constructor_vals_for_inductive() {
    let ind = mk_ind("T", &["T.mk1", "T.mk2"]);
    let ctors = ind.ctors();
    assert_eq!(ctors.len(), 2);
    assert_eq!(ctors[0].cnst.name, n("T.mk1"));
    assert_eq!(ctors[1].cnst.name, n("T.mk2"));
  }
}
