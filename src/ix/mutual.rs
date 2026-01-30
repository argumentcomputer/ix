use crate::{
  ix::env::{
    ConstructorVal, DefinitionSafety, DefinitionVal, Expr, InductiveVal, Name,
    OpaqueVal, RecursorVal, ReducibilityHints, TheoremVal,
  },
  ix::ixon_old::DefKind,
  lean::nat::Nat,
};

use rustc_hash::FxHashMap;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Def {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
  pub kind: DefKind,
  pub value: Expr,
  pub hints: ReducibilityHints,
  pub safety: DefinitionSafety,
  pub all: Vec<Name>,
}

impl Def {
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

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ind {
  pub ind: InductiveVal,
  pub ctors: Vec<ConstructorVal>,
}

pub type Rec = RecursorVal;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum MutConst {
  Defn(Def),
  Indc(Ind),
  Recr(Rec),
}

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
  pub fn name(&self) -> Name {
    match self {
      Self::Defn(x) => x.name.clone(),
      Self::Recr(x) => x.cnst.name.clone(),
      Self::Indc(x) => x.ind.cnst.name.clone(),
    }
  }

  pub fn ctors(&self) -> Vec<ConstructorVal> {
    match self {
      Self::Indc(ind) => ind.ctors.clone(),
      _ => vec![],
    }
  }
  pub fn contains(&self, name: &Name) -> bool {
    match self {
      Self::Defn(x) => x.name == *name,
      Self::Recr(x) => x.cnst.name == *name,
      Self::Indc(x) => {
        x.ind.cnst.name == *name || x.ctors.iter().any(|c| c.cnst.name == *name)
      },
    }
  }
  pub fn single_ctx(name: Name) -> MutCtx {
    let mut mut_ctx = FxHashMap::default();
    mut_ctx.insert(name, Nat(0u64.into()));
    mut_ctx
  }

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
