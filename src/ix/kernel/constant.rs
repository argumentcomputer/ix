//! Constant declarations parameterized by `KernelMode`.
//!
//! Each variant carries structural fields plus metadata fields
//! (`name`, `level_params`, `lean_all`) for roundtrip fidelity in Meta mode.

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, Name, QuotKind, ReducibilityHints};
use crate::ix::ixon::constant::DefKind;

use super::expr::KExpr;
use super::id::KId;
use super::mode::KernelMode;

/// A recursor computation rule.
#[derive(Clone, Debug)]
pub struct RecRule<M: KernelMode> {
  pub fields: u64,
  pub rhs: KExpr<M>,
}

/// A loaded constant.
#[derive(Clone, Debug)]
pub enum KConst<M: KernelMode> {
  Defn {
    name: M::MField<Name>,
    level_params: M::MField<Vec<Name>>,
    kind: DefKind,
    safety: DefinitionSafety,
    hints: ReducibilityHints,
    lvls: u64,
    ty: KExpr<M>,
    val: KExpr<M>,
    lean_all: M::MField<Vec<KId<M>>>,
    block: KId<M>,
  },
  Recr {
    name: M::MField<Name>,
    level_params: M::MField<Vec<Name>>,
    k: bool,
    is_unsafe: bool,
    lvls: u64,
    params: u64,
    indices: u64,
    motives: u64,
    minors: u64,
    block: KId<M>,
    member_idx: u64,
    ty: KExpr<M>,
    rules: Vec<RecRule<M>>,
    lean_all: M::MField<Vec<KId<M>>>,
  },
  Axio {
    name: M::MField<Name>,
    level_params: M::MField<Vec<Name>>,
    is_unsafe: bool,
    lvls: u64,
    ty: KExpr<M>,
  },
  Quot {
    name: M::MField<Name>,
    level_params: M::MField<Vec<Name>>,
    kind: QuotKind,
    lvls: u64,
    ty: KExpr<M>,
  },
  Indc {
    name: M::MField<Name>,
    level_params: M::MField<Vec<Name>>,
    lvls: u64,
    params: u64,
    indices: u64,
    is_rec: bool,
    is_refl: bool,
    is_unsafe: bool,
    nested: u64,
    block: KId<M>,
    member_idx: u64,
    ty: KExpr<M>,
    ctors: Vec<KId<M>>,
    lean_all: M::MField<Vec<KId<M>>>,
  },
  Ctor {
    name: M::MField<Name>,
    level_params: M::MField<Vec<Name>>,
    is_unsafe: bool,
    lvls: u64,
    induct: KId<M>,
    cidx: u64,
    params: u64,
    fields: u64,
    ty: KExpr<M>,
  },
}

impl<M: KernelMode> KConst<M> {
  pub fn ty(&self) -> &KExpr<M> {
    match self {
      KConst::Defn { ty, .. }
      | KConst::Recr { ty, .. }
      | KConst::Axio { ty, .. }
      | KConst::Quot { ty, .. }
      | KConst::Indc { ty, .. }
      | KConst::Ctor { ty, .. } => ty,
    }
  }

  pub fn lvls(&self) -> u64 {
    match self {
      KConst::Defn { lvls, .. }
      | KConst::Recr { lvls, .. }
      | KConst::Axio { lvls, .. }
      | KConst::Quot { lvls, .. }
      | KConst::Indc { lvls, .. }
      | KConst::Ctor { lvls, .. } => *lvls,
    }
  }

  pub fn name(&self) -> &M::MField<Name> {
    match self {
      KConst::Defn { name, .. }
      | KConst::Recr { name, .. }
      | KConst::Axio { name, .. }
      | KConst::Quot { name, .. }
      | KConst::Indc { name, .. }
      | KConst::Ctor { name, .. } => name,
    }
  }

  pub fn level_params(&self) -> &M::MField<Vec<Name>> {
    #[allow(unreachable_patterns)]
    match self {
      KConst::Defn { level_params, .. }
      | KConst::Recr { level_params, .. }
      | KConst::Axio { level_params, .. }
      | KConst::Quot { level_params, .. }
      | KConst::Indc { level_params, .. }
      | KConst::Ctor { level_params, .. } => level_params,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::super::expr::KExpr;
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::Anon;
  use super::*;
  use crate::ix::env::{DefinitionSafety, QuotKind, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;

  fn sort0() -> KExpr<Anon> {
    KExpr::sort(KUniv::zero())
  }
  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  #[test]
  fn axio_accessors() {
    let c = KConst::<Anon>::Axio {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 2,
      ty: sort0(),
    };
    assert_eq!(c.lvls(), 2);
    assert_eq!(*c.name(), ());
    assert_eq!(*c.level_params(), ());
    assert!(matches!(c.ty().data(), super::super::expr::ExprData::Sort(..)));
  }

  #[test]
  fn defn_accessors() {
    let c = KConst::<Anon>::Defn {
      name: (),
      level_params: (),
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      hints: ReducibilityHints::Regular(5),
      lvls: 1,
      ty: sort0(),
      val: sort0(),
      lean_all: (),
      block: KId::new(mk_addr("block"), ()),
    };
    assert_eq!(c.lvls(), 1);
  }

  #[test]
  fn quot_accessors() {
    let c = KConst::<Anon>::Quot {
      name: (),
      level_params: (),
      kind: QuotKind::Type,
      lvls: 1,
      ty: sort0(),
    };
    assert_eq!(c.lvls(), 1);
  }

  #[test]
  fn ctor_accessors() {
    let c = KConst::<Anon>::Ctor {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 0,
      induct: KId::new(mk_addr("Nat"), ()),
      cidx: 0,
      params: 0,
      fields: 0,
      ty: sort0(),
    };
    assert_eq!(c.lvls(), 0);
  }

  #[test]
  fn indc_accessors() {
    let c = KConst::<Anon>::Indc {
      name: (),
      level_params: (),
      lvls: 0,
      params: 2,
      indices: 0,
      is_rec: false,
      is_refl: false,
      is_unsafe: false,
      nested: 0,
      block: KId::new(mk_addr("block"), ()),
      member_idx: 0,
      ty: sort0(),
      ctors: vec![],
      lean_all: (),
    };
    assert_eq!(c.lvls(), 0);
    assert!(matches!(c, KConst::Indc { params: 2, .. }));
  }
}
