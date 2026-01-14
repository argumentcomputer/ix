//! Constants in the Ixon format.
//!
//! These are alpha-invariant representations of Lean constants.
//! Metadata (names, binder info) is stored separately in the names map.
//!
//! The sharing vector is stored at the Constant level, shared across
//! all expressions in the constant (including mutual block members).

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, QuotKind};

use super::expr::Expr;
use super::univ::Univ;

/// Definition kind (definition, opaque, or theorem).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DefKind {
  Definition,
  Opaque,
  Theorem,
}

/// A definition constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Definition {
  pub kind: DefKind,
  pub safety: DefinitionSafety,
  /// Number of universe parameters
  pub lvls: u64,
  /// Type expression
  pub typ: Arc<Expr>,
  /// Value expression
  pub value: Arc<Expr>,
}

/// A recursor rule (computation rule).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorRule {
  /// Number of fields in this constructor
  pub fields: u64,
  /// Right-hand side expression
  pub rhs: Arc<Expr>,
}

/// A recursor constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recursor {
  /// K-like recursor (eliminates into Prop)
  pub k: bool,
  pub is_unsafe: bool,
  /// Number of universe parameters
  pub lvls: u64,
  /// Number of parameters
  pub params: u64,
  /// Number of indices
  pub indices: u64,
  /// Number of motives
  pub motives: u64,
  /// Number of minor premises
  pub minors: u64,
  /// Type expression
  pub typ: Arc<Expr>,
  /// Computation rules
  pub rules: Vec<RecursorRule>,
}

/// An axiom constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Axiom {
  pub is_unsafe: bool,
  /// Number of universe parameters
  pub lvls: u64,
  /// Type expression
  pub typ: Arc<Expr>,
}

/// A quotient constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Quotient {
  pub kind: QuotKind,
  /// Number of universe parameters
  pub lvls: u64,
  /// Type expression
  pub typ: Arc<Expr>,
}

/// A constructor within an inductive type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
  pub is_unsafe: bool,
  /// Number of universe parameters
  pub lvls: u64,
  /// Constructor index
  pub cidx: u64,
  /// Number of parameters
  pub params: u64,
  /// Number of fields
  pub fields: u64,
  /// Type expression
  pub typ: Arc<Expr>,
}

/// An inductive type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inductive {
  /// Has recursive occurrences
  pub recr: bool,
  /// Is reflexive
  pub refl: bool,
  pub is_unsafe: bool,
  /// Number of universe parameters
  pub lvls: u64,
  /// Number of parameters
  pub params: u64,
  /// Number of indices
  pub indices: u64,
  /// Nested inductive depth
  pub nested: u64,
  /// Type expression
  pub typ: Arc<Expr>,
  /// Constructors
  pub ctors: Vec<Constructor>,
}

/// Projection into a mutual block for an inductive type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveProj {
  /// Index within the mutual block
  pub idx: u64,
  /// Address of the mutual block
  pub block: Address,
}

/// Projection into a mutual block for a constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructorProj {
  /// Inductive index within the mutual block
  pub idx: u64,
  /// Constructor index within the inductive
  pub cidx: u64,
  /// Address of the mutual block
  pub block: Address,
}

/// Projection into a mutual block for a recursor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorProj {
  /// Index within the mutual block
  pub idx: u64,
  /// Address of the mutual block
  pub block: Address,
}

/// Projection into a mutual block for a definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefinitionProj {
  /// Index within the mutual block
  pub idx: u64,
  /// Address of the mutual block
  pub block: Address,
}

/// A constant within a mutual block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MutConst {
  Defn(Definition),
  Indc(Inductive),
  Recr(Recursor),
}

/// The variant/payload of a constant (alpha-invariant, no metadata).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstantInfo {
  Defn(Definition),
  Recr(Recursor),
  Axio(Axiom),
  Quot(Quotient),
  CPrj(ConstructorProj),
  RPrj(RecursorProj),
  IPrj(InductiveProj),
  DPrj(DefinitionProj),
  Muts(Vec<MutConst>),
}

impl ConstantInfo {
  // Constant variant indices (used as Tag4 size field)
  pub const CONST_DEFN: u64 = 0;
  pub const CONST_RECR: u64 = 1;
  pub const CONST_AXIO: u64 = 2;
  pub const CONST_QUOT: u64 = 3;
  pub const CONST_CPRJ: u64 = 4;
  pub const CONST_RPRJ: u64 = 5;
  pub const CONST_IPRJ: u64 = 6;
  pub const CONST_DPRJ: u64 = 7;
  pub const CONST_MUTS: u64 = 8;

  /// Returns the variant index (used as Tag4 size field)
  pub fn variant(&self) -> u64 {
    match self {
      Self::Defn(_) => Self::CONST_DEFN,
      Self::Recr(_) => Self::CONST_RECR,
      Self::Axio(_) => Self::CONST_AXIO,
      Self::Quot(_) => Self::CONST_QUOT,
      Self::CPrj(_) => Self::CONST_CPRJ,
      Self::RPrj(_) => Self::CONST_RPRJ,
      Self::IPrj(_) => Self::CONST_IPRJ,
      Self::DPrj(_) => Self::CONST_DPRJ,
      Self::Muts(_) => Self::CONST_MUTS,
    }
  }
}

/// A top-level constant with its sharing, refs, and univs vectors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constant {
  /// The constant payload
  pub info: ConstantInfo,
  /// Shared subexpressions referenced by Expr::Share(idx)
  pub sharing: Vec<Arc<Expr>>,
  /// Reference table: addresses referenced by Expr::Ref(idx, _), Expr::Prj, Expr::Str, Expr::Nat
  pub refs: Vec<Address>,
  /// Universe table: universes referenced by Expr::Sort(idx), Expr::Ref(_, univs), Expr::Rec(_, univs)
  pub univs: Vec<Arc<Univ>>,
}

impl Constant {
  /// Tag4 flag used for all constants (discriminated by size field)
  pub const FLAG: u8 = 0xD;

  /// Create a new constant with no sharing, refs, or univs
  pub fn new(info: ConstantInfo) -> Self {
    Constant { info, sharing: Vec::new(), refs: Vec::new(), univs: Vec::new() }
  }

  /// Create a new constant with sharing, refs, and univs
  pub fn with_tables(info: ConstantInfo, sharing: Vec<Arc<Expr>>, refs: Vec<Address>, univs: Vec<Arc<Univ>>) -> Self {
    Constant { info, sharing, refs, univs }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::ix::env::{DefinitionSafety, QuotKind};
  use crate::ix::ixon::expr::tests::arbitrary_expr;
  use crate::ix::ixon::tests::gen_range;
  use quickcheck::{Arbitrary, Gen};

  impl Arbitrary for DefKind {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 { 0 => DefKind::Definition, 1 => DefKind::Opaque, _ => DefKind::Theorem }
    }
  }

  impl Arbitrary for DefinitionSafety {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 { 0 => DefinitionSafety::Unsafe, 1 => DefinitionSafety::Safe, _ => DefinitionSafety::Partial }
    }
  }

  impl Arbitrary for QuotKind {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 4 { 0 => QuotKind::Type, 1 => QuotKind::Ctor, 2 => QuotKind::Lift, _ => QuotKind::Ind }
    }
  }

  pub fn gen_sharing(g: &mut Gen) -> Vec<Arc<Expr>> {
    (0..gen_range(g, 0..4)).map(|_| arbitrary_expr(g)).collect()
  }

  pub fn gen_refs(g: &mut Gen) -> Vec<Address> {
    (0..gen_range(g, 0..4)).map(|_| Address::arbitrary(g)).collect()
  }

  pub fn gen_univs(g: &mut Gen) -> Vec<Arc<Univ>> {
    use crate::ix::ixon::univ::tests::arbitrary_univ;
    (0..gen_range(g, 0..4)).map(|_| arbitrary_univ(g)).collect()
  }

  pub fn gen_definition(g: &mut Gen) -> Definition {
    Definition {
      kind: DefKind::arbitrary(g), safety: DefinitionSafety::arbitrary(g),
      lvls: u64::arbitrary(g) % 10, typ: arbitrary_expr(g), value: arbitrary_expr(g),
    }
  }

  fn gen_recursor_rule(g: &mut Gen) -> RecursorRule {
    RecursorRule { fields: u64::arbitrary(g) % 10, rhs: arbitrary_expr(g) }
  }

  pub fn gen_recursor(g: &mut Gen) -> Recursor {
    Recursor {
      k: bool::arbitrary(g), is_unsafe: bool::arbitrary(g),
      lvls: u64::arbitrary(g) % 10, params: u64::arbitrary(g) % 10, indices: u64::arbitrary(g) % 5,
      motives: u64::arbitrary(g) % 3, minors: u64::arbitrary(g) % 10, typ: arbitrary_expr(g),
      rules: (0..gen_range(g, 0..5)).map(|_| gen_recursor_rule(g)).collect(),
    }
  }

  pub fn gen_axiom(g: &mut Gen) -> Axiom {
    Axiom { is_unsafe: bool::arbitrary(g), lvls: u64::arbitrary(g) % 10, typ: arbitrary_expr(g) }
  }

  pub fn gen_quotient(g: &mut Gen) -> Quotient {
    Quotient { kind: QuotKind::arbitrary(g), lvls: u64::arbitrary(g) % 10, typ: arbitrary_expr(g) }
  }

  fn gen_constructor(g: &mut Gen) -> Constructor {
    Constructor {
      is_unsafe: bool::arbitrary(g), lvls: u64::arbitrary(g) % 10, cidx: u64::arbitrary(g) % 10,
      params: u64::arbitrary(g) % 10, fields: u64::arbitrary(g) % 10, typ: arbitrary_expr(g),
    }
  }

  pub fn gen_inductive(g: &mut Gen) -> Inductive {
    Inductive {
      recr: bool::arbitrary(g), refl: bool::arbitrary(g), is_unsafe: bool::arbitrary(g),
      lvls: u64::arbitrary(g) % 10, params: u64::arbitrary(g) % 10, indices: u64::arbitrary(g) % 5,
      nested: u64::arbitrary(g) % 3, typ: arbitrary_expr(g),
      ctors: (0..gen_range(g, 0..4)).map(|_| gen_constructor(g)).collect(),
    }
  }

  fn gen_mut_const(g: &mut Gen) -> MutConst {
    match u8::arbitrary(g) % 3 {
      0 => MutConst::Defn(gen_definition(g)), 1 => MutConst::Indc(gen_inductive(g)), _ => MutConst::Recr(gen_recursor(g)),
    }
  }

  fn gen_constant_info(g: &mut Gen) -> ConstantInfo {
    match u8::arbitrary(g) % 9 {
      0 => ConstantInfo::Defn(gen_definition(g)),
      1 => ConstantInfo::Recr(gen_recursor(g)),
      2 => ConstantInfo::Axio(gen_axiom(g)),
      3 => ConstantInfo::Quot(gen_quotient(g)),
      4 => ConstantInfo::CPrj(ConstructorProj { idx: u64::arbitrary(g) % 10, cidx: u64::arbitrary(g) % 10, block: Address::arbitrary(g) }),
      5 => ConstantInfo::RPrj(RecursorProj { idx: u64::arbitrary(g) % 10, block: Address::arbitrary(g) }),
      6 => ConstantInfo::IPrj(InductiveProj { idx: u64::arbitrary(g) % 10, block: Address::arbitrary(g) }),
      7 => ConstantInfo::DPrj(DefinitionProj { idx: u64::arbitrary(g) % 10, block: Address::arbitrary(g) }),
      _ => ConstantInfo::Muts((0..gen_range(g, 1..4)).map(|_| gen_mut_const(g)).collect()),
    }
  }

  pub fn gen_constant(g: &mut Gen) -> Constant {
    Constant {
      info: gen_constant_info(g),
      sharing: gen_sharing(g),
      refs: gen_refs(g),
      univs: gen_univs(g),
    }
  }

  #[derive(Clone, Debug)]
  struct ArbitraryConstant(Constant);

  impl Arbitrary for ArbitraryConstant {
    fn arbitrary(g: &mut Gen) -> Self { ArbitraryConstant(gen_constant(g)) }
  }

  fn constant_roundtrip(c: &Constant) -> bool {
    let mut buf = Vec::new();
    c.put(&mut buf);
    match Constant::get(&mut buf.as_slice()) {
      Ok(c2) => c == &c2,
      Err(err) => { eprintln!("constant_roundtrip error: {err}"); false }
    }
  }

  #[quickcheck]
  fn prop_constant_roundtrip(c: ArbitraryConstant) -> bool {
    constant_roundtrip(&c.0)
  }

  #[test]
  fn constant_tag4_serialization() {
    let defn = gen_definition(&mut Gen::new(10));
    let cnst = Constant::new(ConstantInfo::Defn(defn));
    let mut buf = Vec::new();
    cnst.put(&mut buf);
    assert_eq!(buf[0] >> 4, Constant::FLAG, "Constant should use flag 0xD");
    assert!(constant_roundtrip(&cnst));
  }
}
