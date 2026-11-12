//! Constants in the Ixon format.
//!
//! These are alpha-invariant representations of Lean constants.
//! Metadata (names, binder info) is stored separately in the names map.
//!
//! The sharing vector is stored at the Constant level, shared across
//! all expressions in the constant (including mutual block members).

#![allow(clippy::needless_pass_by_value)]

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::address::Address;
use ix_common::env::{DefinitionSafety, QuotKind};

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
  pub is_unsafe: bool,
  /// Number of universe parameters
  pub lvls: u64,
  /// Number of parameters
  pub params: u64,
  /// Number of indices
  pub indices: u64,
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
  // Constant variant indices (the value of the TagN header)
  // These are 0-7, fitting in 3 bits for single-byte TagN
  // Note: Muts uses a separate flag (0xC), not a variant here
  pub const CONST_DEFN: u64 = 0;
  pub const CONST_RECR: u64 = 1;
  pub const CONST_AXIO: u64 = 2;
  pub const CONST_QUOT: u64 = 3;
  pub const CONST_CPRJ: u64 = 4;
  pub const CONST_RPRJ: u64 = 5;
  pub const CONST_IPRJ: u64 = 6;
  pub const CONST_DPRJ: u64 = 7;

  /// Returns the variant index (the value of the TagN header)
  /// Returns None for Muts (which uses its own flag)
  pub fn variant(&self) -> Option<u64> {
    match self {
      Self::Defn(_) => Some(Self::CONST_DEFN),
      Self::Recr(_) => Some(Self::CONST_RECR),
      Self::Axio(_) => Some(Self::CONST_AXIO),
      Self::Quot(_) => Some(Self::CONST_QUOT),
      Self::CPrj(_) => Some(Self::CONST_CPRJ),
      Self::RPrj(_) => Some(Self::CONST_RPRJ),
      Self::IPrj(_) => Some(Self::CONST_IPRJ),
      Self::DPrj(_) => Some(Self::CONST_DPRJ),
      Self::Muts(_) => None, // Uses FLAG_MUTS, not a variant
    }
  }
}

// ============================================================================
// Binder data
// ============================================================================

/// One numbered node of a binder-data block (`Constant::binders`).
///
/// A binder's datum is the zero-ness of its codomain sort: never zero, or
/// zero exactly when every universe parameter of a set is zero.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinderNode {
  /// A binder whose codomain sort is never zero (wire tag 0).
  Never,
  /// A binder whose codomain sort is always zero (wire tag 1).
  Zero,
  /// A binder whose codomain sort is zero exactly when every listed
  /// universe parameter is (wire tag 2). Canonical: nonempty, strictly
  /// ascending, below the record's level count.
  IfAllZero(Vec<u64>),
  /// A share site whose entry has a binder: that entry at this variant
  /// (wire tag 3).
  Share(u64),
  /// A binder whose datum the compiler could not decide (wire tag 4).
  /// Readers accept it; a checker that needs the datum rejects it.
  Undecided,
}

impl BinderNode {
  pub const TAG_NEVER: u8 = 0;
  pub const TAG_ZERO: u8 = 1;
  pub const TAG_IF_ALL_ZERO: u8 = 2;
  pub const TAG_SHARE: u8 = 3;
  pub const TAG_UNDECIDED: u8 = 4;
}

/// The binder data of one expression of a record: a root (`shared` false,
/// `index` the root's number, `variant` 0) or one variant of a sharing entry
/// (`shared` true, `index` the entry's index). Its nodes follow the
/// expression's numbered nodes (every `Lam` and `All`, and every `Share`
/// whose entry has a binder) in pre-order.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BinderBlock {
  pub shared: bool,
  pub index: u64,
  pub variant: u64,
  pub nodes: Vec<BinderNode>,
}

impl BinderBlock {
  /// The block's key; blocks are strictly sorted by it.
  pub fn key(&self) -> (bool, u64, u64) {
    (self.shared, self.index, self.variant)
  }
}

/// A top-level constant with its sharing, refs, and univs vectors, and its
/// binder-data section.
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
  /// Binder data, blocks strictly sorted by `BinderBlock::key`
  pub binders: Vec<BinderBlock>,
}

impl Constant {
  /// TagN flag used for non-Muts constants (the variant is the value; one byte)
  pub const FLAG: u8 = 0xD;
  /// TagN flag used for Muts constants (the entry count is the value)
  pub const FLAG_MUTS: u8 = 0xC;
  /// The bound on a record's level count (`Ixon.maxLevelCount`): the
  /// canonical check (`binders_canonical`) refuses a record with `2^32`
  /// universe parameters or more, as Lean's canonical decoder and IxVM's
  /// parser do.
  pub const MAX_LEVEL_COUNT: u64 = 1 << 32;

  /// Create a new constant with no sharing, refs, univs or binder data
  pub fn new(info: ConstantInfo) -> Self {
    Constant {
      info,
      sharing: Vec::new(),
      refs: Vec::new(),
      univs: Vec::new(),
      binders: Vec::new(),
    }
  }

  /// Create a new constant with sharing, refs, and univs, and no binder data
  pub fn with_tables(
    info: ConstantInfo,
    sharing: Vec<Arc<Expr>>,
    refs: Vec<Address>,
    univs: Vec<Arc<Univ>>,
  ) -> Self {
    Constant { info, sharing, refs, univs, binders: Vec::new() }
  }

  /// This constant with the binder-data section `binders`.
  pub fn with_binders(mut self, binders: Vec<BinderBlock>) -> Self {
    self.binders = binders;
    self
  }

  /// The level count bounding the binder data's parameters: the largest
  /// level count of the record's members (0 for a projection).
  pub fn max_lvls(&self) -> u64 {
    fn mut_lvls(m: &MutConst) -> u64 {
      match m {
        MutConst::Defn(d) => d.lvls,
        MutConst::Indc(i) => i.lvls,
        MutConst::Recr(r) => r.lvls,
      }
    }
    match &self.info {
      ConstantInfo::Defn(d) => d.lvls,
      ConstantInfo::Recr(r) => r.lvls,
      ConstantInfo::Axio(a) => a.lvls,
      ConstantInfo::Quot(q) => q.lvls,
      ConstantInfo::CPrj(_)
      | ConstantInfo::RPrj(_)
      | ConstantInfo::IPrj(_)
      | ConstantInfo::DPrj(_) => 0,
      ConstantInfo::Muts(ms) => ms.iter().map(mut_lvls).max().unwrap_or(0),
    }
  }

  /// The record's root expressions, in the order its binder-data section
  /// numbers them (`Ixon.ConstantInfo.binderRoots`): a definition's type and
  /// value; an axiom's or quotient's type; a recursor's type and its rules'
  /// right-hand sides; an inductive's type and its constructors' types; a
  /// block's members in order. A projection has none.
  pub fn binder_roots(&self) -> Vec<&Expr> {
    fn member<'a>(m: &'a MutConst, out: &mut Vec<&'a Expr>) {
      match m {
        MutConst::Defn(d) => {
          out.push(d.typ.as_ref());
          out.push(d.value.as_ref());
        },
        MutConst::Indc(i) => {
          out.push(i.typ.as_ref());
          out.extend(i.ctors.iter().map(|c| c.typ.as_ref()));
        },
        MutConst::Recr(r) => {
          out.push(r.typ.as_ref());
          out.extend(r.rules.iter().map(|rule| rule.rhs.as_ref()));
        },
      }
    }
    let mut out = Vec::new();
    match &self.info {
      ConstantInfo::Defn(d) => {
        out.push(d.typ.as_ref());
        out.push(d.value.as_ref());
      },
      ConstantInfo::Recr(r) => {
        out.push(r.typ.as_ref());
        out.extend(r.rules.iter().map(|rule| rule.rhs.as_ref()));
      },
      ConstantInfo::Axio(a) => out.push(a.typ.as_ref()),
      ConstantInfo::Quot(q) => out.push(q.typ.as_ref()),
      ConstantInfo::CPrj(_)
      | ConstantInfo::RPrj(_)
      | ConstantInfo::IPrj(_)
      | ConstantInfo::DPrj(_) => {},
      ConstantInfo::Muts(ms) => ms.iter().for_each(|m| member(m, &mut out)),
    }
    out
  }

  /// Whether the record's constants are unsafe or partial
  /// (`Ixon.ConstantInfo.uncheckedSafety`): their every binder carries the
  /// undecided node.
  pub fn unchecked_safety(&self) -> bool {
    fn defn(d: &Definition) -> bool {
      d.safety != DefinitionSafety::Safe
    }
    match &self.info {
      ConstantInfo::Defn(d) => defn(d),
      ConstantInfo::Recr(r) => r.is_unsafe,
      ConstantInfo::Axio(a) => a.is_unsafe,
      ConstantInfo::Quot(_) => false,
      ConstantInfo::CPrj(_)
      | ConstantInfo::RPrj(_)
      | ConstantInfo::IPrj(_)
      | ConstantInfo::DPrj(_) => false,
      ConstantInfo::Muts(ms) => ms.iter().any(|m| match m {
        MutConst::Defn(d) => defn(d),
        MutConst::Indc(i) => i.is_unsafe,
        MutConst::Recr(r) => r.is_unsafe,
      }),
    }
  }

  /// The binder data are in canonical form (`Ixon.Constant.bindersCanonical`),
  /// the local form every reader checks: the level count (`max_lvls`) below
  /// `MAX_LEVEL_COUNT`, blocks strictly sorted by key, a root block at
  /// variant 0, no empty block, every `IfAllZero` parameter list nonempty,
  /// strictly ascending and below `max_lvls`, and the empty section for a
  /// record with no root (a projection).
  pub fn binders_canonical(&self) -> bool {
    let lvls = self.max_lvls();
    lvls < Self::MAX_LEVEL_COUNT
      && self.binders.windows(2).all(|w| w[0].key() < w[1].key())
      && self.binders.iter().all(|b| {
        (b.shared || b.variant == 0)
          && !b.nodes.is_empty()
          && b.nodes.iter().all(|n| match n {
            BinderNode::IfAllZero(ps) => {
              !ps.is_empty()
                && ps.windows(2).all(|w| w[0] < w[1])
                && ps.iter().all(|p| *p < lvls)
            },
            _ => true,
          })
      })
      && (!self.binder_roots().is_empty() || self.binders.is_empty())
  }

  /// The section is complete (`Ixon.Constant.bindersComplete`): blocks
  /// strictly sorted, exactly one per root with a numbered node (variant 0)
  /// and per sharing entry and variant a share node names, each with one node
  /// per numbered node of its expression and of the matching kind, every
  /// `IfAllZero` list nonempty, strictly ascending and below `max_lvls`, the
  /// variants of an entry numbered in order of first occurrence (roots in
  /// order, each in pre-order, a share node visiting its variant there) and
  /// pairwise distinct.
  pub fn binders_complete(&self) -> bool {
    if self.binder_roots().is_empty() {
      return self.binders.is_empty();
    }
    if !self.binders.windows(2).all(|w| w[0].key() < w[1].key()) {
      return false;
    }
    let lvls = self.max_lvls();
    let full = binderful_entries(&self.sharing);
    let blocks: FxHashMap<(bool, u64, u64), &[BinderNode]> =
      self.binders.iter().map(|b| (b.key(), b.nodes.as_slice())).collect();
    let mut walk = BinderWalk::default();
    let budget = self.binders.len() + 1;
    for (r, root) in self.binder_roots().into_iter().enumerate() {
      let mut shape = Vec::new();
      numbered_nodes(&full, root, &mut shape);
      if shape.is_empty() {
        continue;
      }
      let key = (false, r as u64, 0);
      let Some(nodes) = blocks.get(&key) else { return false };
      walk.visited.insert(key);
      let cx = BinderCheck {
        lvls,
        undecided_only: self.unchecked_safety(),
        full: &full,
        sharing: &self.sharing,
        blocks: &blocks,
      };
      if !cx.check(budget, &shape, nodes, &mut walk) {
        return false;
      }
    }
    if walk.visited.len() != self.binders.len() {
      return false;
    }
    for b in self.binders.iter().filter(|b| b.shared) {
      if self.binders.iter().any(|o| {
        o.shared && o.index == b.index && o.variant < b.variant && o.nodes == b.nodes
      }) {
        return false;
      }
    }
    true
  }
}

/// Whether each sharing entry has a binder, directly or through the entries
/// before it (`Ixon.binderfulEntries`).
fn binderful_entries(sharing: &[Arc<Expr>]) -> Vec<bool> {
  fn has_binder(full: &[bool], e: &Expr) -> bool {
    match e {
      Expr::Lam(..) | Expr::All(..) => true,
      Expr::App(f, a) => has_binder(full, f) || has_binder(full, a),
      Expr::Let(_, t, v, b) => {
        has_binder(full, t) || has_binder(full, v) || has_binder(full, b)
      },
      Expr::Prj(_, _, v) => has_binder(full, v),
      Expr::Share(n) => full.get(*n as usize).copied().unwrap_or(false),
      _ => false,
    }
  }
  let mut full = Vec::with_capacity(sharing.len());
  for e in sharing {
    let flag = has_binder(&full, e);
    full.push(flag);
  }
  full
}

/// The numbered nodes of `e` in pre-order (`Ixon.Expr.numberedNodes`): `None`
/// for a `Lam` or `All`, `Some(n)` for a `Share` of an entry with a binder.
fn numbered_nodes(full: &[bool], e: &Expr, acc: &mut Vec<Option<usize>>) {
  match e {
    Expr::Lam(_, t, b) | Expr::All(_, _, t, b) => {
      acc.push(None);
      numbered_nodes(full, t, acc);
      numbered_nodes(full, b, acc);
    },
    Expr::App(f, a) => {
      numbered_nodes(full, f, acc);
      numbered_nodes(full, a, acc);
    },
    Expr::Let(_, t, v, b) => {
      numbered_nodes(full, t, acc);
      numbered_nodes(full, v, acc);
      numbered_nodes(full, b, acc);
    },
    Expr::Prj(_, _, v) => numbered_nodes(full, v, acc),
    Expr::Share(n) => {
      if full.get(*n as usize).copied().unwrap_or(false) {
        acc.push(Some(*n as usize));
      }
    },
    _ => {},
  }
}

#[derive(Default)]
struct BinderWalk {
  visited: FxHashSet<(bool, u64, u64)>,
  variants: FxHashMap<usize, u64>,
}

struct BinderCheck<'a> {
  lvls: u64,
  undecided_only: bool,
  full: &'a [bool],
  sharing: &'a [Arc<Expr>],
  blocks: &'a FxHashMap<(bool, u64, u64), &'a [BinderNode]>,
}

impl BinderCheck<'_> {
  /// `Ixon.checkBinderNodes`.
  fn check(
    &self,
    fuel: usize,
    shape: &[Option<usize>],
    nodes: &[BinderNode],
    walk: &mut BinderWalk,
  ) -> bool {
    if fuel == 0 || shape.len() != nodes.len() {
      return false;
    }
    for (kind, node) in shape.iter().zip(nodes) {
      match (kind, node) {
        (None, BinderNode::Share(_)) => return false,
        (None, n) if self.undecided_only => {
          if *n != BinderNode::Undecided {
            return false;
          }
        },
        (None, BinderNode::IfAllZero(ps)) => {
          if ps.is_empty()
            || !ps.windows(2).all(|w| w[0] < w[1])
            || !ps.iter().all(|p| *p < self.lvls)
          {
            return false;
          }
        },
        (None, _) => {},
        (Some(n), BinderNode::Share(v)) => {
          let key = (true, *n as u64, *v);
          if walk.visited.contains(&key) {
            continue;
          }
          if *v != walk.variants.get(n).copied().unwrap_or(0) {
            return false;
          }
          let Some(entry) = self.sharing.get(*n) else { return false };
          let Some(sub) = self.blocks.get(&key) else { return false };
          walk.visited.insert(key);
          walk.variants.insert(*n, v + 1);
          let mut sub_shape = Vec::new();
          numbered_nodes(self.full, entry, &mut sub_shape);
          if !self.check(fuel - 1, &sub_shape, sub, walk) {
            return false;
          }
        },
        (Some(_), _) => return false,
      }
    }
    true
  }

}

// ============================================================================
// Canonical projection-address helpers
// ============================================================================
//
// The compile and ingress pipelines independently derive projection
// addresses for members of a mutual block — each member's
// `D/I/R/CPrj` wrapper has a deterministic content hash that becomes
// the kernel's lookup key. Centralizing the wrapper construction +
// `.commit().0` here keeps all callers in lock-step: drift between
// the compile-side address (what gets stored in `env.consts`) and
// the kernel-side address (what `LazyAnonIngress` looks up) is the
// kind of bug that surfaces only on full-env runs and is painful to
// diagnose.

/// Deterministic `DPrj` content address for member `idx` of `block`.
pub fn defn_proj_address(idx: u64, block: &Address) -> Address {
  defn_proj_constant(idx, block.clone()).commit().0
}

/// Deterministic `IPrj` content address for member `idx` of `block`.
pub fn indc_proj_address(idx: u64, block: &Address) -> Address {
  indc_proj_constant(idx, block.clone()).commit().0
}

/// Deterministic `RPrj` content address for member `idx` of `block`.
pub fn recr_proj_address(idx: u64, block: &Address) -> Address {
  recr_proj_constant(idx, block.clone()).commit().0
}

/// Deterministic `CPrj` content address for ctor `(idx, cidx)` of `block`.
pub fn ctor_proj_address(idx: u64, cidx: u64, block: &Address) -> Address {
  ctor_proj_constant(idx, cidx, block.clone()).commit().0
}

/// Canonical `DPrj` `Constant` for member `idx` of `block`. Use this
/// (rather than ad-hoc `Constant::new(ConstantInfo::DPrj { ... })`)
/// so all callers share one construction path.
pub fn defn_proj_constant(idx: u64, block: Address) -> Constant {
  Constant::new(ConstantInfo::DPrj(DefinitionProj { idx, block }))
}

/// Canonical `IPrj` `Constant` for member `idx` of `block`.
pub fn indc_proj_constant(idx: u64, block: Address) -> Constant {
  Constant::new(ConstantInfo::IPrj(InductiveProj { idx, block }))
}

/// Canonical `RPrj` `Constant` for member `idx` of `block`.
pub fn recr_proj_constant(idx: u64, block: Address) -> Constant {
  Constant::new(ConstantInfo::RPrj(RecursorProj { idx, block }))
}

/// Canonical `CPrj` `Constant` for ctor `(idx, cidx)` of `block`.
pub fn ctor_proj_constant(idx: u64, cidx: u64, block: Address) -> Constant {
  Constant::new(ConstantInfo::CPrj(ConstructorProj { idx, cidx, block }))
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::expr::tests::arbitrary_expr;
  use crate::tests::gen_range;
  use ix_common::env::{DefinitionSafety, QuotKind};
  use quickcheck::{Arbitrary, Gen};
  use quickcheck_macros::quickcheck;

  impl Arbitrary for DefKind {
    fn arbitrary(g: &mut Gen) -> Self {
      match u8::arbitrary(g) % 3 {
        0 => DefKind::Definition,
        1 => DefKind::Opaque,
        _ => DefKind::Theorem,
      }
    }
  }

  pub fn gen_sharing(g: &mut Gen) -> Vec<Arc<Expr>> {
    (0..gen_range(g, 0..4)).map(|_| arbitrary_expr(g)).collect()
  }

  pub fn gen_refs(g: &mut Gen) -> Vec<Address> {
    (0..gen_range(g, 0..4)).map(|_| Address::arbitrary(g)).collect()
  }

  pub fn gen_univs(g: &mut Gen) -> Vec<Arc<Univ>> {
    use crate::univ::tests::arbitrary_univ;
    (0..gen_range(g, 0..4)).map(|_| arbitrary_univ(g)).collect()
  }

  pub fn gen_definition(g: &mut Gen) -> Definition {
    Definition {
      kind: DefKind::arbitrary(g),
      safety: DefinitionSafety::arbitrary(g),
      lvls: u64::arbitrary(g) % 10,
      typ: arbitrary_expr(g),
      value: arbitrary_expr(g),
    }
  }

  fn gen_recursor_rule(g: &mut Gen) -> RecursorRule {
    RecursorRule { fields: u64::arbitrary(g) % 10, rhs: arbitrary_expr(g) }
  }

  pub fn gen_recursor(g: &mut Gen) -> Recursor {
    Recursor {
      k: bool::arbitrary(g),
      is_unsafe: bool::arbitrary(g),
      lvls: u64::arbitrary(g) % 10,
      params: u64::arbitrary(g) % 10,
      indices: u64::arbitrary(g) % 5,
      motives: u64::arbitrary(g) % 3,
      minors: u64::arbitrary(g) % 10,
      typ: arbitrary_expr(g),
      rules: (0..gen_range(g, 0..5)).map(|_| gen_recursor_rule(g)).collect(),
    }
  }

  pub fn gen_axiom(g: &mut Gen) -> Axiom {
    Axiom {
      is_unsafe: bool::arbitrary(g),
      lvls: u64::arbitrary(g) % 10,
      typ: arbitrary_expr(g),
    }
  }

  pub fn gen_quotient(g: &mut Gen) -> Quotient {
    Quotient {
      kind: QuotKind::arbitrary(g),
      lvls: u64::arbitrary(g) % 10,
      typ: arbitrary_expr(g),
    }
  }

  fn gen_constructor(g: &mut Gen) -> Constructor {
    Constructor {
      is_unsafe: bool::arbitrary(g),
      lvls: u64::arbitrary(g) % 10,
      cidx: u64::arbitrary(g) % 10,
      params: u64::arbitrary(g) % 10,
      fields: u64::arbitrary(g) % 10,
      typ: arbitrary_expr(g),
    }
  }

  pub fn gen_inductive(g: &mut Gen) -> Inductive {
    Inductive {
      is_unsafe: bool::arbitrary(g),
      lvls: u64::arbitrary(g) % 10,
      params: u64::arbitrary(g) % 10,
      indices: u64::arbitrary(g) % 5,
      typ: arbitrary_expr(g),
      ctors: (0..gen_range(g, 0..4)).map(|_| gen_constructor(g)).collect(),
    }
  }

  fn gen_mut_const(g: &mut Gen) -> MutConst {
    match u8::arbitrary(g) % 3 {
      0 => MutConst::Defn(gen_definition(g)),
      1 => MutConst::Indc(gen_inductive(g)),
      _ => MutConst::Recr(gen_recursor(g)),
    }
  }

  fn gen_constant_info(g: &mut Gen) -> ConstantInfo {
    match u8::arbitrary(g) % 9 {
      0 => ConstantInfo::Defn(gen_definition(g)),
      1 => ConstantInfo::Recr(gen_recursor(g)),
      2 => ConstantInfo::Axio(gen_axiom(g)),
      3 => ConstantInfo::Quot(gen_quotient(g)),
      4 => ConstantInfo::CPrj(ConstructorProj {
        idx: u64::arbitrary(g) % 10,
        cidx: u64::arbitrary(g) % 10,
        block: Address::arbitrary(g),
      }),
      5 => ConstantInfo::RPrj(RecursorProj {
        idx: u64::arbitrary(g) % 10,
        block: Address::arbitrary(g),
      }),
      6 => ConstantInfo::IPrj(InductiveProj {
        idx: u64::arbitrary(g) % 10,
        block: Address::arbitrary(g),
      }),
      7 => ConstantInfo::DPrj(DefinitionProj {
        idx: u64::arbitrary(g) % 10,
        block: Address::arbitrary(g),
      }),
      _ => ConstantInfo::Muts(
        (0..gen_range(g, 1..4)).map(|_| gen_mut_const(g)).collect(),
      ),
    }
  }

  pub fn gen_binder_node(g: &mut Gen) -> BinderNode {
    match u8::arbitrary(g) % 5 {
      0 => BinderNode::Never,
      1 => BinderNode::Zero,
      2 => BinderNode::IfAllZero(
        (0..gen_range(g, 0..4)).map(|_| u64::arbitrary(g)).collect(),
      ),
      3 => BinderNode::Share(u64::arbitrary(g)),
      _ => BinderNode::Undecided,
    }
  }

  /// Arbitrary sections: neither sorted nor canonical, which the codec
  /// round-trips all the same.
  pub fn gen_binders(g: &mut Gen) -> Vec<BinderBlock> {
    (0..gen_range(g, 0..3))
      .map(|_| BinderBlock {
        shared: bool::arbitrary(g),
        index: u64::arbitrary(g),
        variant: u64::arbitrary(g),
        nodes: (0..gen_range(g, 0..5)).map(|_| gen_binder_node(g)).collect(),
      })
      .collect()
  }

  pub fn gen_constant(g: &mut Gen) -> Constant {
    Constant {
      info: gen_constant_info(g),
      sharing: gen_sharing(g),
      refs: gen_refs(g),
      univs: gen_univs(g),
      binders: gen_binders(g),
    }
  }

  #[derive(Clone, Debug)]
  struct ArbitraryConstant(Constant);

  impl Arbitrary for ArbitraryConstant {
    fn arbitrary(g: &mut Gen) -> Self {
      ArbitraryConstant(gen_constant(g))
    }
  }

  fn constant_roundtrip(c: &Constant) -> bool {
    let mut buf = Vec::new();
    c.put(&mut buf);
    match Constant::get(&mut buf.as_slice()) {
      Ok(c2) => c == &c2,
      Err(err) => {
        eprintln!("constant_roundtrip error: {err}");
        false
      },
    }
  }

  #[quickcheck]
  fn prop_constant_roundtrip(c: ArbitraryConstant) -> bool {
    constant_roundtrip(&c.0)
  }

  #[test]
  fn constant_tagn_serialization() {
    let defn = gen_definition(&mut Gen::new(10));
    let cnst = Constant::new(ConstantInfo::Defn(defn));
    let mut buf = Vec::new();
    cnst.put(&mut buf);
    assert_eq!(buf[0] >> 4, Constant::FLAG, "Constant should use flag 0xD");
    assert!(constant_roundtrip(&cnst));
  }

  /// A universe-polymorphic definition `fun (x : Sort u) => x` with a
  /// sharing entry, carrying a section with every node kind: a root block,
  /// two variants of a sharing entry, a share node and the sentinel.
  fn binder_fixture() -> Constant {
    let typ = Expr::all(Expr::sort(0), Expr::share(0));
    let value = Expr::lam(Expr::sort(0), Expr::share(0));
    let defn = Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 3,
      typ,
      value,
    };
    Constant::with_tables(
      ConstantInfo::Defn(defn),
      vec![Expr::lam(Expr::sort(0), Expr::var(0))],
      vec![],
      vec![Arc::new(Univ::Var(0))],
    )
    .with_binders(vec![
      BinderBlock {
        shared: false,
        index: 0,
        variant: 0,
        nodes: vec![BinderNode::IfAllZero(vec![0, 2]), BinderNode::Share(0)],
      },
      BinderBlock {
        shared: false,
        index: 1,
        variant: 0,
        nodes: vec![BinderNode::Never, BinderNode::Share(1)],
      },
      BinderBlock {
        shared: true,
        index: 0,
        variant: 0,
        nodes: vec![BinderNode::Zero],
      },
      BinderBlock {
        shared: true,
        index: 0,
        variant: 1,
        nodes: vec![BinderNode::Undecided],
      },
    ])
  }

  #[test]
  fn binders_section_bytes() {
    // The empty section is one byte, 0x00, after the univs table.
    let empty = Constant::new(ConstantInfo::DPrj(DefinitionProj {
      idx: 0,
      block: Address::hash(b"block"),
    }));
    let mut buf = Vec::new();
    empty.put(&mut buf);
    assert_eq!(buf[buf.len() - 4..], [0, 0, 0, 0], "sharing, refs, univs, binders");
    assert!(constant_roundtrip(&empty));
    assert!(empty.binders_canonical());

    let c = binder_fixture();
    let mut section = Vec::new();
    crate::serialize::put_binders(&c.binders, &mut section);
    assert_eq!(
      section,
      vec![
        4, // four blocks
        0, 0, 0, 2, 2, 2, 0, 2, 3, 0, // root 0: ifAllZero [0, 2], share 0
        0, 1, 0, 2, 0, 3, 1, // root 1: never, share 1
        1, 0, 0, 1, 1, // entry 0, variant 0: zero
        1, 0, 1, 1, 4, // entry 0, variant 1: undecided
      ]
    );
    let mut full = Vec::new();
    c.put(&mut full);
    assert!(full.ends_with(&section));
    assert!(constant_roundtrip(&c));
    assert!(c.binders_canonical());
  }

  #[test]
  fn binders_noncanonical_forms() {
    let base = binder_fixture();
    let with = |f: &dyn Fn(&mut Vec<BinderBlock>)| {
      let mut c = base.clone();
      f(&mut c.binders);
      c
    };
    // Every form below still round-trips; only the canonical form rejects it.
    let block = |shared, index, variant, nodes: Vec<BinderNode>| BinderBlock {
      shared,
      index,
      variant,
      nodes,
    };
    let cases = [
      with(&|b| b.swap(0, 1)),                 // blocks out of order
      with(&|b| b.push(b[3].clone())),         // a repeated key
      with(&|b| b[1].variant = 1),             // a root block at variant 1
      with(&|b| b[0].nodes[0] = BinderNode::IfAllZero(vec![])), // empty list
      with(&|b| b[0].nodes[0] = BinderNode::IfAllZero(vec![2, 0])), // descending
      with(&|b| b[0].nodes[0] = BinderNode::IfAllZero(vec![1, 1])), // repeated
      with(&|b| b[0].nodes[0] = BinderNode::IfAllZero(vec![3])), // not below lvls
      with(&|b| b.push(block(true, 0, 2, vec![]))), // an empty block
    ];
    for c in &cases {
      assert!(constant_roundtrip(c));
      assert!(!c.binders_canonical(), "{:?}", c.binders);
    }
    // Canonical (local) and round-tripping; only the complete form rejects them.
    let incomplete = [
      with(&|b| b.push(block(true, 0, 2, vec![BinderNode::Never]))), // a dead variant
      with(&|b| {
        b.remove(1);
      }), // a missing root block
      with(&|b| {
        b.remove(3);
      }), // a missing variant
      with(&|b| {
        b[0].nodes[1] = BinderNode::Share(1);
        b[1].nodes[1] = BinderNode::Share(0);
      }), // variants out of first-occurrence order
      with(&|b| b[3].nodes = vec![BinderNode::Zero]), // two equal variants
      with(&|b| b[2].nodes = vec![BinderNode::Share(0)]), // a share node at a binder
      with(&|b| b[0].nodes[1] = BinderNode::Never), // a binder node at a share
      with(&|b| b[2].nodes = vec![BinderNode::Zero, BinderNode::Zero]), // a node too many
      with(&|b| b.push(block(true, 1, 0, vec![BinderNode::Never]))), // no such entry
      with(&|b| b.clear()),                    // a record with binders and no section
    ];
    for c in &incomplete {
      assert!(constant_roundtrip(c));
      assert!(c.binders_canonical(), "{:?}", c.binders);
      assert!(!c.binders_complete(), "{:?}", c.binders);
    }
    assert!(base.binders_complete());
    // A projection carries no binder data: any section is noncanonical.
    for node in [BinderNode::IfAllZero(vec![0]), BinderNode::Never] {
      let prj = Constant::new(ConstantInfo::DPrj(DefinitionProj {
        idx: 0,
        block: Address::hash(b"block"),
      }))
      .with_binders(vec![block(false, 0, 0, vec![node])]);
      assert!(!prj.binders_canonical());
    }
  }

  #[test]
  fn level_count_bound() {
    // The wire carries any u64 level count; the canonical check refuses
    // 2^32 or more, for a record and for a block member alike.
    for (lvls, canonical) in [
      (0u64, true),
      (1, true),
      (Constant::MAX_LEVEL_COUNT - 1, true),
      (Constant::MAX_LEVEL_COUNT, false),
      ((1 << 56) - 1, false),
      (1 << 56, false),
      (u64::MAX, false),
    ] {
      let axiom = Constant::with_tables(
        ConstantInfo::Axio(Axiom { is_unsafe: true, lvls, typ: Expr::sort(0) }),
        vec![],
        vec![],
        vec![Arc::new(Univ::Zero)],
      );
      assert!(constant_roundtrip(&axiom));
      assert_eq!(
        axiom.binders_canonical(),
        canonical,
        "axiom with {lvls} levels"
      );
      let member = Definition {
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        lvls,
        typ: Expr::sort(0),
        value: Expr::sort(0),
      };
      let block = Constant::with_tables(
        ConstantInfo::Muts(vec![MutConst::Defn(member)]),
        vec![],
        vec![],
        vec![Arc::new(Univ::Zero)],
      );
      assert!(constant_roundtrip(&block));
      assert_eq!(
        block.binders_canonical(),
        canonical,
        "block member with {lvls} levels"
      );
    }
  }

  #[test]
  fn binders_reader_rejects_bad_tags() {
    let c = binder_fixture();
    let mut buf = Vec::new();
    c.put(&mut buf);
    let section_start = buf.len() - 28;
    // An unknown node tag.
    let mut bad = buf.clone();
    bad[section_start + 5] = 5;
    assert!(Constant::get(&mut bad.as_slice()).is_err());
    // A block kind other than 0 or 1.
    let mut bad = buf.clone();
    bad[section_start + 1] = 2;
    assert!(Constant::get(&mut bad.as_slice()).is_err());
    // A truncated section.
    assert!(Constant::get(&mut &buf[..buf.len() - 1]).is_err());
    // A record without its section (Ixon v4 bytes).
    let empty = Constant::new(ConstantInfo::Muts(vec![]));
    let mut v5 = Vec::new();
    empty.put(&mut v5);
    assert!(Constant::get(&mut &v5[..v5.len() - 1]).is_err());
  }
}
