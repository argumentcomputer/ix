//! Kernel-specific types for Kernel2.
//!
//! These types mirror `Ix.Kernel.Types` from Lean: they use `Address` for
//! constant references and positional indices for level parameters, unlike
//! the `env` module's `Name`-based types.
//!
//! Types are parameterized by `MetaMode`: in `Meta` mode, metadata fields
//! (names, binder info) are preserved; in `Anon` mode, they become `()`
//! for cache-friendly sharing.
//!
//! # Mutual blocks: Lean vs Ixon (canonical)
//!
//! Lean's kernel stores an `all` field on definitions, theorems, opaques,
//! inductives, and recursors listing the constants in the same "mutual block".
//! This field is **non-canonical**: it reflects source order from the Lean
//! compiler and is NOT alpha-invariant.
//!
//! Ixon recomputes canonical mutual blocks via:
//! 1. Building a reference graph (`src/ix/graph.rs`)
//! 2. Condensing via Tarjan's SCC (`src/ix/condense.rs`)
//! 3. Sorting canonically with partition refinement (`src/ix/compile.rs`)
//!
//! **Key distinction**: inductives reference their constructors (bidirectional),
//! but recursors only reference constructors one-way. So recursors and
//! inductives end up in **separate** canonical blocks.
//!
//! In our kernel types:
//! - `lean_all: M::Field<Vec<MetaId<M>>>` — Lean's non-canonical metadata,
//!   erased in anonymous mode. Used only for roundtripping back to Lean.
//! - `induct_block: Vec<MetaId<M>>` (on recursors) — the canonical inductive
//!   block associated with this recursor. Always present. Used by the
//!   typechecker for nested inductive detection.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc as Rc;

use rustc_hash::FxHashMap;

use crate::ix::address::Address;
pub use crate::ix::env::{
  BinderInfo, DataValue, DefinitionSafety, Literal, Name, QuotKind,
  ReducibilityHints,
};
use super::helpers::lift_bvars;

// ============================================================================
// Blake3 hashing utilities for kernel types
// ============================================================================

/// Combine two blake3 hashes into a new one.
/// Uses single-buffer blake3::hash() for speed (avoids Hasher object overhead).
#[inline]
pub fn combine_hashes(a: &blake3::Hash, b: &blake3::Hash) -> blake3::Hash {
  let mut buf = [0u8; 64];
  buf[..32].copy_from_slice(a.as_bytes());
  buf[32..].copy_from_slice(b.as_bytes());
  blake3::hash(&buf)
}

/// Hash a tag byte + one blake3 hash.
#[inline]
pub fn hash_tag1(tag: u8, a: &blake3::Hash) -> blake3::Hash {
  let mut buf = [0u8; 33];
  buf[0] = tag;
  buf[1..33].copy_from_slice(a.as_bytes());
  blake3::hash(&buf)
}

/// Hash a tag byte + two blake3 hashes.
#[inline]
pub fn hash_tag2(tag: u8, a: &blake3::Hash, b: &blake3::Hash) -> blake3::Hash {
  let mut buf = [0u8; 65];
  buf[0] = tag;
  buf[1..33].copy_from_slice(a.as_bytes());
  buf[33..65].copy_from_slice(b.as_bytes());
  blake3::hash(&buf)
}

/// Hash a tag byte + three blake3 hashes.
#[inline]
pub fn hash_tag3(tag: u8, a: &blake3::Hash, b: &blake3::Hash, c: &blake3::Hash) -> blake3::Hash {
  let mut buf = [0u8; 97];
  buf[0] = tag;
  buf[1..33].copy_from_slice(a.as_bytes());
  buf[33..65].copy_from_slice(b.as_bytes());
  buf[65..97].copy_from_slice(c.as_bytes());
  blake3::hash(&buf)
}

/// Compute blake3 hash from KLevelData (used at construction time, only called when hashing enabled).
fn hash_level_data<M: MetaMode>(data: &KLevelData<M>) -> blake3::Hash {
  // Safe: only called inside mk_hash closures where hashing is enabled
  fn lh<M2: MetaMode>(l: &KLevel<M2>) -> &blake3::Hash { M2::as_blake3(l.blake3_hash()).unwrap() }
  match data {
    KLevelData::Zero => blake3::hash(&[0]),
    KLevelData::Succ(l) => hash_tag1(1, lh(l)),
    KLevelData::Max(a, b) => hash_tag2(2, lh(a), lh(b)),
    KLevelData::IMax(a, b) => hash_tag2(3, lh(a), lh(b)),
    KLevelData::Param(idx, _) => {
      let mut buf = [0u8; 9];
      buf[0] = 4;
      buf[1..9].copy_from_slice(&idx.to_le_bytes());
      blake3::hash(&buf)
    }
  }
}

/// Get the cached blake3 hash of a KLevel. Only valid when hashing is enabled.
pub fn hash_level<M: MetaMode>(level: &KLevel<M>) -> blake3::Hash {
  *M::as_blake3(level.blake3_hash()).expect("hash_level called with hashing disabled")
}

/// Compute blake3 hash of a slice of KLevels. Only valid when hashing is enabled.
pub fn hash_levels<M: MetaMode>(levels: &[KLevel<M>]) -> blake3::Hash {
  if levels.is_empty() {
    return blake3::hash(&[5]);
  }
  let mut buf = vec![5u8]; // tag
  for level in levels {
    buf.extend_from_slice(M::as_blake3(level.blake3_hash()).unwrap().as_bytes());
  }
  blake3::hash(&buf)
}

/// Compute blake3 hash of a Literal.
pub fn hash_literal(lit: &Literal) -> blake3::Hash {
  match lit {
    Literal::NatVal(n) => {
      let bytes = n.0.to_bytes_le();
      let mut buf = vec![0u8; 1 + bytes.len()];
      buf[0] = 0;
      buf[1..].copy_from_slice(&bytes);
      blake3::hash(&buf)
    }
    Literal::StrVal(s) => {
      let mut buf = vec![0u8; 1 + s.len()];
      buf[0] = 1;
      buf[1..].copy_from_slice(s.as_bytes());
      blake3::hash(&buf)
    }
  }
}

// ============================================================================
// MetaMode — const-generic kernel mode parameterization
// ============================================================================

/// Trait for parameterizing kernel type fields.
///
/// Controls two axes via const generics on `KMode<NAMES, HASH>`:
/// - **NAMES**: when true, metadata fields (names, binder info) are preserved.
///   When false, they become `()` for cache-friendly sharing.
/// - **HASH**: when true, blake3 hash fields are computed and stored (32 bytes).
///   When false, they become `()` (ZST, zero bytes, zero cost).
pub trait MetaMode: 'static + Clone + Default + fmt::Debug + Send + Sync {
  type Field<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync + Send + Sync>:
    Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync;
  type HashVal: Clone + fmt::Debug + Send + Sync;

  fn mk_field<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync + Send + Sync>(
    val: T,
  ) -> Self::Field<T>;
  /// Access a metadata field's value. Returns `Some` in named mode,
  /// `None` in anonymous mode where metadata is erased.
  fn field_ref<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync + Send + Sync>(
    field: &Self::Field<T>,
  ) -> Option<&T>;
  fn mk_hash(f: impl FnOnce() -> blake3::Hash) -> Self::HashVal;
  fn as_blake3(h: &Self::HashVal) -> Option<&blake3::Hash>;
}

/// Const-generic kernel mode. `NAMES` controls metadata fields,
/// `HASH` controls blake3 hash fields.
#[derive(Clone, Default, Debug)]
pub struct KMode<const NAMES: bool, const HASH: bool>;

// Convenient aliases
/// Full metadata + blake3 hashing (default for type checking).
pub type Meta = KMode<true, true>;
/// Full metadata, no hashing (for benchmarking hash overhead).
pub type MetaNoHash = KMode<true, false>;
/// Anonymous mode: no metadata, no hashing.
pub type Anon = KMode<false, false>;
/// Anonymous mode with hashing.
pub type AnonHash = KMode<false, true>;

// -- Helper traits for mapping const bools to types -------------------------

pub trait FieldSelector<const B: bool> {
  type Out<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>:
    Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync;
  fn mk<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    val: T,
  ) -> Self::Out<T>;
  fn as_ref<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    field: &Self::Out<T>,
  ) -> Option<&T>;
}

impl FieldSelector<true> for () {
  type Out<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync> = T;
  fn mk<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    val: T,
  ) -> T {
    val
  }
  fn as_ref<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    field: &T,
  ) -> Option<&T> {
    Some(field)
  }
}

impl FieldSelector<false> for () {
  type Out<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync> = ();
  fn mk<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    _: T,
  ) -> () {
  }
  fn as_ref<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    _: &(),
  ) -> Option<&T> {
    None
  }
}

pub trait HashSelector<const B: bool> {
  type Out: Clone + fmt::Debug + Send + Sync;
  fn mk_hash(f: impl FnOnce() -> blake3::Hash) -> Self::Out;
  fn as_blake3(h: &Self::Out) -> Option<&blake3::Hash>;
}

impl HashSelector<true> for () {
  type Out = blake3::Hash;
  fn mk_hash(f: impl FnOnce() -> blake3::Hash) -> blake3::Hash {
    f()
  }
  fn as_blake3(h: &blake3::Hash) -> Option<&blake3::Hash> {
    Some(h)
  }
}

impl HashSelector<false> for () {
  type Out = ();
  fn mk_hash(_: impl FnOnce() -> blake3::Hash) {}
  fn as_blake3(_: &()) -> Option<&blake3::Hash> {
    None
  }
}

// Single blanket impl for all KMode combinations
impl<const N: bool, const H: bool> MetaMode for KMode<N, H>
where
  (): FieldSelector<N> + HashSelector<H>,
{
  type Field<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync> =
    <() as FieldSelector<N>>::Out<T>;
  type HashVal = <() as HashSelector<H>>::Out;

  fn mk_field<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    val: T,
  ) -> Self::Field<T> {
    <() as FieldSelector<N>>::mk(val)
  }
  fn field_ref<T: Default + PartialEq + Clone + fmt::Debug + Hash + Send + Sync>(
    field: &Self::Field<T>,
  ) -> Option<&T> {
    <() as FieldSelector<N>>::as_ref(field)
  }
  fn mk_hash(f: impl FnOnce() -> blake3::Hash) -> Self::HashVal {
    <() as HashSelector<H>>::mk_hash(f)
  }
  fn as_blake3(h: &Self::HashVal) -> Option<&blake3::Hash> {
    <() as HashSelector<H>>::as_blake3(h)
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
/// Carries a cached blake3 hash for O(1) structural fingerprinting.
#[derive(Clone, Debug)]
pub struct KLevel<M: MetaMode>(Rc<KLevelNode<M>>);

/// Internal node wrapping hash + data for KLevel.
#[derive(Debug)]
struct KLevelNode<M: MetaMode> {
  hash: M::HashVal,
  data: KLevelData<M>,
}

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
  /// Construct a KLevel from data, computing the blake3 hash if M::HashVal is active.
  fn from_data(data: KLevelData<M>) -> Self {
    let hash = M::mk_hash(|| hash_level_data(&data));
    KLevel(Rc::new(KLevelNode { hash, data }))
  }

  pub fn zero() -> Self {
    Self::from_data(KLevelData::Zero)
  }

  pub fn succ(l: KLevel<M>) -> Self {
    Self::from_data(KLevelData::Succ(l))
  }

  pub fn max(l: KLevel<M>, r: KLevel<M>) -> Self {
    Self::from_data(KLevelData::Max(l, r))
  }

  pub fn imax(l: KLevel<M>, r: KLevel<M>) -> Self {
    Self::from_data(KLevelData::IMax(l, r))
  }

  pub fn param(idx: usize, name: M::Field<Name>) -> Self {
    Self::from_data(KLevelData::Param(idx, name))
  }

  pub fn data(&self) -> &KLevelData<M> {
    &self.0.data
  }

  /// Returns the cached hash value.
  pub fn blake3_hash(&self) -> &M::HashVal {
    &self.0.hash
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
/// Carries a cached blake3 hash for O(1) structural fingerprinting.
#[derive(Clone, Debug)]
pub struct KExpr<M: MetaMode>(Rc<KExprNode<M>>);

/// A single mdata layer: key-value pairs from Lean's `Expr.mdata`.
pub type KMData = Vec<(Name, DataValue)>;

/// Internal node wrapping hash + data for KExpr.
#[derive(Debug)]
struct KExprNode<M: MetaMode> {
  hash: M::HashVal,
  data: KExprData<M>,
  /// Flattened mdata layers. `MData(kv1, MData(kv2, inner))` becomes
  /// `inner` with `mdata = [kv1, kv2]`. Empty for most expressions.
  /// Not behind MetaField because DataValue doesn't impl Hash.
  mdata: Vec<KMData>,
}

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
  /// Let binding: type, value, body, binder name, non-dep flag.
  LetE(KExpr<M>, KExpr<M>, KExpr<M>, M::Field<Name>, bool),
  /// Literal value (nat or string).
  Lit(Literal),
  /// Projection: type MetaId, field index, struct expr.
  Proj(MetaId<M>, usize, KExpr<M>),
}

impl<M: MetaMode> KExpr<M> {
  /// Construct a KExpr from data, computing the blake3 hash if enabled.
  fn from_data(data: KExprData<M>) -> Self {
    let hash = M::mk_hash(|| Self::compute_hash(&data));
    KExpr(Rc::new(KExprNode { hash, data, mdata: vec![] }))
  }

  /// Construct a KExpr with mdata layers attached.
  pub fn with_mdata(data: KExprData<M>, mdata: Vec<KMData>) -> Self {
    let hash = M::mk_hash(|| Self::compute_hash(&data));
    KExpr(Rc::new(KExprNode { hash, data, mdata }))
  }

  /// Get the mdata layers on this expression.
  pub fn mdata_layers(&self) -> &[KMData] {
    &self.0.mdata
  }

  /// Return a new KExpr with additional mdata layers prepended.
  /// The underlying data and hash are preserved (mdata is semantically transparent).
  pub fn add_mdata(self, mut layers: Vec<KMData>) -> Self {
    if layers.is_empty() {
      return self;
    }
    // Combine with any existing mdata on the inner node
    layers.extend_from_slice(&self.0.mdata);
    KExpr(Rc::new(KExprNode {
      hash: self.0.hash.clone(),
      data: self.data_owned(),
      mdata: layers,
    }))
  }

  /// Clone the underlying KExprData. Required for restructuring nodes.
  fn data_owned(&self) -> KExprData<M> {
    match self.data() {
      KExprData::BVar(i, n) => KExprData::BVar(*i, n.clone()),
      KExprData::Sort(l) => KExprData::Sort(l.clone()),
      KExprData::Const(id, ls) => KExprData::Const(id.clone(), ls.clone()),
      KExprData::App(f, a) => KExprData::App(f.clone(), a.clone()),
      KExprData::Lam(t, b, n, bi) => KExprData::Lam(t.clone(), b.clone(), n.clone(), bi.clone()),
      KExprData::ForallE(t, b, n, bi) => KExprData::ForallE(t.clone(), b.clone(), n.clone(), bi.clone()),
      KExprData::LetE(t, v, b, n, nd) => KExprData::LetE(t.clone(), v.clone(), b.clone(), n.clone(), *nd),
      KExprData::Lit(l) => KExprData::Lit(l.clone()),
      KExprData::Proj(id, i, s) => KExprData::Proj(id.clone(), *i, s.clone()),
    }
  }

  /// Compute blake3 hash of a KExprData node (only called when hashing enabled).
  fn compute_hash(data: &KExprData<M>) -> blake3::Hash {
    fn eh<M2: MetaMode>(e: &KExpr<M2>) -> &blake3::Hash { M2::as_blake3(e.blake3_hash()).unwrap() }
    match data {
      KExprData::BVar(idx, _) => {
        let mut buf = [0u8; 9];
        buf[0] = 0;
        buf[1..9].copy_from_slice(&idx.to_le_bytes());
        blake3::hash(&buf)
      }
      KExprData::Sort(level) => hash_tag1(1, M::as_blake3(level.blake3_hash()).unwrap()),
      KExprData::Const(id, levels) => {
        let lh = hash_levels(levels);
        let mut buf = [0u8; 65];
        buf[0] = 2;
        buf[1..33].copy_from_slice(id.addr.as_bytes());
        buf[33..65].copy_from_slice(lh.as_bytes());
        blake3::hash(&buf)
      }
      KExprData::App(f, a) => hash_tag2(3, eh(f), eh(a)),
      KExprData::Lam(ty, body, _, _) => hash_tag2(4, eh(ty), eh(body)),
      KExprData::ForallE(ty, body, _, _) => hash_tag2(5, eh(ty), eh(body)),
      KExprData::LetE(ty, val, body, _, _) => hash_tag3(6, eh(ty), eh(val), eh(body)),
      KExprData::Lit(lit) => hash_tag1(7, &hash_literal(lit)),
      KExprData::Proj(id, idx, strct) => {
        let mut buf = [0u8; 73];
        buf[0] = 8;
        buf[1..33].copy_from_slice(id.addr.as_bytes());
        buf[33..41].copy_from_slice(&idx.to_le_bytes());
        buf[41..73].copy_from_slice(eh(strct).as_bytes());
        blake3::hash(&buf)
      }
    }
  }

  pub fn data(&self) -> &KExprData<M> {
    &self.0.data
  }

  /// Returns the cached hash value.
  pub fn blake3_hash(&self) -> &M::HashVal {
    &self.0.hash
  }

  /// Returns the pointer identity for caching.
  pub fn ptr_id(&self) -> usize {
    Rc::as_ptr(&self.0) as usize
  }

  // Smart constructors

  pub fn bvar(idx: usize, name: M::Field<Name>) -> Self {
    Self::from_data(KExprData::BVar(idx, name))
  }

  pub fn sort(level: KLevel<M>) -> Self {
    Self::from_data(KExprData::Sort(level))
  }

  pub fn cnst(
    id: MetaId<M>,
    levels: Vec<KLevel<M>>,
  ) -> Self {
    Self::from_data(KExprData::Const(id, levels))
  }

  pub fn app(f: KExpr<M>, a: KExpr<M>) -> Self {
    Self::from_data(KExprData::App(f, a))
  }

  pub fn lam(
    ty: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
  ) -> Self {
    Self::from_data(KExprData::Lam(ty, body, name, bi))
  }

  pub fn forall_e(
    ty: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
    bi: M::Field<BinderInfo>,
  ) -> Self {
    Self::from_data(KExprData::ForallE(ty, body, name, bi))
  }

  pub fn let_e(
    ty: KExpr<M>,
    val: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
  ) -> Self {
    Self::from_data(KExprData::LetE(ty, val, body, name, true))
  }

  pub fn let_e_nd(
    ty: KExpr<M>,
    val: KExpr<M>,
    body: KExpr<M>,
    name: M::Field<Name>,
    non_dep: bool,
  ) -> Self {
    Self::from_data(KExprData::LetE(ty, val, body, name, non_dep))
  }

  pub fn lit(l: Literal) -> Self {
    Self::from_data(KExprData::Lit(l))
  }

  pub fn proj(
    type_id: MetaId<M>,
    idx: usize,
    strct: KExpr<M>,
  ) -> Self {
    Self::from_data(KExprData::Proj(type_id, idx, strct))
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
        KExprData::LetE(t1, v1, b1, _, _),
        KExprData::LetE(t2, v2, b2, _, _),
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
    if let Some(h) = M::as_blake3(self.blake3_hash()) {
      // Use cached blake3 digest for fast hashing
      state.write(h.as_bytes());
    } else {
      // Fall back to structural hashing when blake3 is disabled
      std::mem::discriminant(self.data()).hash(state);
      match self.data() {
        KExprData::BVar(idx, _) => idx.hash(state),
        KExprData::Sort(l) => l.hash(state),
        KExprData::Const(id, levels) => {
          id.addr.hash(state);
          levels.hash(state);
        }
        KExprData::App(f, a) => { f.hash(state); a.hash(state); }
        KExprData::Lam(t, b, _, _) | KExprData::ForallE(t, b, _, _) => {
          t.hash(state); b.hash(state);
        }
        KExprData::LetE(t, v, b, _, _) => { t.hash(state); v.hash(state); b.hash(state); }
        KExprData::Lit(l) => match l {
          Literal::NatVal(n) => { 0u8.hash(state); n.hash(state); }
          Literal::StrVal(s) => { 1u8.hash(state); s.hash(state); }
        }
        KExprData::Proj(id, idx, s) => { id.addr.hash(state); idx.hash(state); s.hash(state); }
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
      KExprData::LetE(ty, val, body, name, _) => {
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
  /// Lean's non-canonical mutual block (source order). Metadata for
  /// roundtripping back to Lean — NOT the canonical Ixon mutual block.
  pub lean_all: M::Field<Vec<MetaId<M>>>,
  /// Canonical mutual block from Ixon's SCC + partition refinement.
  /// Members are in canonical order for de Bruijn indexing in anon mode.
  pub canonical_block: Vec<MetaId<M>>,
}

/// A theorem declaration.
#[derive(Debug, Clone)]
pub struct KTheoremVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub value: KExpr<M>,
  /// Lean's non-canonical mutual block (source order). Metadata for
  /// roundtripping back to Lean — NOT the canonical Ixon mutual block.
  pub lean_all: M::Field<Vec<MetaId<M>>>,
  /// Canonical mutual block from Ixon's SCC + partition refinement.
  pub canonical_block: Vec<MetaId<M>>,
}

/// An opaque constant.
#[derive(Debug, Clone)]
pub struct KOpaqueVal<M: MetaMode> {
  pub cv: KConstantVal<M>,
  pub value: KExpr<M>,
  pub is_unsafe: bool,
  /// Lean's non-canonical mutual block (source order). Metadata for
  /// roundtripping back to Lean — NOT the canonical Ixon mutual block.
  pub lean_all: M::Field<Vec<MetaId<M>>>,
  /// Canonical mutual block from Ixon's SCC + partition refinement.
  pub canonical_block: Vec<MetaId<M>>,
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
  /// Lean's non-canonical mutual block (source order). Metadata for
  /// roundtripping back to Lean — NOT the canonical Ixon mutual block.
  pub lean_all: M::Field<Vec<MetaId<M>>>,
  /// Canonical mutual block from Ixon's SCC + partition refinement.
  /// Contains inductives + constructors (they form a cycle in the
  /// reference graph and thus share an SCC).
  pub canonical_block: Vec<MetaId<M>>,
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
  /// Lean's non-canonical mutual block (source order). Metadata for
  /// roundtripping — NOT the canonical Ixon mutual block.
  pub lean_all: M::Field<Vec<MetaId<M>>>,
  /// Canonical mutual block of *recursors* from Ixon's SCC + partition
  /// refinement. Separate from the inductive block because recursors
  /// reference constructors one-way (no back-edge from inductive).
  pub canonical_block: Vec<MetaId<M>>,
  /// Canonical inductive block: the mutually recursive set of inductives
  /// associated with this recursor's major inductive, computed from
  /// Ixon's SCC structure. Used by the typechecker for nested inductive
  /// detection.
  pub induct_block: Vec<MetaId<M>>,
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
