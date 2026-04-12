//! Zero kernel environment.
//!
//! `KEnv<M>` maps `KId<M>` to `KConst<M>`. In Anon mode, KId compares by
//! address only (name is `()`). In Meta mode, both address and name participate,
//! enabling smooth transitions between modes.

use std::sync::Arc;

use dashmap::DashMap;

use super::constant::KConst;
use super::expr::KExpr;
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;

/// Shared Merkle hash. Cheap to clone (Arc refcount bump).
pub type Addr = Arc<blake3::Hash>;

/// Hash-consing intern table for expressions and universes.
///
/// Thread-safe via `DashMap`: usable from parallel ingress and
/// sequential type checking alike. Guarantees pointer uniqueness
/// by blake3 hash: `ptr(a) == ptr(b)` iff `hash(a) == hash(b)`.
pub struct InternTable<M: KernelMode> {
  univs: DashMap<blake3::Hash, KUniv<M>>,
  exprs: DashMap<blake3::Hash, KExpr<M>>,
}

impl<M: KernelMode> InternTable<M> {
  pub fn new() -> Self {
    InternTable { univs: DashMap::default(), exprs: DashMap::default() }
  }

  /// Intern a universe: if one with the same hash exists, return the
  /// existing Arc (ensuring pointer uniqueness). Otherwise insert and return.
  /// Atomic via DashMap entry — safe for concurrent access.
  pub fn intern_univ(&self, u: KUniv<M>) -> KUniv<M> {
    let key = **u.addr();
    self.univs.entry(key).or_insert(u).value().clone()
  }

  /// Intern an expression: same pointer-uniqueness guarantee as `intern_univ`.
  pub fn intern_expr(&self, e: KExpr<M>) -> KExpr<M> {
    let key = **e.addr();
    self.exprs.entry(key).or_insert(e).value().clone()
  }
}

/// The global zero kernel environment.
///
/// Thread-safe via `DashMap`: supports concurrent reads and writes during
/// parallel compilation (ingress) and sequential type checking alike.
/// `get()` returns owned `KConst`/`Vec` (cheap Arc clones) to avoid
/// holding DashMap guards across call boundaries.
pub struct KEnv<M: KernelMode> {
  /// Loaded constants keyed by `KId`.
  pub consts: DashMap<KId<M>, KConst<M>>,
  /// Block membership: block id → ordered member ids.
  pub blocks: DashMap<KId<M>, Vec<KId<M>>>,
}

impl<M: KernelMode> KEnv<M> {
  pub fn new() -> Self {
    KEnv { consts: DashMap::default(), blocks: DashMap::default() }
  }

  pub fn get(&self, id: &KId<M>) -> Option<KConst<M>> {
    self.consts.get(id).map(|r| r.value().clone())
  }

  pub fn insert(&self, id: KId<M>, c: KConst<M>) {
    self.consts.insert(id, c);
  }

  pub fn len(&self) -> usize {
    self.consts.len()
  }

  pub fn is_empty(&self) -> bool {
    self.consts.is_empty()
  }

  pub fn contains_key(&self, id: &KId<M>) -> bool {
    self.consts.contains_key(id)
  }

  /// Iterate over all constants. Returns owned (KId, KConst) pairs.
  /// Internally snapshots the DashMap — safe for concurrent access.
  pub fn iter(&self) -> impl Iterator<Item = (KId<M>, KConst<M>)> + '_ {
    self.consts.iter().map(|r| (r.key().clone(), r.value().clone()))
  }

  /// Get block members. Returns owned Vec (cheap KId clones).
  pub fn get_block(&self, id: &KId<M>) -> Option<Vec<KId<M>>> {
    self.blocks.get(id).map(|r| r.value().clone())
  }

  /// Insert a block membership entry.
  pub fn insert_block(&self, id: KId<M>, members: Vec<KId<M>>) {
    self.blocks.insert(id, members);
  }
}

#[cfg(test)]
mod tests {
  use super::super::mode::Anon;
  use super::*;
  use crate::ix::address::Address;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }

  fn mk_axio(_s: &str) -> KConst<Anon> {
    KConst::Axio {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
    }
  }

  #[test]
  fn new_env_is_empty() {
    let env = KEnv::<Anon>::new();
    assert!(env.is_empty());
    assert_eq!(env.len(), 0);
  }

  #[test]
  fn insert_and_get() {
    let mut env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert_eq!(env.len(), 1);
    assert!(env.get(&id).is_some());
  }

  #[test]
  fn contains_key_works() {
    let mut env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    assert!(!env.contains_key(&id));
    env.insert(id.clone(), mk_axio("Nat"));
    assert!(env.contains_key(&id));
  }

  #[test]
  fn get_missing_returns_none() {
    let env = KEnv::<Anon>::new();
    assert!(env.get(&mk_id("missing")).is_none());
  }

  #[test]
  fn get_by_id_works() {
    let mut env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert!(env.get(&id).is_some());
    assert!(env.get(&mk_id("missing")).is_none());
  }

  #[test]
  fn intern_univ_dedup() {
    let it = InternTable::<Anon>::new();
    let z1 = KUniv::zero();
    let z2 = KUniv::zero();
    // Before interning, same hash but different Arcs
    assert!(!z1.ptr_eq(&z2));
    let i1 = it.intern_univ(z1);
    let i2 = it.intern_univ(z2);
    assert!(i1.ptr_eq(&i2));
  }

  #[test]
  fn intern_univ_different() {
    let it = InternTable::<Anon>::new();
    let z = it.intern_univ(KUniv::zero());
    let s = it.intern_univ(KUniv::succ(KUniv::zero()));
    assert!(!z.ptr_eq(&s));
  }

  #[test]
  fn intern_expr_dedup() {
    let it = InternTable::<Anon>::new();
    let v1 = KExpr::var(0, ());
    let v2 = KExpr::var(0, ());
    assert!(!v1.ptr_eq(&v2));
    let i1 = it.intern_expr(v1);
    let i2 = it.intern_expr(v2);
    assert!(i1.ptr_eq(&i2));
  }

  #[test]
  fn intern_expr_different() {
    let it = InternTable::<Anon>::new();
    let v0 = it.intern_expr(KExpr::var(0, ()));
    let v1 = it.intern_expr(KExpr::var(1, ()));
    assert!(!v0.ptr_eq(&v1));
  }

  #[test]
  fn iter_all_entries() {
    let mut env = KEnv::<Anon>::new();
    env.insert(mk_id("A"), mk_axio("A"));
    env.insert(mk_id("B"), mk_axio("B"));
    assert_eq!(env.iter().count(), 2);
  }
}
