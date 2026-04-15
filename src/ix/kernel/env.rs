//! Zero kernel environment.
//!
//! `KEnv<M>` maps `KId<M>` to `KConst<M>`, and owns all shared kernel state:
//! the intern table, type-checking caches, and resolved primitives.
//!
//! All mutable state uses `DashMap`/`DashSet` for lock-free concurrent access.
//! Multiple `TypeChecker` instances can share one `Arc<KEnv>` and run in parallel.

use std::collections::BTreeSet;
use std::sync::{Arc, OnceLock};

use dashmap::{DashMap, DashSet};

use crate::ix::address::Address;

use super::constant::{KConst, RecRule};
use super::expr::KExpr;
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::primitive::Primitives;

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

impl<M: KernelMode> Default for InternTable<M> {
  fn default() -> Self {
    Self::new()
  }
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

/// Generated recursor, cached after inductive validation.
#[derive(Clone, Debug)]
pub struct GeneratedRecursor<M: KernelMode> {
  pub ind_addr: Address,
  pub ty: KExpr<M>,
  pub rules: Vec<RecRule<M>>,
}

/// The global zero kernel environment.
///
/// Thread-safe via `DashMap`/`DashSet`: supports concurrent reads and writes
/// from multiple `TypeChecker` instances running in parallel. Contains all
/// shared kernel state: constants, intern table, and type-checking caches.
///
/// `get()` returns owned `KConst`/`Vec` (cheap Arc clones) to avoid
/// holding DashMap guards across call boundaries.
pub struct KEnv<M: KernelMode> {
  // -- Constants --
  /// Loaded constants keyed by `KId`.
  pub consts: DashMap<KId<M>, KConst<M>>,
  /// Block membership: block id → ordered member ids.
  pub blocks: DashMap<KId<M>, Vec<KId<M>>>,

  // -- Intern table (hash-consing for pointer dedup) --
  pub intern: InternTable<M>,

  // -- Primitives (resolved lazily from consts) --
  prims: OnceLock<Primitives<M>>,

  // -- Global caches (grow monotonically, keyed by content hash) --
  // All cache keys use `Addr` (= `Arc<blake3::Hash>`, content-addressed) rather
  // than `Arc::as_ptr` pointers, avoiding the ABA problem where deallocated
  // pointers are reused by the allocator for semantically different expressions.
  /// WHNF cache (full, with delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// WHNF cache (no delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_no_delta_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Infer cache: keyed by (expr_hash, ctx_hash). Context-dependent.
  pub infer_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Infer-only cache: results from infer_only mode (no def-eq checks).
  pub infer_only_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Def-eq cache: keyed by (expr_hash, expr_hash, ctx_hash). Context-dependent.
  pub def_eq_cache: DashMap<(Addr, Addr, Addr), bool>,
  /// Failed def-eq pairs in lazy delta: canonical ordering by hash.
  pub def_eq_failure: DashSet<(Addr, Addr, Addr)>,
  /// Ingress cache: LeanExpr → KExpr conversion results.
  /// Keyed by (expr_hash, param_names_hash) to account for different
  /// level param bindings producing different KExprs from the same LeanExpr.
  pub ingress_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Generated recursors, keyed by inductive Muts block id.
  pub recursor_cache: DashMap<KId<M>, Vec<GeneratedRecursor<M>>>,
  /// Maps the set of major inductive KIds to the inductive block id.
  pub rec_majors_cache: DashMap<BTreeSet<KId<M>>, KId<M>>,
}

impl<M: KernelMode> Default for KEnv<M> {
  fn default() -> Self {
    Self::new()
  }
}

impl<M: KernelMode> KEnv<M> {
  pub fn new() -> Self {
    KEnv {
      consts: DashMap::default(),
      blocks: DashMap::default(),
      intern: InternTable::new(),
      prims: OnceLock::new(),
      whnf_cache: DashMap::default(),
      whnf_no_delta_cache: DashMap::default(),
      infer_cache: DashMap::default(),
      infer_only_cache: DashMap::default(),
      def_eq_cache: DashMap::default(),
      def_eq_failure: DashSet::default(),
      ingress_cache: DashMap::default(),
      recursor_cache: DashMap::default(),
      rec_majors_cache: DashMap::default(),
    }
  }

  /// Resolve primitives from the environment (cached via OnceLock).
  pub fn prims(&self) -> &Primitives<M> {
    self.prims.get_or_init(|| Primitives::from_env(self))
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
    let env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert_eq!(env.len(), 1);
    assert!(env.get(&id).is_some());
  }

  #[test]
  fn contains_key_works() {
    let env = KEnv::<Anon>::new();
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
    let env = KEnv::<Anon>::new();
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
    let env = KEnv::<Anon>::new();
    env.insert(mk_id("A"), mk_axio("A"));
    env.insert(mk_id("B"), mk_axio("B"));
    assert_eq!(env.iter().count(), 2);
  }
}
