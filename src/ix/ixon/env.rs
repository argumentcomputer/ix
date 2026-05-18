//! Environment for storing Ixon data.

use dashmap::DashMap;
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::env::{Name, ReducibilityHints};

use super::comm::Comm;
use super::constant::Constant;
use super::lazy::LazyConstant;
use super::metadata::ConstantMeta;

/// A named constant with metadata.
#[derive(Clone, Debug)]
pub struct Named {
  /// Address of the constant (in consts map)
  pub addr: Address,
  /// Typed metadata for this constant (includes mutual context in `all` field)
  pub meta: ConstantMeta,
  /// For aux_gen-rewritten constants: the original Lean constant's compiled
  /// form (address + metadata). Ingress uses `addr`/`meta` (the canonical
  /// aux_gen form). Decompile uses `original` for faithful roundtrip of
  /// binder names and other cosmetic metadata.
  pub original: Option<(Address, ConstantMeta)>,
}

impl Named {
  pub fn new(addr: Address, meta: ConstantMeta) -> Self {
    Named { addr, meta, original: None }
  }

  pub fn with_addr(addr: Address) -> Self {
    Named { addr, meta: ConstantMeta::default(), original: None }
  }
}

/// Nested-auxiliary layout info for a mutual inductive block.
///
/// Paired perm + source_ctor_counts so consumers have everything needed to
/// correctly permute source-order aux motives/minors into canonical
/// positions. Both arrays have one entry per source-walk-discovered aux.
///
/// This lives in `ixon::env` (not `compile::surgery`, where it originated)
/// so it can be persisted into the serialized Ixon environment as a
/// side-table on [`Env::aux_layouts`]. The surgery layer re-exports it.
///
/// Keyed by `<source_all[0]>` — the first inductive in the Lean source's
/// mutual block, which is what Lean hangs `.rec_N` / `.below_N` /
/// `.brecOn_N` names off.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuxLayout {
  /// `perm[source_j] = canonical_i`: Lean's source-walk position to
  /// our canonical hash-sorted position.
  pub perm: Vec<usize>,
  /// Number of constructors for the aux inductive at source position j.
  /// Same count regardless of which position the aux ends up at
  /// canonically (it's a property of the external nested inductive).
  pub source_ctor_counts: Vec<usize>,
}

/// The Ixon environment.
///
/// Contains five maps:
/// - `consts`: Alpha-invariant constants indexed by content hash,
///   stored lazily as serialized bytes ([`LazyConstant`]) and
///   materialized on demand.
/// - `named`: Named references with metadata and mutual context
/// - `blobs`: Raw data (strings, nats, files)
/// - `names`: Hash-consed Lean.Name components (Address -> Name)
/// - `comms`: Cryptographic commitments (secrets)
#[derive(Debug, Default)]
pub struct Env {
  /// Alpha-invariant constants: Address -> LazyConstant (raw bytes +
  /// optional materialized cache; see [`LazyConstant`]).
  pub consts: DashMap<Address, LazyConstant>,
  /// Named references: Name -> (constant address, metadata, ctx)
  pub named: DashMap<Name, Named>,
  /// Raw data blobs: Address -> bytes
  pub blobs: DashMap<Address, Vec<u8>>,
  /// Hash-consed Lean.Name components: Address -> Name
  pub names: DashMap<Address, Name>,
  /// Cryptographic commitments: commitment Address -> Comm
  pub comms: DashMap<Address, Comm>,
  /// Reducibility hints sidecar harvested by [`Env::get_anon`] from the
  /// otherwise-discarded Named section. Keyed by the constant's
  /// projection/standalone address (i.e. `Named.addr` — the address the
  /// kernel sees, **not** the name-hash address). Empty for envs loaded
  /// via [`Env::get`] / [`Env::new`] / `store_*`; meta-mode ingress
  /// pulls hints directly from `Named.meta` and ignores this field.
  ///
  /// Anon-mode ingress passes these hints through to
  /// `ingress_defn` so the kernel's lazy-delta tiebreak
  /// (`def_eq::def_rank_id`) sees realistic heights instead of the
  /// constant `Regular(0)` fallback. Hints are performance advice —
  /// supplying them in anon mode does not relax the kernel's
  /// metadata-free correctness model.
  pub anon_hints: FxHashMap<Address, ReducibilityHints>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      consts: DashMap::new(),
      named: DashMap::new(),
      blobs: DashMap::new(),
      names: DashMap::new(),
      comms: DashMap::new(),
      anon_hints: FxHashMap::default(),
    }
  }

  /// Store a blob and return its content address.
  pub fn store_blob(&self, bytes: Vec<u8>) -> Address {
    let addr = Address::hash(&bytes);
    self.blobs.insert(addr.clone(), bytes);
    addr
  }

  /// Get a blob by address.
  pub fn get_blob(&self, addr: &Address) -> Option<Vec<u8>> {
    self.blobs.get(addr).map(|r| r.clone())
  }

  /// Store a structured constant under `addr`.
  ///
  /// Serializes the constant once and pre-populates the
  /// [`LazyConstant`] cache so subsequent `Env::put` is a memcpy and
  /// the first `get_const` call is free.
  pub fn store_const(&self, addr: Address, constant: Constant) {
    self.consts.insert(addr, LazyConstant::from_constant(constant));
  }

  /// Store an already-serialized constant under `addr` (lazy load path).
  /// `bytes` must be exactly what `Constant::put` produced for `addr`.
  pub fn store_const_lazy(&self, addr: Address, bytes: Arc<[u8]>) {
    self.consts.insert(addr, LazyConstant::from_bytes(bytes));
  }

  /// Store a constant as a window into a memory-mapped `.ixe` file.
  /// `(mmap, offset, len)` must reference exactly what `Constant::put`
  /// produced for `addr`. Used by [`Env::get_anon_mmap`] to avoid
  /// heap-copying on-disk bytes — the OS page cache backs the slice.
  pub fn store_const_lazy_mmap(
    &self,
    addr: Address,
    mmap: Arc<memmap2::Mmap>,
    offset: usize,
    len: usize,
  ) {
    self
      .consts
      .insert(addr, LazyConstant::from_mmap_slice(mmap, offset, len));
  }

  /// Get a constant by address, materializing on demand.
  ///
  /// Returns `None` if the address is not present or materialization
  /// fails (e.g., corrupt bytes). Use [`Self::try_get_const`] to
  /// inspect materialization errors.
  pub fn get_const(&self, addr: &Address) -> Option<Arc<Constant>> {
    self.consts.get(addr).and_then(|r| r.value().get().ok())
  }

  /// Get a constant by address, returning materialization errors.
  pub fn try_get_const(
    &self,
    addr: &Address,
  ) -> Option<Result<Arc<Constant>, String>> {
    self.consts.get(addr).map(|r| r.value().get())
  }

  /// Get the raw serialized bytes of a constant without materializing it.
  pub fn get_const_bytes(&self, addr: &Address) -> Option<Arc<[u8]>> {
    self.consts.get(addr).map(|r| Arc::from(r.value().raw_bytes()))
  }

  /// Register a named constant.
  pub fn register_name(&self, name: Name, named: Named) {
    self.named.insert(name, named);
  }

  /// Look up a name.
  pub fn lookup_name(&self, name: &Name) -> Option<Named> {
    self.named.get(name).map(|r| r.clone())
  }

  /// Store a hash-consed name component.
  pub fn store_name(&self, addr: Address, name: Name) {
    self.names.insert(addr, name);
  }

  /// Get a name by address.
  pub fn get_name(&self, addr: &Address) -> Option<Name> {
    self.names.get(addr).map(|r| r.clone())
  }

  /// Store a commitment.
  pub fn store_comm(&self, addr: Address, comm: Comm) {
    self.comms.insert(addr, comm);
  }

  /// Get a commitment by address.
  pub fn get_comm(&self, addr: &Address) -> Option<Comm> {
    self.comms.get(addr).map(|r| r.clone())
  }

  /// Number of constants.
  pub fn const_count(&self) -> usize {
    self.consts.len()
  }

  /// Number of named entries.
  pub fn named_count(&self) -> usize {
    self.named.len()
  }

  /// Number of hash-consed name components.
  pub fn name_count(&self) -> usize {
    self.names.len()
  }

  /// Number of blobs.
  pub fn blob_count(&self) -> usize {
    self.blobs.len()
  }

  /// Number of commitments.
  pub fn comm_count(&self) -> usize {
    self.comms.len()
  }

  /// BFS-collect all addresses transitively reachable from `root` via
  /// the `Constant.refs` field. The returned set includes `root` itself.
  ///
  /// Addresses that are referenced but not present in `self.consts` are
  /// still added to the set (so verifiers see external assumptions)
  /// but we cannot recurse into them.
  ///
  /// Visited constants are materialized via [`LazyConstant::get`];
  /// subsequent BFS passes over the same closure are free.
  pub fn bfs_refs(&self, root: &Address) -> FxHashSet<Address> {
    let mut visited: FxHashSet<Address> = FxHashSet::default();
    let mut queue: VecDeque<Address> = VecDeque::new();
    visited.insert(root.clone());
    queue.push_back(root.clone());
    while let Some(addr) = queue.pop_front() {
      // Materialize the constant just long enough to read its refs.
      // Drop the DashMap guard before recursing so concurrent BFS
      // calls don't deadlock on the same shard.
      let refs: Option<Vec<Address>> = self
        .consts
        .get(&addr)
        .and_then(|r| r.value().get().ok())
        .map(|c| c.refs.clone());
      if let Some(rs) = refs {
        for r in rs {
          if visited.insert(r.clone()) {
            queue.push_back(r);
          }
        }
      }
    }
    visited
  }

  /// Transitive dep addresses of `root`, excluding `root` itself. Sorted
  /// lex-ascending for canonical use (e.g., feeding `merkle_root_canonical`).
  pub fn transitive_deps_excl(&self, root: &Address) -> Vec<Address> {
    let mut set = self.bfs_refs(root);
    set.remove(root);
    let mut v: Vec<Address> = set.into_iter().collect();
    v.sort_unstable();
    v
  }
}

impl Clone for Env {
  fn clone(&self) -> Self {
    let consts = DashMap::new();
    for entry in self.consts.iter() {
      consts.insert(entry.key().clone(), entry.value().clone());
    }

    let named = DashMap::new();
    for entry in self.named.iter() {
      named.insert(entry.key().clone(), entry.value().clone());
    }

    let blobs = DashMap::new();
    for entry in self.blobs.iter() {
      blobs.insert(entry.key().clone(), entry.value().clone());
    }

    let names = DashMap::new();
    for entry in self.names.iter() {
      names.insert(entry.key().clone(), entry.value().clone());
    }

    let comms = DashMap::new();
    for entry in self.comms.iter() {
      comms.insert(entry.key().clone(), entry.value().clone());
    }

    Env {
      consts,
      named,
      blobs,
      names,
      comms,
      anon_hints: self.anon_hints.clone(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::Name;
  use crate::ix::ixon::constant::{Axiom, Constant, ConstantInfo};
  use crate::ix::ixon::expr::Expr;
  use std::sync::Arc;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  fn dummy_constant() -> Constant {
    Constant::new(ConstantInfo::Axio(Axiom {
      is_unsafe: false,
      lvls: 0,
      typ: Arc::new(Expr::Sort(0)),
    }))
  }

  #[test]
  fn store_and_get_blob() {
    let env = Env::new();
    let data = vec![1, 2, 3, 4, 5];
    let addr = env.store_blob(data.clone());
    assert_eq!(env.get_blob(&addr), Some(data));
    // Same content produces same address
    let addr2 = env.store_blob(vec![1, 2, 3, 4, 5]);
    assert_eq!(addr, addr2);
  }

  #[test]
  fn store_and_get_const() {
    let env = Env::new();
    let constant = dummy_constant();
    let addr = Address::hash(b"test-constant");
    env.store_const(addr.clone(), constant.clone());
    let got = env.get_const(&addr).unwrap();
    assert_eq!(*got, constant);
  }

  #[test]
  fn register_and_lookup_name() {
    let env = Env::new();
    let name = n("MyConst");
    let addr = Address::hash(b"my-const-addr");
    let named = Named::with_addr(addr.clone());
    env.register_name(name.clone(), named.clone());
    let got = env.lookup_name(&name).unwrap();
    assert_eq!(got.addr, addr);
  }

  #[test]
  fn store_and_get_name_component() {
    let env = Env::new();
    let name = n("Component");
    let addr = Address::hash(b"name-component");
    env.store_name(addr.clone(), name.clone());
    assert_eq!(env.get_name(&addr), Some(name));
  }

  #[test]
  fn store_and_get_comm() {
    let env = Env::new();
    let secret = Address::hash(b"secret");
    let payload = Address::hash(b"payload");
    let comm = Comm::new(secret.clone(), payload.clone());
    let comm_addr = Address::hash(b"comm-addr");
    env.store_comm(comm_addr.clone(), comm.clone());
    let got = env.get_comm(&comm_addr).unwrap();
    assert_eq!(got, comm);
  }

  #[test]
  fn counts() {
    let env = Env::new();
    assert_eq!(env.const_count(), 0);
    assert_eq!(env.named_count(), 0);
    assert_eq!(env.blob_count(), 0);
    assert_eq!(env.name_count(), 0);
    assert_eq!(env.comm_count(), 0);

    env.store_blob(vec![1]);
    assert_eq!(env.blob_count(), 1);

    env.store_const(Address::hash(b"c1"), dummy_constant());
    assert_eq!(env.const_count(), 1);

    env.register_name(n("x"), Named::with_addr(Address::hash(b"x")));
    assert_eq!(env.named_count(), 1);

    env.store_name(Address::hash(b"n1"), n("n"));
    assert_eq!(env.name_count(), 1);

    env.store_comm(
      Address::hash(b"cm"),
      Comm::new(Address::hash(b"s"), Address::hash(b"p")),
    );
    assert_eq!(env.comm_count(), 1);
  }

  #[test]
  fn missing_keys_return_none() {
    let env = Env::new();
    let missing = Address::hash(b"nonexistent");
    assert!(env.get_blob(&missing).is_none());
    assert!(env.get_const(&missing).is_none());
    assert!(env.lookup_name(&n("missing")).is_none());
    // addr_to_name reverse index was removed (unsound for alpha-equivalent constants)
    assert!(env.get_name(&missing).is_none());
    assert!(env.get_comm(&missing).is_none());
  }

  #[test]
  fn blob_content_addressing() {
    let env = Env::new();
    let addr1 = env.store_blob(vec![1, 2, 3]);
    let addr2 = env.store_blob(vec![4, 5, 6]);
    // Different content produces different addresses
    assert_ne!(addr1, addr2);
    // Same content produces same address
    let addr3 = env.store_blob(vec![1, 2, 3]);
    assert_eq!(addr1, addr3);
  }

  /// Build a constant with the given refs (for BFS tests). `discriminator`
  /// is folded into `lvls` so callers can produce content-distinct
  /// constants when the same ref-set would otherwise collide (e.g.
  /// two independent leaf nodes both with empty refs).
  fn const_with_refs(refs: Vec<Address>) -> Constant {
    const_with_refs_discriminator(refs, 0)
  }

  fn const_with_refs_discriminator(
    refs: Vec<Address>,
    discriminator: u64,
  ) -> Constant {
    Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: discriminator,
        typ: Arc::new(Expr::Sort(0)),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
  }

  /// Store a constant at its true content address and return that
  /// address. Use this instead of `store_const(Address::hash(b"a"),
  /// ...)` for tests that round-trip through `Env::put`/`Env::get`;
  /// the load path verifies `Address::hash(bytes) == addr` per
  /// entry, so fake keys are rejected.
  fn store_canonical(env: &Env, c: Constant) -> Address {
    let (addr, _) = c.commit();
    env.store_const(addr.clone(), c);
    addr
  }

  #[test]
  fn bfs_refs_singleton_no_deps() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), const_with_refs(vec![]));
    let visited = env.bfs_refs(&a);
    assert_eq!(visited.len(), 1);
    assert!(visited.contains(&a));
  }

  #[test]
  fn bfs_refs_transitive() {
    // a -> b -> c, a -> d
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    let d = Address::hash(b"d");
    env.store_const(a.clone(), const_with_refs(vec![b.clone(), d.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![c.clone()]));
    env.store_const(c.clone(), const_with_refs(vec![]));
    env.store_const(d.clone(), const_with_refs(vec![]));
    let visited = env.bfs_refs(&a);
    assert_eq!(visited.len(), 4);
    assert!(visited.contains(&a));
    assert!(visited.contains(&b));
    assert!(visited.contains(&c));
    assert!(visited.contains(&d));
  }

  #[test]
  fn bfs_refs_cycle_terminates() {
    // a -> b -> a (cyclic, should not infinite-loop)
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![a.clone()]));
    let visited = env.bfs_refs(&a);
    assert_eq!(visited.len(), 2);
  }

  #[test]
  fn bfs_refs_includes_external_addresses() {
    // a -> b, where b is referenced but not stored in env. We still
    // surface b in the visited set so callers see the external dep.
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b-external");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    let visited = env.bfs_refs(&a);
    assert!(visited.contains(&a));
    assert!(visited.contains(&b));
  }

  #[test]
  fn transitive_deps_excl_excludes_root() {
    // a -> b -> c
    let env = Env::new();
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let c = Address::hash(b"c");
    env.store_const(a.clone(), const_with_refs(vec![b.clone()]));
    env.store_const(b.clone(), const_with_refs(vec![c.clone()]));
    env.store_const(c.clone(), const_with_refs(vec![]));
    let deps = env.transitive_deps_excl(&a);
    assert!(!deps.contains(&a));
    assert!(deps.contains(&b));
    assert!(deps.contains(&c));
    assert_eq!(deps.len(), 2);
  }

  #[test]
  fn transitive_deps_excl_is_sorted() {
    let env = Env::new();
    let a = Address::hash(b"a");
    // Use multiple deps; the returned Vec should be in sorted order
    // regardless of how the BFS visited them.
    let mut refs: Vec<Address> = (0..16)
      .map(|i| Address::hash(format!("dep-{i}").as_bytes()))
      .collect();
    env.store_const(a.clone(), const_with_refs(refs.clone()));
    for r in &refs {
      env.store_const(r.clone(), const_with_refs(vec![]));
    }
    refs.sort_unstable();
    let deps = env.transitive_deps_excl(&a);
    assert_eq!(deps, refs);
  }

  #[test]
  fn transitive_deps_excl_empty_for_root_with_no_refs() {
    let env = Env::new();
    let a = Address::hash(b"a");
    env.store_const(a.clone(), const_with_refs(vec![]));
    assert!(env.transitive_deps_excl(&a).is_empty());
  }

  /// Round-trips an env through serialize → deserialize so the
  /// deserialized side holds purely lazy entries, then asserts that
  /// a `transitive_deps_excl(seed)` walk only touches constants
  /// reachable from `seed` (correctness of the BFS).
  ///
  /// Lazy-loaded `LazyConstant`s no longer cache materialized values
  /// (see `src/ix/ixon/lazy.rs` "Cache policy" docs), so we can't
  /// observe materialization via `is_materialized()` after a walk —
  /// that observable was always-false. Instead we assert the BFS
  /// returns exactly the closure, and that `is_materialized()` stays
  /// false everywhere (proving the load path doesn't accidentally
  /// pre-populate the cache).
  #[test]
  fn lazy_sparsity_only_materializes_closure() {
    // Build a small env: a→b→c, and an independent d. Each const is
    // stored at its true content address (round-trip through `put`+`get`
    // verifies `Address::hash(bytes) == addr`). The `d` discriminator
    // avoids a content-hash collision with `c` (both have empty refs).
    let env = Env::new();
    let c = store_canonical(&env, const_with_refs(vec![]));
    let b = store_canonical(&env, const_with_refs(vec![c.clone()]));
    let a = store_canonical(&env, const_with_refs(vec![b.clone()]));
    let d = store_canonical(
      &env,
      const_with_refs_discriminator(vec![], 1),
    );

    // Serialize → deserialize so all entries are lazy-from-bytes.
    let mut buf = Vec::new();
    env.put(&mut buf).unwrap();
    let loaded = Env::get(&mut buf.as_slice()).unwrap();
    for entry in loaded.consts.iter() {
      assert!(
        !entry.value().is_materialized(),
        "freshly-loaded entry {:?} should not be materialized",
        entry.key()
      );
    }

    // BFS the closure of `a`; should hit {a, b, c} but not `d`.
    let deps = loaded.transitive_deps_excl(&a);
    let dep_set: FxHashSet<Address> = deps.iter().cloned().collect();
    assert!(dep_set.contains(&b), "`b` reachable from `a`");
    assert!(dep_set.contains(&c), "`c` reachable from `a` via `b`");
    assert!(!dep_set.contains(&d), "`d` should not be in `a`'s closure");
    assert!(!dep_set.contains(&a), "deps_excl excludes the seed");

    // Even after the BFS, no entries should report as materialized:
    // lazy-loaded `LazyConstant`s parse fresh on each `get()` and
    // don't cache (env-side caching is what kept mathlib's RSS at
    // ~30GB; the cache-free policy is what made `--anon` viable).
    for entry in loaded.consts.iter() {
      assert!(
        !entry.value().is_materialized(),
        "entry {:?} should remain unmaterialized after BFS",
        entry.key()
      );
    }
  }
}
