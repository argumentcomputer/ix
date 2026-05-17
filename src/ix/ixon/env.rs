//! Environment for storing Ixon data.

use dashmap::DashMap;
use rustc_hash::FxHashSet;
use std::collections::VecDeque;

use crate::ix::address::Address;
use crate::ix::env::Name;

use super::comm::Comm;
use super::constant::Constant;
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
/// - `consts`: Alpha-invariant constants indexed by content hash
/// - `named`: Named references with metadata and mutual context
/// - `blobs`: Raw data (strings, nats, files)
/// - `names`: Hash-consed Lean.Name components (Address -> Name)
/// - `comms`: Cryptographic commitments (secrets)
#[derive(Debug, Default)]
pub struct Env {
  /// Alpha-invariant constants: Address -> Constant
  pub consts: DashMap<Address, Constant>,
  /// Named references: Name -> (constant address, metadata, ctx)
  pub named: DashMap<Name, Named>,
  /// Raw data blobs: Address -> bytes
  pub blobs: DashMap<Address, Vec<u8>>,
  /// Hash-consed Lean.Name components: Address -> Name
  pub names: DashMap<Address, Name>,
  /// Cryptographic commitments: commitment Address -> Comm
  pub comms: DashMap<Address, Comm>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      consts: DashMap::new(),
      named: DashMap::new(),
      blobs: DashMap::new(),
      names: DashMap::new(),
      comms: DashMap::new(),
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

  /// Store a constant and return its content address.
  /// Note: The actual hashing/serialization is done elsewhere.
  pub fn store_const(&self, addr: Address, constant: Constant) {
    self.consts.insert(addr, constant);
  }

  /// Get a constant by address.
  pub fn get_const(&self, addr: &Address) -> Option<Constant> {
    self.consts.get(addr).map(|r| r.clone())
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
  pub fn bfs_refs(&self, root: &Address) -> FxHashSet<Address> {
    let mut visited: FxHashSet<Address> = FxHashSet::default();
    let mut queue: VecDeque<Address> = VecDeque::new();
    visited.insert(root.clone());
    queue.push_back(root.clone());
    while let Some(addr) = queue.pop_front() {
      if let Some(entry) = self.consts.get(&addr) {
        for r in &entry.value().refs {
          if visited.insert(r.clone()) {
            queue.push_back(r.clone());
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

    Env { consts, named, blobs, names, comms }
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
    assert_eq!(got, constant);
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

  /// Build a constant with the given refs (for BFS tests).
  fn const_with_refs(refs: Vec<Address>) -> Constant {
    Constant::with_tables(
      ConstantInfo::Axio(Axiom {
        is_unsafe: false,
        lvls: 0,
        typ: Arc::new(Expr::Sort(0)),
      }),
      Vec::new(),
      refs,
      Vec::new(),
    )
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
}
