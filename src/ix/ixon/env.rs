//! Environment for storing Ixon data.

use dashmap::DashMap;

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
}

impl Named {
  pub fn new(addr: Address, meta: ConstantMeta) -> Self {
    Named { addr, meta }
  }

  pub fn with_addr(addr: Address) -> Self {
    Named { addr, meta: ConstantMeta::default() }
  }
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
}
