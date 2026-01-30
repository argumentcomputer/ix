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
/// - `addr_to_name`: Reverse index from constant address to name (for O(1) lookup)
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
  /// Reverse index: constant Address -> Name (for fast lookup during decompile)
  pub addr_to_name: DashMap<Address, Name>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      consts: DashMap::new(),
      named: DashMap::new(),
      blobs: DashMap::new(),
      names: DashMap::new(),
      comms: DashMap::new(),
      addr_to_name: DashMap::new(),
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
    // Also insert into reverse index for O(1) lookup by address
    self.addr_to_name.insert(named.addr.clone(), name.clone());
    self.named.insert(name, named);
  }

  /// Look up a name.
  pub fn lookup_name(&self, name: &Name) -> Option<Named> {
    self.named.get(name).map(|r| r.clone())
  }

  /// Look up name by constant address (O(1) using reverse index).
  pub fn get_name_by_addr(&self, addr: &Address) -> Option<Name> {
    self.addr_to_name.get(addr).map(|r| r.clone())
  }

  /// Look up named entry by constant address (O(1) using reverse index).
  pub fn get_named_by_addr(&self, addr: &Address) -> Option<Named> {
    self.get_name_by_addr(addr).and_then(|name| self.lookup_name(&name))
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

    let addr_to_name = DashMap::new();
    for entry in self.addr_to_name.iter() {
      addr_to_name.insert(entry.key().clone(), entry.value().clone());
    }

    Env { consts, named, blobs, names, comms, addr_to_name }
  }
}
