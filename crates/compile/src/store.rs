//! Content-addressed store for Ix compilation data (`~/.ix/store`).
//!
//! Delegates to [`ix_common::store::IxStore`] (two-tiered memory-mapped `.ixpack` +
//! 256-shard loose object store with an in-memory hot cache).

use ix_common::address::Address;
pub use ix_common::store::{IxStore, ObjectKind, StoreError, StoreResult, StoreStats};

/// Handle for reading and writing content-addressed objects under `~/.ix/store`.
pub struct Store;

impl Store {
  /// Write bytes to the store and return their address (blake3 hash).
  pub fn write(bytes: &[u8]) -> StoreResult<Address> {
    IxStore::global()?.write(bytes)
  }

  /// Write bytes at an explicit caller-supplied address.
  pub fn write_at(addr: &Address, bytes: &[u8]) -> StoreResult<()> {
    IxStore::global()?.write_at(addr, bytes)
  }

  /// Read bytes from the store given an address.
  pub fn read(addr: &Address) -> StoreResult<Vec<u8>> {
    IxStore::global()?.read(addr)
  }
}
