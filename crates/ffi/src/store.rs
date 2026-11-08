//! Lean FFI bindings for `ix_common::store::IxStore`.
//!
//! Unifies Lean's `Ix/Store.lean` with the Rust `IxStore` engine (in-process
//! `DashMap` hot cache + memory-mapped `.ixpack`/`.ixidx` packfiles + 1-level
//! sharded loose objects).

use ix_common::address::Address;
use ix_common::store::IxStore;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanProd,
  LeanString,
};

use crate::lean::LeanStoreStats;

fn decode_addr(
  ba: &LeanByteArray<LeanBorrowed<'_>>,
) -> Result<Address, String> {
  Address::from_slice(ba.as_bytes())
    .map_err(|e| format!("invalid 32-byte Store Address: {e}"))
}

/// `Store.rootDirFFI : IO String`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_root() -> LeanIOResult<LeanOwned> {
  match IxStore::global() {
    Ok(store) => LeanIOResult::ok(LeanString::new(
      &store.root().to_string_lossy(),
    )),
    Err(e) => LeanIOResult::error_string(&format!("rs_store_root: {e}")),
  }
}

/// `Store.containsFFI : @& Address → IO Bool`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_contains(
  addr: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let addr = match decode_addr(&addr) {
    Ok(a) => a,
    Err(e) => return LeanIOResult::error_string(&e),
  };
  match IxStore::global() {
    Ok(store) => {
      let exists = store.contains(&addr);
      LeanIOResult::ok(LeanOwned::box_usize(usize::from(exists)))
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_store_contains: {e}")),
  }
}

/// `Store.writeFFI : @& ByteArray → IO Address`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_write(
  bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => return LeanIOResult::error_string(&format!("rs_store_write: {e}")),
  };
  match store.write(bytes.as_bytes()) {
    Ok(addr) => LeanIOResult::ok(LeanByteArray::from_bytes(addr.as_bytes())),
    Err(e) => LeanIOResult::error_string(&format!("rs_store_write: {e}")),
  }
}

/// `Store.writeAtFFI : @& Address → @& ByteArray → IO Unit`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_write_at(
  addr: LeanByteArray<LeanBorrowed<'_>>,
  bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let addr = match decode_addr(&addr) {
    Ok(a) => a,
    Err(e) => return LeanIOResult::error_string(&e),
  };
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_store_write_at: {e}"));
    },
  };
  match store.write_at(&addr, bytes.as_bytes()) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&format!("rs_store_write_at: {e}")),
  }
}

/// `Store.writePackFFI : @& Array (Address × ByteArray) → IO (Address × UInt64)`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_write_pack(
  entries: LeanArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_store_write_pack: {e}"));
    },
  };
  let mut decoded: Vec<(Address, Vec<u8>)> = Vec::with_capacity(entries.len());
  for i in 0..entries.len() {
    let elem = entries.get(i);
    let pair = elem.as_ctor();
    let addr_ba = pair.get(0).as_byte_array();
    let bytes_ba = pair.get(1).as_byte_array();
    let addr = match Address::from_slice(addr_ba.as_bytes()) {
      Ok(a) => a,
      Err(e) => {
        return LeanIOResult::error_string(&format!(
          "rs_store_write_pack: entry {i} invalid address: {e}"
        ));
      },
    };
    decoded.push((addr, bytes_ba.as_bytes().to_vec()));
  }
  match store.write_pack(
    decoded
      .iter()
      .map(|(a, b)| (a.clone(), b.as_slice(), ix_common::store::ObjectKind::Raw)),
  ) {
    Ok((pack_id, written)) => {
      let pack_ba = LeanByteArray::from_bytes(pack_id.as_bytes());
      let count_box = LeanOwned::box_u64(written as u64);
      LeanIOResult::ok(LeanProd::new(pack_ba, count_box))
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_store_write_pack: {e}")),
  }
}

/// `Store.readFFI : @& Address → IO ByteArray`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_read(
  addr: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let addr = match decode_addr(&addr) {
    Ok(a) => a,
    Err(e) => return LeanIOResult::error_string(&e),
  };
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => return LeanIOResult::error_string(&format!("rs_store_read: {e}")),
  };
  match store.read(&addr) {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
    Err(e) => LeanIOResult::error_string(&format!(
      "unknown address {}: {e}",
      addr.hex()
    )),
  }
}

/// `Store.readVerifiedFFI : @& Address → IO ByteArray`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_read_verified(
  addr: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let addr = match decode_addr(&addr) {
    Ok(a) => a,
    Err(e) => return LeanIOResult::error_string(&e),
  };
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_store_read_verified: {e}"));
    },
  };
  match store.read_verified(&addr) {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(&bytes)),
    Err(e) => LeanIOResult::error_string(&format!(
      "verified read failed for {}: {e}",
      addr.hex()
    )),
  }
}

/// `Store.compactFFI : IO (UInt64 × UInt64)`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_compact() -> LeanIOResult<LeanOwned> {
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_store_compact: {e}"));
    },
  };
  match store.compact() {
    Ok((packed, unlinked)) => {
      let packed_box = LeanOwned::box_u64(packed as u64);
      let unlinked_box = LeanOwned::box_u64(unlinked as u64);
      LeanIOResult::ok(LeanProd::new(packed_box, unlinked_box))
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_store_compact: {e}")),
  }
}

/// `Store.ingestIxeFFI : @& String → IO (Address × UInt64)`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_ingest_ixe(
  path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_store_ingest_ixe: {e}"));
    },
  };
  let path_str = path.as_str();
  match store.ingest_ixe(std::path::Path::new(path_str)) {
    Ok((env_root, count)) => {
      let root_ba = LeanByteArray::from_bytes(env_root.as_bytes());
      let count_box = LeanOwned::box_u64(count as u64);
      LeanIOResult::ok(LeanProd::new(root_ba, count_box))
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_store_ingest_ixe: {e}")),
  }
}

/// `Store.statsFFI : IO StoreStats`
#[unsafe(no_mangle)]
pub extern "C" fn rs_store_stats() -> LeanIOResult<LeanOwned> {
  let store = match IxStore::global() {
    Ok(s) => s,
    Err(e) => {
      return LeanIOResult::error_string(&format!("rs_store_stats: {e}"));
    },
  };
  match store.stats() {
    Ok(s) => {
      let ctor = LeanStoreStats::alloc(0);
      ctor.set_num_64(0, s.hot_cache_objects as u64);
      ctor.set_num_64(1, s.pack_count as u64);
      ctor.set_num_64(2, s.packed_objects as u64);
      ctor.set_num_64(3, s.total_pack_bytes);
      ctor.set_num_64(4, s.loose_objects as u64);
      ctor.set_num_64(5, s.total_loose_bytes);
      LeanIOResult::ok(ctor)
    },
    Err(e) => LeanIOResult::error_string(&format!("rs_store_stats: {e}")),
  }
}
