//! Ix.Address build/decode/roundtrip FFI.
//!
//! Address = { hash : ByteArray } - ByteArray wrapper for blake3 Hash

use crate::lean::LeanIxAddress;
use lean_sys::object::LeanByteArray;

/// Build a Ix.Address from a blake3::Hash.
/// Address = { hash : ByteArray } - single field struct, so UNBOXED to ByteArray
pub fn build_address(hash: &blake3::Hash) -> LeanIxAddress {
  LeanByteArray::from_bytes(hash.as_bytes())
}

/// Round-trip an Ix.Address: decode ByteArray, re-encode.
/// Address = { hash : ByteArray } - single field struct, so UNBOXED to ByteArray directly
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_address(
  addr: LeanIxAddress,
) -> LeanIxAddress {
  // Address is a single-field struct { hash : ByteArray }
  // Due to unboxing, addr IS the ByteArray directly
  LeanByteArray::from_bytes(addr.as_bytes())
}
