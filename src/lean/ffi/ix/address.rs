//! Ix.Address build/decode/roundtrip FFI.
//!
//! Address = { hash : ByteArray } - ByteArray wrapper for blake3 Hash

use std::ffi::c_void;

use crate::lean::{
  lean::{lean_alloc_sarray, lean_sarray_cptr},
  lean_sarray_data,
};

/// Build a Ix.Address from a blake3::Hash.
/// Address = { hash : ByteArray } - single field struct, so UNBOXED to ByteArray
pub fn build_address(hash: &blake3::Hash) -> *mut c_void {
  unsafe {
    let bytes = hash.as_bytes();
    let ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let data_ptr = lean_sarray_cptr(ba);
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());
    ba.cast() // Due to unboxing, ByteArray IS the Address
  }
}

/// Round-trip an Ix.Address: decode ByteArray, re-encode.
/// Address = { hash : ByteArray } - single field struct, so UNBOXED to ByteArray directly
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_address(
  addr_ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    // Address is a single-field struct { hash : ByteArray }
    // Due to unboxing, addr_ptr IS the ByteArray directly
    let bytes = lean_sarray_data(addr_ptr);

    // Rebuild ByteArray - this IS the Address due to unboxing
    let new_ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let data_ptr = lean_sarray_cptr(new_ba);
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());
    new_ba.cast()
  }
}
