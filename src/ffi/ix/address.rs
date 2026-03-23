//! Ix.Address build/decode/roundtrip FFI.
//!
//! Address = { hash : ByteArray } - ByteArray wrapper for blake3 Hash

use crate::ix::address::Address;
use crate::lean::LeanIxAddress;
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanByteArray, LeanOwned};

impl LeanIxAddress<LeanOwned> {
  /// Build an Ix.Address from a blake3::Hash.
  pub fn build_from_hash(hash: &blake3::Hash) -> Self {
    LeanByteArray::from_bytes(hash.as_bytes()).into()
  }

  /// Build an Ix.Address from an Ixon Address (which is just a [u8; 32]).
  pub fn build(addr: &Address) -> Self {
    LeanByteArray::from_bytes(addr.as_bytes()).into()
  }

  /// Build an Array of Addresses.
  pub fn build_array(addrs: &[Address]) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(addrs.len());
    for (i, addr) in addrs.iter().enumerate() {
      arr.set(i, Self::build(addr));
    }
    arr
  }
}

impl<R: lean_ffi::object::LeanRef> LeanIxAddress<R> {
  /// Decode a ByteArray (Address) to Address.
  pub fn decode(&self) -> Address {
    Address::from_slice(&self.as_bytes()[..32])
      .expect("Address should be 32 bytes")
  }
}

impl LeanIxAddress<LeanBorrowed<'_>> {
  /// Decode Array Address.
  pub fn decode_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<Address> {
    obj.map(|x| LeanIxAddress::from_borrowed(x.as_byte_array()).decode())
  }
}

/// Round-trip an Ix.Address: decode ByteArray, re-encode.
/// Address = { hash : ByteArray } - single field struct, so UNBOXED to ByteArray directly
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_address(
  addr: LeanIxAddress<LeanBorrowed<'_>>,
) -> LeanIxAddress<LeanOwned> {
  let decoded = addr.decode();
  LeanIxAddress::build(&decoded)
}
