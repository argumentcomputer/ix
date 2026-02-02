//! Ixon.RawEnv FFI build/decode/roundtrip functions.
//!
//! Provides full decode/build cycle for RawEnv and its component types:
//! RawConst, RawNamed, RawBlob, RawComm.

use std::ffi::c_void;

use crate::ix::address::Address;
use crate::ix::env::Name;
use crate::ix::ixon::constant::Constant as IxonConstant;
use crate::ix::ixon::metadata::ConstantMeta;
use crate::lean::array::LeanArrayObject;
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_alloc_sarray, lean_array_set_core,
  lean_ctor_get, lean_ctor_set, lean_sarray_cptr,
};

use super::constant::{build_address_from_ixon, build_ixon_constant, decode_ixon_address, decode_ixon_constant};
use super::meta::{build_constant_meta, decode_constant_meta};
use crate::lean::ffi::builder::LeanBuildCache;
use crate::lean::ffi::ix::name::{build_name, decode_ix_name};

// =============================================================================
// Comm Type (secret: Address, payload: Address)
// =============================================================================

/// Decoded Ixon.Comm
pub struct DecodedComm {
  pub secret: Address,
  pub payload: Address,
}

/// Decode Ixon.Comm from Lean pointer.
/// Comm = { secret : Address, payload : Address }
pub fn decode_comm(ptr: *const c_void) -> DecodedComm {
  unsafe {
    let secret_ptr = lean_ctor_get(ptr as *mut _, 0);
    let payload_ptr = lean_ctor_get(ptr as *mut _, 1);
    DecodedComm {
      secret: decode_ixon_address(secret_ptr),
      payload: decode_ixon_address(payload_ptr),
    }
  }
}

/// Build Ixon.Comm Lean object.
pub fn build_comm(comm: &DecodedComm) -> *mut c_void {
  unsafe {
    let secret_obj = build_address_from_ixon(&comm.secret);
    let payload_obj = build_address_from_ixon(&comm.payload);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, secret_obj);
    lean_ctor_set(obj, 1, payload_obj);
    obj
  }
}

// =============================================================================
// RawConst (addr: Address, const: Constant)
// =============================================================================

/// Decoded Ixon.RawConst
pub struct DecodedRawConst {
  pub addr: Address,
  pub constant: IxonConstant,
}

/// Decode Ixon.RawConst from Lean pointer.
pub fn decode_raw_const(ptr: *const c_void) -> DecodedRawConst {
  unsafe {
    let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
    let const_ptr = lean_ctor_get(ptr as *mut _, 1);
    DecodedRawConst {
      addr: decode_ixon_address(addr_ptr),
      constant: decode_ixon_constant(const_ptr),
    }
  }
}

/// Build Ixon.RawConst Lean object.
pub fn build_raw_const(rc: &DecodedRawConst) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(&rc.addr);
    let const_obj = build_ixon_constant(&rc.constant);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, const_obj);
    obj
  }
}

// =============================================================================
// RawNamed (name: Ix.Name, addr: Address, constMeta: ConstantMeta)
// =============================================================================

/// Decoded Ixon.RawNamed
pub struct DecodedRawNamed {
  pub name: Name,
  pub addr: Address,
  pub const_meta: ConstantMeta,
}

/// Decode Ixon.RawNamed from Lean pointer.
pub fn decode_raw_named(ptr: *const c_void) -> DecodedRawNamed {
  unsafe {
    let name_ptr = lean_ctor_get(ptr as *mut _, 0);
    let addr_ptr = lean_ctor_get(ptr as *mut _, 1);
    let meta_ptr = lean_ctor_get(ptr as *mut _, 2);
    DecodedRawNamed {
      name: decode_ix_name(name_ptr),
      addr: decode_ixon_address(addr_ptr),
      const_meta: decode_constant_meta(meta_ptr),
    }
  }
}

/// Build Ixon.RawNamed Lean object.
pub fn build_raw_named(cache: &mut LeanBuildCache, rn: &DecodedRawNamed) -> *mut c_void {
  unsafe {
    let name_obj = build_name(cache, &rn.name);
    let addr_obj = build_address_from_ixon(&rn.addr);
    let meta_obj = build_constant_meta(&rn.const_meta);
    let obj = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(obj, 0, name_obj);
    lean_ctor_set(obj, 1, addr_obj);
    lean_ctor_set(obj, 2, meta_obj);
    obj
  }
}

// =============================================================================
// RawBlob (addr: Address, bytes: ByteArray)
// =============================================================================

/// Decoded Ixon.RawBlob
pub struct DecodedRawBlob {
  pub addr: Address,
  pub bytes: Vec<u8>,
}

/// Decode Ixon.RawBlob from Lean pointer.
pub fn decode_raw_blob(ptr: *const c_void) -> DecodedRawBlob {
  unsafe {
    let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
    let bytes_ptr = lean_ctor_get(ptr as *mut _, 1);
    let bytes_arr: &LeanSArrayObject = as_ref_unsafe(bytes_ptr.cast());
    DecodedRawBlob {
      addr: decode_ixon_address(addr_ptr),
      bytes: bytes_arr.data().to_vec(),
    }
  }
}

/// Build Ixon.RawBlob Lean object.
pub fn build_raw_blob(rb: &DecodedRawBlob) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(&rb.addr);
    // Build ByteArray (SArray UInt8)
    let len = rb.bytes.len();
    let bytes_obj = lean_alloc_sarray(1, len, len);
    let data_ptr = lean_sarray_cptr(bytes_obj);
    std::ptr::copy_nonoverlapping(rb.bytes.as_ptr(), data_ptr, len);

    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, bytes_obj);
    obj
  }
}

// =============================================================================
// RawComm (addr: Address, comm: Comm)
// =============================================================================

/// Decoded Ixon.RawComm
pub struct DecodedRawComm {
  pub addr: Address,
  pub comm: DecodedComm,
}

/// Decode Ixon.RawComm from Lean pointer.
pub fn decode_raw_comm(ptr: *const c_void) -> DecodedRawComm {
  unsafe {
    let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
    let comm_ptr = lean_ctor_get(ptr as *mut _, 1);
    DecodedRawComm {
      addr: decode_ixon_address(addr_ptr),
      comm: decode_comm(comm_ptr),
    }
  }
}

/// Build Ixon.RawComm Lean object.
pub fn build_raw_comm(rc: &DecodedRawComm) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(&rc.addr);
    let comm_obj = build_comm(&rc.comm);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, comm_obj);
    obj
  }
}

// =============================================================================
// RawNameEntry (addr: Address, name: Ix.Name)
// =============================================================================

/// Decoded Ixon.RawNameEntry
pub struct DecodedRawNameEntry {
  pub addr: Address,
  pub name: Name,
}

/// Decode Ixon.RawNameEntry from Lean pointer.
pub fn decode_raw_name_entry(ptr: *const c_void) -> DecodedRawNameEntry {
  unsafe {
    let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
    let name_ptr = lean_ctor_get(ptr as *mut _, 1);
    DecodedRawNameEntry {
      addr: decode_ixon_address(addr_ptr),
      name: decode_ix_name(name_ptr),
    }
  }
}

/// Build Ixon.RawNameEntry Lean object.
pub fn build_raw_name_entry(cache: &mut LeanBuildCache, addr: &Address, name: &Name) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(addr);
    let name_obj = build_name(cache, name);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, name_obj);
    obj
  }
}

// =============================================================================
// RawEnv (consts, named, blobs, comms, names)
// =============================================================================

/// Decoded Ixon.RawEnv
pub struct DecodedRawEnv {
  pub consts: Vec<DecodedRawConst>,
  pub named: Vec<DecodedRawNamed>,
  pub blobs: Vec<DecodedRawBlob>,
  pub comms: Vec<DecodedRawComm>,
  pub names: Vec<DecodedRawNameEntry>,
}

/// Decode Ixon.RawEnv from Lean pointer.
pub fn decode_raw_env(ptr: *const c_void) -> DecodedRawEnv {
  unsafe {
    let consts_ptr = lean_ctor_get(ptr as *mut _, 0);
    let named_ptr = lean_ctor_get(ptr as *mut _, 1);
    let blobs_ptr = lean_ctor_get(ptr as *mut _, 2);
    let comms_ptr = lean_ctor_get(ptr as *mut _, 3);
    let names_ptr = lean_ctor_get(ptr as *mut _, 4);

    let consts_arr: &LeanArrayObject = as_ref_unsafe(consts_ptr.cast());
    let named_arr: &LeanArrayObject = as_ref_unsafe(named_ptr.cast());
    let blobs_arr: &LeanArrayObject = as_ref_unsafe(blobs_ptr.cast());
    let comms_arr: &LeanArrayObject = as_ref_unsafe(comms_ptr.cast());
    let names_arr: &LeanArrayObject = as_ref_unsafe(names_ptr.cast());

    DecodedRawEnv {
      consts: consts_arr.to_vec(decode_raw_const),
      named: named_arr.to_vec(decode_raw_named),
      blobs: blobs_arr.to_vec(decode_raw_blob),
      comms: comms_arr.to_vec(decode_raw_comm),
      names: names_arr.to_vec(decode_raw_name_entry),
    }
  }
}

/// Build Ixon.RawEnv Lean object.
pub fn build_raw_env(env: &DecodedRawEnv) -> *mut c_void {
  unsafe {
    let mut cache = LeanBuildCache::new();

    // Build consts array
    let consts_arr = lean_alloc_array(env.consts.len(), env.consts.len());
    for (i, rc) in env.consts.iter().enumerate() {
      let obj = build_raw_const(rc);
      lean_array_set_core(consts_arr, i, obj);
    }

    // Build named array
    let named_arr = lean_alloc_array(env.named.len(), env.named.len());
    for (i, rn) in env.named.iter().enumerate() {
      let obj = build_raw_named(&mut cache, rn);
      lean_array_set_core(named_arr, i, obj);
    }

    // Build blobs array
    let blobs_arr = lean_alloc_array(env.blobs.len(), env.blobs.len());
    for (i, rb) in env.blobs.iter().enumerate() {
      let obj = build_raw_blob(rb);
      lean_array_set_core(blobs_arr, i, obj);
    }

    // Build comms array
    let comms_arr = lean_alloc_array(env.comms.len(), env.comms.len());
    for (i, rc) in env.comms.iter().enumerate() {
      let obj = build_raw_comm(rc);
      lean_array_set_core(comms_arr, i, obj);
    }

    // Build names array
    let names_arr = lean_alloc_array(env.names.len(), env.names.len());
    for (i, rn) in env.names.iter().enumerate() {
      let obj = build_raw_name_entry(&mut cache, &rn.addr, &rn.name);
      lean_array_set_core(names_arr, i, obj);
    }

    // Build RawEnv structure
    let obj = lean_alloc_ctor(0, 5, 0);
    lean_ctor_set(obj, 0, consts_arr);
    lean_ctor_set(obj, 1, named_arr);
    lean_ctor_set(obj, 2, blobs_arr);
    lean_ctor_set(obj, 3, comms_arr);
    lean_ctor_set(obj, 4, names_arr);
    obj
  }
}

