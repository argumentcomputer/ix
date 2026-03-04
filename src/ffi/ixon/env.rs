//! Ixon.RawEnv FFI build/decode/roundtrip functions.
//!
//! Provides full decode/build cycle for RawEnv and its component types:
//! RawConst, RawNamed, RawBlob, RawComm.

use crate::ix::address::Address;
use crate::ix::env::Name;
use crate::ix::ixon::comm::Comm;
use crate::ix::ixon::constant::Constant as IxonConstant;
use crate::ix::ixon::env::{Env as IxonEnv, Named as IxonNamed};
use crate::ix::ixon::metadata::ConstantMeta;
use crate::lean::{
  LeanIxName, LeanIxonComm, LeanIxonConstant, LeanIxonConstantMeta,
  LeanIxonRawBlob, LeanIxonRawComm, LeanIxonRawConst, LeanIxonRawEnv,
  LeanIxonRawNameEntry, LeanIxonRawNamed,
};
use lean_ffi::object::{LeanArray, LeanByteArray, LeanCtor, LeanExcept};

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::ix::name::{build_name, decode_ix_name};
use crate::ffi::ixon::constant::{
  build_address_from_ixon, build_ixon_constant, decode_ixon_address,
  decode_ixon_constant,
};
use crate::ffi::ixon::meta::{build_constant_meta, decode_constant_meta};

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
pub fn decode_comm(obj: LeanIxonComm) -> DecodedComm {
  let ctor = obj.as_ctor();
  DecodedComm {
    secret: decode_ixon_address(ctor.get(0).as_byte_array()),
    payload: decode_ixon_address(ctor.get(1).as_byte_array()),
  }
}

/// Build Ixon.Comm Lean object.
pub fn build_comm(comm: &DecodedComm) -> LeanIxonComm {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(&comm.secret));
  ctor.set(1, build_address_from_ixon(&comm.payload));
  LeanIxonComm::new(*ctor)
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
pub fn decode_raw_const(obj: LeanIxonRawConst) -> DecodedRawConst {
  let ctor = obj.as_ctor();
  DecodedRawConst {
    addr: decode_ixon_address(ctor.get(0).as_byte_array()),
    constant: decode_ixon_constant(LeanIxonConstant::new(ctor.get(1))),
  }
}

/// Build Ixon.RawConst Lean object.
pub fn build_raw_const(rc: &DecodedRawConst) -> LeanIxonRawConst {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(&rc.addr));
  ctor.set(1, build_ixon_constant(&rc.constant));
  LeanIxonRawConst::new(*ctor)
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
pub fn decode_raw_named(obj: LeanIxonRawNamed) -> DecodedRawNamed {
  let ctor = obj.as_ctor();
  DecodedRawNamed {
    name: decode_ix_name(LeanIxName::new(ctor.get(0))),
    addr: decode_ixon_address(ctor.get(1).as_byte_array()),
    const_meta: decode_constant_meta(LeanIxonConstantMeta::new(ctor.get(2))),
  }
}

/// Build Ixon.RawNamed Lean object.
pub fn build_raw_named(
  cache: &mut LeanBuildCache,
  rn: &DecodedRawNamed,
) -> LeanIxonRawNamed {
  let ctor = LeanCtor::alloc(0, 3, 0);
  ctor.set(0, build_name(cache, &rn.name));
  ctor.set(1, build_address_from_ixon(&rn.addr));
  ctor.set(2, build_constant_meta(&rn.const_meta));
  LeanIxonRawNamed::new(*ctor)
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
pub fn decode_raw_blob(obj: LeanIxonRawBlob) -> DecodedRawBlob {
  let ctor = obj.as_ctor();
  let ba = ctor.get(1).as_byte_array();
  DecodedRawBlob {
    addr: decode_ixon_address(ctor.get(0).as_byte_array()),
    bytes: ba.as_bytes().to_vec(),
  }
}

/// Build Ixon.RawBlob Lean object.
pub fn build_raw_blob(rb: &DecodedRawBlob) -> LeanIxonRawBlob {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(&rb.addr));
  ctor.set(1, LeanByteArray::from_bytes(&rb.bytes));
  LeanIxonRawBlob::new(*ctor)
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
pub fn decode_raw_comm(obj: LeanIxonRawComm) -> DecodedRawComm {
  let ctor = obj.as_ctor();
  DecodedRawComm {
    addr: decode_ixon_address(ctor.get(0).as_byte_array()),
    comm: decode_comm(LeanIxonComm::new(ctor.get(1))),
  }
}

/// Build Ixon.RawComm Lean object.
pub fn build_raw_comm(rc: &DecodedRawComm) -> LeanIxonRawComm {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(&rc.addr));
  ctor.set(1, build_comm(&rc.comm));
  LeanIxonRawComm::new(*ctor)
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
pub fn decode_raw_name_entry(obj: LeanIxonRawNameEntry) -> DecodedRawNameEntry {
  let ctor = obj.as_ctor();
  DecodedRawNameEntry {
    addr: decode_ixon_address(ctor.get(0).as_byte_array()),
    name: decode_ix_name(LeanIxName::new(ctor.get(1))),
  }
}

/// Build Ixon.RawNameEntry Lean object.
pub fn build_raw_name_entry(
  cache: &mut LeanBuildCache,
  addr: &Address,
  name: &Name,
) -> LeanIxonRawNameEntry {
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, build_address_from_ixon(addr));
  ctor.set(1, build_name(cache, name));
  LeanIxonRawNameEntry::new(*ctor)
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
pub fn decode_raw_env(obj: LeanIxonRawEnv) -> DecodedRawEnv {
  let ctor = obj.as_ctor();
  let consts_arr = ctor.get(0).as_array();
  let named_arr = ctor.get(1).as_array();
  let blobs_arr = ctor.get(2).as_array();
  let comms_arr = ctor.get(3).as_array();
  let names_arr = ctor.get(4).as_array();

  DecodedRawEnv {
    consts: consts_arr.map(|x| decode_raw_const(LeanIxonRawConst::new(x))),
    named: named_arr.map(|x| decode_raw_named(LeanIxonRawNamed::new(x))),
    blobs: blobs_arr.map(|x| decode_raw_blob(LeanIxonRawBlob::new(x))),
    comms: comms_arr.map(|x| decode_raw_comm(LeanIxonRawComm::new(x))),
    names: names_arr
      .map(|x| decode_raw_name_entry(LeanIxonRawNameEntry::new(x))),
  }
}

/// Build Ixon.RawEnv Lean object.
pub fn build_raw_env(env: &DecodedRawEnv) -> LeanIxonRawEnv {
  let mut cache = LeanBuildCache::new();

  // Build consts array
  let consts_arr = LeanArray::alloc(env.consts.len());
  for (i, rc) in env.consts.iter().enumerate() {
    consts_arr.set(i, build_raw_const(rc));
  }

  // Build named array
  let named_arr = LeanArray::alloc(env.named.len());
  for (i, rn) in env.named.iter().enumerate() {
    named_arr.set(i, build_raw_named(&mut cache, rn));
  }

  // Build blobs array
  let blobs_arr = LeanArray::alloc(env.blobs.len());
  for (i, rb) in env.blobs.iter().enumerate() {
    blobs_arr.set(i, build_raw_blob(rb));
  }

  // Build comms array
  let comms_arr = LeanArray::alloc(env.comms.len());
  for (i, rc) in env.comms.iter().enumerate() {
    comms_arr.set(i, build_raw_comm(rc));
  }

  // Build names array
  let names_arr = LeanArray::alloc(env.names.len());
  for (i, rn) in env.names.iter().enumerate() {
    names_arr.set(i, build_raw_name_entry(&mut cache, &rn.addr, &rn.name));
  }

  // Build RawEnv structure
  let ctor = LeanCtor::alloc(0, 5, 0);
  ctor.set(0, consts_arr);
  ctor.set(1, named_arr);
  ctor.set(2, blobs_arr);
  ctor.set(3, comms_arr);
  ctor.set(4, names_arr);
  LeanIxonRawEnv::new(*ctor)
}

// =============================================================================
// DecodedRawEnv <-> IxonEnv Conversion Helpers
// =============================================================================

/// Reconstruct a Rust IxonEnv from a DecodedRawEnv.
pub fn decoded_to_ixon_env(decoded: &DecodedRawEnv) -> IxonEnv {
  let env = IxonEnv::new();
  for rc in &decoded.consts {
    env.store_const(rc.addr.clone(), rc.constant.clone());
  }
  for rn in &decoded.names {
    env.store_name(rn.addr.clone(), rn.name.clone());
  }
  for rn in &decoded.named {
    let named = IxonNamed::new(rn.addr.clone(), rn.const_meta.clone());
    env.register_name(rn.name.clone(), named);
  }
  for rb in &decoded.blobs {
    env.blobs.insert(rb.addr.clone(), rb.bytes.clone());
  }
  for rc in &decoded.comms {
    let comm =
      Comm { secret: rc.comm.secret.clone(), payload: rc.comm.payload.clone() };
    env.store_comm(rc.addr.clone(), comm);
  }
  env
}

/// Convert a Rust IxonEnv to a DecodedRawEnv.
pub fn ixon_env_to_decoded(env: &IxonEnv) -> DecodedRawEnv {
  let consts = env
    .consts
    .iter()
    .map(|e| DecodedRawConst {
      addr: e.key().clone(),
      constant: e.value().clone(),
    })
    .collect();
  let named = env
    .named
    .iter()
    .map(|e| DecodedRawNamed {
      name: e.key().clone(),
      addr: e.value().addr.clone(),
      const_meta: e.value().meta.clone(),
    })
    .collect();
  let blobs = env
    .blobs
    .iter()
    .map(|e| DecodedRawBlob { addr: e.key().clone(), bytes: e.value().clone() })
    .collect();
  let comms = env
    .comms
    .iter()
    .map(|e| DecodedRawComm {
      addr: e.key().clone(),
      comm: DecodedComm {
        secret: e.value().secret.clone(),
        payload: e.value().payload.clone(),
      },
    })
    .collect();
  let names = env
    .names
    .iter()
    .map(|e| DecodedRawNameEntry {
      addr: e.key().clone(),
      name: e.value().clone(),
    })
    .collect();
  DecodedRawEnv { consts, named, blobs, comms, names }
}

// =============================================================================
// rs_ser_env: Serialize an Ixon.RawEnv to bytes
// =============================================================================

/// FFI: Serialize an Ixon.RawEnv -> ByteArray via Rust's Env.put. Pure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_ser_env(obj: LeanIxonRawEnv) -> LeanByteArray {
  let decoded = decode_raw_env(obj);
  let env = decoded_to_ixon_env(&decoded);
  let mut buf = Vec::new();
  env.put(&mut buf).expect("Env serialization failed");

  LeanByteArray::from_bytes(&buf)
}

// =============================================================================
// rs_des_env: Deserialize bytes to an Ixon.RawEnv
// =============================================================================

/// FFI: Deserialize ByteArray -> Except String Ixon.RawEnv via Rust's Env.get. Pure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_des_env(obj: LeanByteArray) -> LeanExcept {
  let data = obj.as_bytes();
  let mut slice: &[u8] = data;
  match IxonEnv::get(&mut slice) {
    Ok(env) => {
      let decoded = ixon_env_to_decoded(&env);
      let raw_env = build_raw_env(&decoded);
      LeanExcept::ok(raw_env)
    },
    Err(e) => {
      let msg = format!("rs_des_env: {}", e);
      LeanExcept::error_string(&msg)
    },
  }
}
