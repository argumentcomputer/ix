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
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanExcept, LeanOwned, LeanRef,
};

use crate::ffi::builder::LeanBuildCache;
use crate::lean::LeanIxAddress;

// =============================================================================
// RawConst (addr: Address, const: Constant)
// =============================================================================

/// Decoded Ixon.RawConst
pub struct DecodedRawConst {
  pub addr: Address,
  pub constant: IxonConstant,
}

impl LeanIxonRawConst<LeanOwned> {
  /// Build Ixon.RawConst Lean object.
  pub fn build(rc: &DecodedRawConst) -> Self {
    let ctor = LeanIxonRawConst::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(&rc.addr));
    ctor.set_obj(1, LeanIxonConstant::build(&rc.constant));
    ctor
  }

  /// Build from individual parts (used by compile.rs).
  pub fn build_from_parts(addr: &Address, constant: &IxonConstant) -> Self {
    let ctor = LeanIxonRawConst::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(addr));
    ctor.set_obj(1, LeanIxonConstant::build(constant));
    ctor
  }
}

impl<R: LeanRef> LeanIxonRawConst<R> {
  /// Decode Ixon.RawConst from Lean pointer.
  pub fn decode(&self) -> DecodedRawConst {
    let ctor = self.as_ctor();
    DecodedRawConst {
      addr: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      constant: LeanIxonConstant::new(ctor.get(1).to_owned_ref()).decode(),
    }
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

impl LeanIxonRawNamed<LeanOwned> {
  /// Build Ixon.RawNamed Lean object.
  pub fn build(cache: &mut LeanBuildCache, rn: &DecodedRawNamed) -> Self {
    let ctor = LeanIxonRawNamed::alloc(0);
    ctor.set_obj(0, LeanIxName::build(cache, &rn.name));
    ctor.set_obj(1, LeanIxAddress::build(&rn.addr));
    ctor.set_obj(2, LeanIxonConstantMeta::build(&rn.const_meta));
    ctor
  }

  /// Build from individual parts (used by compile.rs).
  pub fn build_from_parts(
    cache: &mut LeanBuildCache,
    name: &Name,
    addr: &Address,
    meta: &ConstantMeta,
  ) -> Self {
    let ctor = LeanIxonRawNamed::alloc(0);
    ctor.set_obj(0, LeanIxName::build(cache, name));
    ctor.set_obj(1, LeanIxAddress::build(addr));
    ctor.set_obj(2, LeanIxonConstantMeta::build(meta));
    ctor
  }
}

impl<R: LeanRef> LeanIxonRawNamed<R> {
  /// Decode Ixon.RawNamed from Lean pointer.
  pub fn decode(&self) -> DecodedRawNamed {
    let ctor = self.as_ctor();
    DecodedRawNamed {
      name: LeanIxName::new(ctor.get(0).to_owned_ref()).decode(),
      addr: LeanIxAddress::from_borrowed(ctor.get(1).as_byte_array()).decode(),
      const_meta: LeanIxonConstantMeta::new(ctor.get(2).to_owned_ref())
        .decode(),
    }
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

impl LeanIxonRawBlob<LeanOwned> {
  /// Build Ixon.RawBlob Lean object.
  pub fn build(rb: &DecodedRawBlob) -> Self {
    let ctor = LeanIxonRawBlob::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(&rb.addr));
    ctor.set_obj(1, LeanByteArray::from_bytes(&rb.bytes));
    ctor
  }

  /// Build from individual parts (used by compile.rs).
  pub fn build_from_parts(addr: &Address, bytes: &[u8]) -> Self {
    let ctor = LeanIxonRawBlob::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(addr));
    ctor.set_obj(1, LeanByteArray::from_bytes(bytes));
    ctor
  }
}

impl<R: LeanRef> LeanIxonRawBlob<R> {
  /// Decode Ixon.RawBlob from Lean pointer.
  pub fn decode(&self) -> DecodedRawBlob {
    let ctor = self.as_ctor();
    let ba = ctor.get(1).as_byte_array();
    DecodedRawBlob {
      addr: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      bytes: ba.as_bytes().to_vec(),
    }
  }
}

// =============================================================================
// RawComm (addr: Address, comm: Comm)
// =============================================================================

/// Decoded Ixon.RawComm
pub struct DecodedRawComm {
  pub addr: Address,
  pub comm: Comm,
}

impl LeanIxonRawComm<LeanOwned> {
  /// Build Ixon.RawComm Lean object.
  pub fn build(rc: &DecodedRawComm) -> Self {
    let ctor = LeanIxonRawComm::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(&rc.addr));
    ctor.set_obj(1, LeanIxonComm::build(&rc.comm));
    ctor
  }

  /// Build from individual parts (used by compile.rs).
  pub fn build_from_parts(addr: &Address, comm: &Comm) -> Self {
    let ctor = LeanIxonRawComm::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(addr));
    ctor.set_obj(1, LeanIxonComm::build(comm));
    ctor
  }
}

impl<R: LeanRef> LeanIxonRawComm<R> {
  /// Decode Ixon.RawComm from Lean pointer.
  pub fn decode(&self) -> DecodedRawComm {
    let ctor = self.as_ctor();
    DecodedRawComm {
      addr: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      comm: LeanIxonComm::new(ctor.get(1).to_owned_ref()).decode(),
    }
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

impl LeanIxonRawNameEntry<LeanOwned> {
  /// Build Ixon.RawNameEntry Lean object.
  pub fn build(
    cache: &mut LeanBuildCache,
    addr: &Address,
    name: &Name,
  ) -> Self {
    let ctor = LeanIxonRawNameEntry::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(addr));
    ctor.set_obj(1, LeanIxName::build(cache, name));
    ctor
  }
}

impl<R: LeanRef> LeanIxonRawNameEntry<R> {
  /// Decode Ixon.RawNameEntry from Lean pointer.
  pub fn decode(&self) -> DecodedRawNameEntry {
    let ctor = self.as_ctor();
    DecodedRawNameEntry {
      addr: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      name: LeanIxName::new(ctor.get(1).to_owned_ref()).decode(),
    }
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

impl LeanIxonRawEnv<LeanOwned> {
  /// Build Ixon.RawEnv Lean object.
  pub fn build(env: &DecodedRawEnv) -> Self {
    let mut cache = LeanBuildCache::new();

    // Build consts array
    let consts_arr = LeanArray::alloc(env.consts.len());
    for (i, rc) in env.consts.iter().enumerate() {
      consts_arr.set(i, LeanIxonRawConst::build(rc));
    }

    // Build named array
    let named_arr = LeanArray::alloc(env.named.len());
    for (i, rn) in env.named.iter().enumerate() {
      named_arr.set(i, LeanIxonRawNamed::build(&mut cache, rn));
    }

    // Build blobs array
    let blobs_arr = LeanArray::alloc(env.blobs.len());
    for (i, rb) in env.blobs.iter().enumerate() {
      blobs_arr.set(i, LeanIxonRawBlob::build(rb));
    }

    // Build comms array
    let comms_arr = LeanArray::alloc(env.comms.len());
    for (i, rc) in env.comms.iter().enumerate() {
      comms_arr.set(i, LeanIxonRawComm::build(rc));
    }

    // Build names array
    let names_arr = LeanArray::alloc(env.names.len());
    for (i, rn) in env.names.iter().enumerate() {
      names_arr
        .set(i, LeanIxonRawNameEntry::build(&mut cache, &rn.addr, &rn.name));
    }

    // Build RawEnv structure
    let ctor = LeanIxonRawEnv::alloc(0);
    ctor.set_obj(0, consts_arr);
    ctor.set_obj(1, named_arr);
    ctor.set_obj(2, blobs_arr);
    ctor.set_obj(3, comms_arr);
    ctor.set_obj(4, names_arr);
    ctor
  }
}

impl<R: LeanRef> LeanIxonRawEnv<R> {
  /// Decode Ixon.RawEnv from Lean pointer.
  pub fn decode(&self) -> DecodedRawEnv {
    let ctor = self.as_ctor();
    let consts_arr = ctor.get(0).as_array();
    let named_arr = ctor.get(1).as_array();
    let blobs_arr = ctor.get(2).as_array();
    let comms_arr = ctor.get(3).as_array();
    let names_arr = ctor.get(4).as_array();

    DecodedRawEnv {
      consts: consts_arr
        .map(|x| LeanIxonRawConst::new(x.to_owned_ref()).decode()),
      named: named_arr
        .map(|x| LeanIxonRawNamed::new(x.to_owned_ref()).decode()),
      blobs: blobs_arr.map(|x| LeanIxonRawBlob::new(x.to_owned_ref()).decode()),
      comms: comms_arr.map(|x| LeanIxonRawComm::new(x.to_owned_ref()).decode()),
      names: names_arr
        .map(|x| LeanIxonRawNameEntry::new(x.to_owned_ref()).decode()),
    }
  }
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
    env.store_comm(rc.addr.clone(), rc.comm.clone());
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
    .map(|e| DecodedRawComm { addr: e.key().clone(), comm: e.value().clone() })
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
pub extern "C" fn rs_ser_env(
  obj: LeanIxonRawEnv<LeanBorrowed<'_>>,
) -> LeanByteArray<LeanOwned> {
  let decoded = obj.decode();
  let env = decoded_to_ixon_env(&decoded);
  let mut buf = Vec::new();
  env.put(&mut buf).expect("Env serialization failed");

  LeanByteArray::from_bytes(&buf)
}

// =============================================================================
// rs_de_env: Deserialize bytes to an Ixon.RawEnv
// =============================================================================

/// FFI: Deserialize ByteArray -> Except String Ixon.RawEnv via Rust's Env.get. Pure.
#[unsafe(no_mangle)]
pub extern "C" fn rs_de_env(
  obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let data = obj.as_bytes();
  let mut slice: &[u8] = data;
  match IxonEnv::get(&mut slice) {
    Ok(env) => {
      let decoded = ixon_env_to_decoded(&env);
      let raw_env = LeanIxonRawEnv::build(&decoded);
      LeanExcept::ok(raw_env)
    },
    Err(e) => {
      let msg = format!("rs_de_env: {}", e);
      LeanExcept::error_string(&msg)
    },
  }
}
