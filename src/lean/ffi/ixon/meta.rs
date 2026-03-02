//! Ixon metadata types build/decode/roundtrip FFI.
//!
//! Includes: DataValue, KVMap, ExprMetaData, ExprMetaArena, ConstantMeta, Named, Comm

use crate::ix::address::Address;
use crate::ix::env::BinderInfo;
use crate::ix::ixon::Comm;
use crate::ix::ixon::env::Named;
use crate::ix::ixon::metadata::{
  ConstantMeta, DataValue, ExprMeta, ExprMetaData, KVMap,
};
use crate::lean::obj::{
  IxAddress, IxonComm, IxonConstantMeta, IxonDataValue, IxonExprMetaArena,
  IxonExprMetaData, IxonNamed, LeanArray, LeanCtor, LeanObj,
};

use super::constant::*;
use crate::lean::ffi::ix::constant::{
  build_reducibility_hints, decode_reducibility_hints,
};
use crate::lean::ffi::ix::expr::binder_info_to_u8;

// =============================================================================
// DataValue Build/Decode
// =============================================================================

impl IxonDataValue {
  /// Build Ixon.DataValue (for metadata)
  pub fn build(dv: &DataValue) -> Self {
    let obj = match dv {
      DataValue::OfString(addr) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, IxAddress::build_from_ixon(addr));
        *ctor
      },
      DataValue::OfBool(b) => {
        let ctor = LeanCtor::alloc(1, 0, 1);
        ctor.set_u8(0, if *b { 1 } else { 0 });
        *ctor
      },
      DataValue::OfName(addr) => {
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, IxAddress::build_from_ixon(addr));
        *ctor
      },
      DataValue::OfNat(addr) => {
        let ctor = LeanCtor::alloc(3, 1, 0);
        ctor.set(0, IxAddress::build_from_ixon(addr));
        *ctor
      },
      DataValue::OfInt(addr) => {
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, IxAddress::build_from_ixon(addr));
        *ctor
      },
      DataValue::OfSyntax(addr) => {
        let ctor = LeanCtor::alloc(5, 1, 0);
        ctor.set(0, IxAddress::build_from_ixon(addr));
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.DataValue.
  pub fn decode(self) -> DataValue {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    match ctor.tag() {
      0 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        DataValue::OfString(ba.decode_ixon())
      },
      1 => {
        let b = ctor.scalar_u8(0, 0) != 0;
        DataValue::OfBool(b)
      },
      2 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        DataValue::OfName(ba.decode_ixon())
      },
      3 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        DataValue::OfNat(ba.decode_ixon())
      },
      4 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        DataValue::OfInt(ba.decode_ixon())
      },
      5 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        DataValue::OfSyntax(ba.decode_ixon())
      },
      tag => panic!("Invalid Ixon.DataValue tag: {tag}"),
    }
  }
}

// =============================================================================
// KVMap Build/Decode
// =============================================================================

/// Build an Ixon.KVMap (Array (Address × DataValue)).
pub fn build_ixon_kvmap(kvmap: &KVMap) -> LeanArray {
  let arr = LeanArray::alloc(kvmap.len());
  for (i, (addr, dv)) in kvmap.iter().enumerate() {
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, IxAddress::build_from_ixon(addr));
    pair.set(1, IxonDataValue::build(dv));
    arr.set(i, pair);
  }
  arr
}

/// Build Array KVMap.
pub fn build_kvmap_array(kvmaps: &[KVMap]) -> LeanArray {
  let arr = LeanArray::alloc(kvmaps.len());
  for (i, kvmap) in kvmaps.iter().enumerate() {
    arr.set(i, build_ixon_kvmap(kvmap));
  }
  arr
}

/// Decode KVMap (Array (Address × DataValue)).
pub fn decode_ixon_kvmap(obj: LeanObj) -> KVMap {
  let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
  arr.map(|pair| {
    let pair_ctor = unsafe { LeanCtor::from_raw(pair.as_ptr()) };
    let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(pair_ctor.get(0).as_ptr()) };
    (
      ba.decode_ixon(),
      IxonDataValue::new(pair_ctor.get(1)).decode(),
    )
  })
}

/// Decode Array KVMap.
fn decode_kvmap_array(obj: LeanObj) -> Vec<KVMap> {
  let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
  arr.map(decode_ixon_kvmap)
}

// =============================================================================
// Address Array Helpers
// =============================================================================

/// Decode Array Address.
fn decode_address_array(obj: LeanObj) -> Vec<Address> {
  IxAddress::decode_array(obj)
}

/// Build Array UInt64.
fn build_u64_array(vals: &[u64]) -> LeanArray {
  let arr = LeanArray::alloc(vals.len());
  for (i, &v) in vals.iter().enumerate() {
    arr.set(i, LeanObj::box_u64(v));
  }
  arr
}

/// Decode Array UInt64.
fn decode_u64_array(obj: LeanObj) -> Vec<u64> {
  let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
  arr.map(|elem| elem.unbox_u64())
}

// =============================================================================
// ExprMetaData Build/Decode
// =============================================================================

impl IxonExprMetaData {
  /// Build Ixon.ExprMetaData Lean object.
  pub fn build(node: &ExprMetaData) -> Self {
    let obj = match node {
      ExprMetaData::Leaf => LeanObj::box_usize(0),

      ExprMetaData::App { children } => {
        let ctor = LeanCtor::alloc(1, 0, 16);
        ctor.set_u64(0, children[0]);
        ctor.set_u64(8, children[1]);
        *ctor
      },

      ExprMetaData::Binder { name, info, children } => {
        let ctor = LeanCtor::alloc(2, 1, 17);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set_u64(8, children[0]);
        ctor.set_u64(8 + 8, children[1]);
        ctor.set_u8(8 + 16, binder_info_to_u8(info));
        *ctor
      },

      ExprMetaData::LetBinder { name, children } => {
        let ctor = LeanCtor::alloc(3, 1, 24);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set_u64(8, children[0]);
        ctor.set_u64(8 + 8, children[1]);
        ctor.set_u64(8 + 16, children[2]);
        *ctor
      },

      ExprMetaData::Ref { name } => {
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, IxAddress::build_from_ixon(name));
        *ctor
      },

      ExprMetaData::Prj { struct_name, child } => {
        let ctor = LeanCtor::alloc(5, 1, 8);
        ctor.set(0, IxAddress::build_from_ixon(struct_name));
        ctor.set_u64(8, *child);
        *ctor
      },

      ExprMetaData::Mdata { mdata, child } => {
        let ctor = LeanCtor::alloc(6, 1, 8);
        ctor.set(0, build_kvmap_array(mdata));
        ctor.set_u64(8, *child);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.ExprMetaData from Lean pointer.
  pub fn decode(self) -> ExprMetaData {
    let obj: LeanObj = *self;
    if obj.is_scalar() {
      let tag = obj.unbox_usize();
      assert_eq!(tag, 0, "Invalid scalar ExprMetaData tag: {tag}");
      return ExprMetaData::Leaf;
    }
    let ctor = unsafe { LeanCtor::from_raw(obj.as_ptr()) };
    match ctor.tag() {
      1 => {
        let fun_ = ctor.scalar_u64(0, 0);
        let arg = ctor.scalar_u64(0, 8);
        ExprMetaData::App { children: [fun_, arg] }
      },

      2 => {
        let ty_child = ctor.scalar_u64(1, 0);
        let body_child = ctor.scalar_u64(1, 8);
        let info_byte = ctor.scalar_u8(1, 16);
        let info = match info_byte {
          0 => BinderInfo::Default,
          1 => BinderInfo::Implicit,
          2 => BinderInfo::StrictImplicit,
          3 => BinderInfo::InstImplicit,
          _ => panic!("Invalid BinderInfo tag: {info_byte}"),
        };
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        ExprMetaData::Binder {
          name: ba.decode_ixon(),
          info,
          children: [ty_child, body_child],
        }
      },

      3 => {
        let ty_child = ctor.scalar_u64(1, 0);
        let val_child = ctor.scalar_u64(1, 8);
        let body_child = ctor.scalar_u64(1, 16);
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        ExprMetaData::LetBinder {
          name: ba.decode_ixon(),
          children: [ty_child, val_child, body_child],
        }
      },

      4 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        ExprMetaData::Ref { name: ba.decode_ixon() }
      },

      5 => {
        let child = ctor.scalar_u64(1, 0);
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        ExprMetaData::Prj {
          struct_name: ba.decode_ixon(),
          child,
        }
      },

      6 => {
        let child = ctor.scalar_u64(1, 0);
        ExprMetaData::Mdata {
          mdata: decode_kvmap_array(ctor.get(0)),
          child,
        }
      },

      tag => panic!("Invalid Ixon.ExprMetaData tag: {tag}"),
    }
  }
}

// =============================================================================
// ExprMetaArena Build/Decode
// =============================================================================

impl IxonExprMetaArena {
  /// Build Ixon.ExprMetaArena Lean object.
  /// ExprMetaArena is a single-field structure (nodes : Array ExprMetaData),
  /// which Lean unboxes — the value IS the Array directly.
  pub fn build(arena: &ExprMeta) -> LeanArray {
    let arr = LeanArray::alloc(arena.nodes.len());
    for (i, node) in arena.nodes.iter().enumerate() {
      arr.set(i, IxonExprMetaData::build(node));
    }
    arr
  }

  /// Decode Ixon.ExprMetaArena from Lean pointer.
  /// Single-field struct is unboxed — obj IS the Array directly.
  pub fn decode(obj: LeanObj) -> ExprMeta {
    let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
    ExprMeta { nodes: arr.map(|n| IxonExprMetaData::new(n).decode()) }
  }
}

// =============================================================================
// ConstantMeta Build/Decode
// =============================================================================

impl IxonConstantMeta {
  /// Build Ixon.ConstantMeta Lean object.
  pub fn build(meta: &ConstantMeta) -> Self {
    let obj = match meta {
      ConstantMeta::Empty => LeanObj::box_usize(0),

      ConstantMeta::Def {
        name,
        lvls,
        hints,
        all,
        ctx,
        arena,
        type_root,
        value_root,
      } => {
        let ctor = LeanCtor::alloc(1, 6, 16);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set(1, IxAddress::build_array(lvls));
        ctor.set(2, build_reducibility_hints(hints));
        ctor.set(3, IxAddress::build_array(all));
        ctor.set(4, IxAddress::build_array(ctx));
        ctor.set(5, IxonExprMetaArena::build(arena));
        ctor.set_u64(6 * 8, *type_root);
        ctor.set_u64(6 * 8 + 8, *value_root);
        *ctor
      },

      ConstantMeta::Axio { name, lvls, arena, type_root } => {
        let ctor = LeanCtor::alloc(2, 3, 8);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set(1, IxAddress::build_array(lvls));
        ctor.set(2, IxonExprMetaArena::build(arena));
        ctor.set_u64(3 * 8, *type_root);
        *ctor
      },

      ConstantMeta::Quot { name, lvls, arena, type_root } => {
        let ctor = LeanCtor::alloc(3, 3, 8);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set(1, IxAddress::build_array(lvls));
        ctor.set(2, IxonExprMetaArena::build(arena));
        ctor.set_u64(3 * 8, *type_root);
        *ctor
      },

      ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        let ctor = LeanCtor::alloc(4, 6, 8);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set(1, IxAddress::build_array(lvls));
        ctor.set(2, IxAddress::build_array(ctors));
        ctor.set(3, IxAddress::build_array(all));
        ctor.set(4, IxAddress::build_array(ctx));
        ctor.set(5, IxonExprMetaArena::build(arena));
        ctor.set_u64(6 * 8, *type_root);
        *ctor
      },

      ConstantMeta::Ctor { name, lvls, induct, arena, type_root } => {
        let ctor = LeanCtor::alloc(5, 4, 8);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set(1, IxAddress::build_array(lvls));
        ctor.set(2, IxAddress::build_from_ixon(induct));
        ctor.set(3, IxonExprMetaArena::build(arena));
        ctor.set_u64(4 * 8, *type_root);
        *ctor
      },

      ConstantMeta::Rec {
        name,
        lvls,
        rules,
        all,
        ctx,
        arena,
        type_root,
        rule_roots,
      } => {
        let ctor = LeanCtor::alloc(6, 7, 8);
        ctor.set(0, IxAddress::build_from_ixon(name));
        ctor.set(1, IxAddress::build_array(lvls));
        ctor.set(2, IxAddress::build_array(rules));
        ctor.set(3, IxAddress::build_array(all));
        ctor.set(4, IxAddress::build_array(ctx));
        ctor.set(5, IxonExprMetaArena::build(arena));
        ctor.set(6, build_u64_array(rule_roots));
        ctor.set_u64(7 * 8, *type_root);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.ConstantMeta from Lean pointer.
  pub fn decode(self) -> ConstantMeta {
    let obj: LeanObj = *self;
    if obj.is_scalar() {
      let tag = obj.unbox_usize();
      assert_eq!(tag, 0, "Invalid scalar ConstantMeta tag: {tag}");
      return ConstantMeta::Empty;
    }
    let ctor = unsafe { LeanCtor::from_raw(obj.as_ptr()) };
    match ctor.tag() {
      1 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        let name = ba.decode_ixon();
        let lvls = decode_address_array(ctor.get(1));
        let hints = decode_reducibility_hints(ctor.get(2).as_ptr());
        let all = decode_address_array(ctor.get(3));
        let ctx = decode_address_array(ctor.get(4));
        let arena = IxonExprMetaArena::decode(ctor.get(5));
        let type_root = ctor.scalar_u64(6, 0);
        let value_root = ctor.scalar_u64(6, 8);
        ConstantMeta::Def {
          name,
          lvls,
          hints,
          all,
          ctx,
          arena,
          type_root,
          value_root,
        }
      },

      2 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        let name = ba.decode_ixon();
        let lvls = decode_address_array(ctor.get(1));
        let arena = IxonExprMetaArena::decode(ctor.get(2));
        let type_root = ctor.scalar_u64(3, 0);
        ConstantMeta::Axio { name, lvls, arena, type_root }
      },

      3 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        let name = ba.decode_ixon();
        let lvls = decode_address_array(ctor.get(1));
        let arena = IxonExprMetaArena::decode(ctor.get(2));
        let type_root = ctor.scalar_u64(3, 0);
        ConstantMeta::Quot { name, lvls, arena, type_root }
      },

      4 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        let name = ba.decode_ixon();
        let lvls = decode_address_array(ctor.get(1));
        let ctors = decode_address_array(ctor.get(2));
        let all = decode_address_array(ctor.get(3));
        let ctx = decode_address_array(ctor.get(4));
        let arena = IxonExprMetaArena::decode(ctor.get(5));
        let type_root = ctor.scalar_u64(6, 0);
        ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root }
      },

      5 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        let name = ba.decode_ixon();
        let lvls = decode_address_array(ctor.get(1));
        let ba2 = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(2).as_ptr()) };
        let induct = ba2.decode_ixon();
        let arena = IxonExprMetaArena::decode(ctor.get(3));
        let type_root = ctor.scalar_u64(4, 0);
        ConstantMeta::Ctor { name, lvls, induct, arena, type_root }
      },

      6 => {
        let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
        let name = ba.decode_ixon();
        let lvls = decode_address_array(ctor.get(1));
        let rules = decode_address_array(ctor.get(2));
        let all = decode_address_array(ctor.get(3));
        let ctx = decode_address_array(ctor.get(4));
        let arena = IxonExprMetaArena::decode(ctor.get(5));
        let rule_roots = decode_u64_array(ctor.get(6));
        let type_root = ctor.scalar_u64(7, 0);
        ConstantMeta::Rec {
          name,
          lvls,
          rules,
          all,
          ctx,
          arena,
          type_root,
          rule_roots,
        }
      },

      tag => panic!("Invalid Ixon.ConstantMeta tag: {tag}"),
    }
  }
}

// =============================================================================
// Named and Comm Build/Decode
// =============================================================================

impl IxonNamed {
  /// Build Ixon.Named { addr : Address, constMeta : ConstantMeta }
  pub fn build(addr: &Address, meta: &ConstantMeta) -> Self {
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, IxAddress::build_from_ixon(addr));
    ctor.set(1, IxonConstantMeta::build(meta));
    Self::new(*ctor)
  }

  /// Decode Ixon.Named.
  pub fn decode(self) -> Named {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let ba = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
    Named {
      addr: ba.decode_ixon(),
      meta: IxonConstantMeta::new(ctor.get(1)).decode(),
    }
  }
}

impl IxonComm {
  /// Build Ixon.Comm { secret : Address, payload : Address }
  pub fn build(comm: &Comm) -> Self {
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, IxAddress::build_from_ixon(&comm.secret));
    ctor.set(1, IxAddress::build_from_ixon(&comm.payload));
    Self::new(*ctor)
  }

  /// Decode Ixon.Comm.
  pub fn decode(self) -> Comm {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let ba0 = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
    let ba1 = unsafe { crate::lean::obj::LeanByteArray::from_raw(ctor.get(1).as_ptr()) };
    Comm {
      secret: ba0.decode_ixon(),
      payload: ba1.decode_ixon(),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DataValue.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_data_value(obj: LeanObj) -> LeanObj {
  let dv = IxonDataValue::new(obj).decode();
  IxonDataValue::build(&dv).into()
}

/// Round-trip Ixon.Comm.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_comm(obj: LeanObj) -> LeanObj {
  let comm = IxonComm::new(obj).decode();
  IxonComm::build(&comm).into()
}

/// Round-trip Ixon.ExprMetaData.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_data(obj: LeanObj) -> LeanObj {
  let node = IxonExprMetaData::new(obj).decode();
  IxonExprMetaData::build(&node).into()
}

/// Round-trip Ixon.ExprMetaArena.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_arena(obj: LeanObj) -> LeanObj {
  let arena = IxonExprMetaArena::decode(obj);
  IxonExprMetaArena::build(&arena).into()
}

/// Round-trip Ixon.ConstantMeta (full arena-based).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_meta(obj: LeanObj) -> LeanObj {
  let meta = IxonConstantMeta::new(obj).decode();
  IxonConstantMeta::build(&meta).into()
}

/// Round-trip Ixon.Named (with real metadata).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_named(obj: LeanObj) -> LeanObj {
  let named = IxonNamed::new(obj).decode();
  IxonNamed::build(&named.addr, &named.meta).into()
}
