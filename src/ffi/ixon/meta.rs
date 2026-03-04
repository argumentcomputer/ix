//! Ixon metadata types build/decode/roundtrip FFI.
//!
//! Includes: DataValue, KVMap, ExprMetaData, ExprMetaArena, ConstantMeta, Named, Comm

use crate::ix::address::Address;
use crate::ix::env::BinderInfo;
use crate::ix::ixon::Comm;
use crate::ix::ixon::env::Named;
use crate::ix::ixon::metadata::{
  ConstantMeta, DataValue as IxonDataValue, ExprMeta, ExprMetaData, KVMap,
};
use crate::lean::{
  LeanIxReducibilityHints, LeanIxonComm, LeanIxonConstantMeta,
  LeanIxonDataValue, LeanIxonExprMetaArena, LeanIxonExprMetaData,
  LeanIxonNamed,
};
use lean_ffi::object::{LeanArray, LeanCtor, LeanObject};

use crate::ffi::ix::constant::{
  build_reducibility_hints, decode_reducibility_hints,
};
use crate::ffi::ix::expr::binder_info_to_u8;
use crate::ffi::ixon::constant::{
  build_address_array, build_address_from_ixon, decode_ixon_address,
  decode_ixon_address_array,
};

// =============================================================================
// DataValue Build/Decode
// =============================================================================

/// Build Ixon.DataValue (for metadata)
pub fn build_ixon_data_value(dv: &IxonDataValue) -> LeanIxonDataValue {
  let obj = match dv {
    IxonDataValue::OfString(addr) => {
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    IxonDataValue::OfBool(b) => {
      let ctor = LeanCtor::alloc(1, 0, 1);
      ctor.set_u8(0, if *b { 1 } else { 0 });
      *ctor
    },
    IxonDataValue::OfName(addr) => {
      let ctor = LeanCtor::alloc(2, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    IxonDataValue::OfNat(addr) => {
      let ctor = LeanCtor::alloc(3, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    IxonDataValue::OfInt(addr) => {
      let ctor = LeanCtor::alloc(4, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
    IxonDataValue::OfSyntax(addr) => {
      let ctor = LeanCtor::alloc(5, 1, 0);
      ctor.set(0, build_address_from_ixon(addr));
      *ctor
    },
  };
  LeanIxonDataValue::new(obj)
}

/// Decode Ixon.DataValue.
pub fn decode_ixon_data_value(obj: LeanIxonDataValue) -> IxonDataValue {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      IxonDataValue::OfString(decode_ixon_address(ctor.get(0).as_byte_array()))
    },
    1 => {
      let b = ctor.scalar_u8(0, 0) != 0;
      IxonDataValue::OfBool(b)
    },
    2 => {
      IxonDataValue::OfName(decode_ixon_address(ctor.get(0).as_byte_array()))
    },
    3 => IxonDataValue::OfNat(decode_ixon_address(ctor.get(0).as_byte_array())),
    4 => IxonDataValue::OfInt(decode_ixon_address(ctor.get(0).as_byte_array())),
    5 => {
      IxonDataValue::OfSyntax(decode_ixon_address(ctor.get(0).as_byte_array()))
    },
    tag => panic!("Invalid Ixon.DataValue tag: {}", tag),
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
    pair.set(0, build_address_from_ixon(addr));
    pair.set(1, build_ixon_data_value(dv));
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
pub fn decode_ixon_kvmap(obj: LeanArray) -> KVMap {
  obj
    .iter()
    .map(|pair| {
      let pair_ctor = pair.as_ctor();
      (
        decode_ixon_address(pair_ctor.get(0).as_byte_array()),
        decode_ixon_data_value(LeanIxonDataValue::new(pair_ctor.get(1))),
      )
    })
    .collect()
}

/// Decode Array KVMap.
fn decode_kvmap_array(obj: LeanArray) -> Vec<KVMap> {
  obj.map(|x| decode_ixon_kvmap(x.as_array()))
}

// =============================================================================
// Address Array Helpers
// =============================================================================

/// Decode Array Address.
fn decode_address_array(obj: LeanArray) -> Vec<Address> {
  decode_ixon_address_array(obj)
}

/// Build Array UInt64.
fn build_u64_array(vals: &[u64]) -> LeanArray {
  let arr = LeanArray::alloc(vals.len());
  for (i, &v) in vals.iter().enumerate() {
    arr.set(i, LeanObject::box_u64(v));
  }
  arr
}

/// Decode Array UInt64.
fn decode_u64_array(obj: LeanArray) -> Vec<u64> {
  obj.iter().map(|elem| elem.unbox_u64()).collect()
}

// =============================================================================
// ExprMetaData Build/Decode
// =============================================================================

/// Build Ixon.ExprMetaData Lean object.
///
/// | Variant    | Tag | Obj fields             | Scalar bytes             |
/// |------------|-----|------------------------|--------------------------|
/// | leaf       | 0   | 0                      | 0                        |
/// | app        | 1   | 0                      | 16 (2× u64)             |
/// | binder     | 2   | 1 (name: Address)      | 17 (info: u8, 2× u64)   |
/// | letBinder  | 3   | 1 (name: Address)      | 24 (3× u64)             |
/// | ref        | 4   | 1 (name: Address)      | 0                        |
/// | prj        | 5   | 1 (structName: Address) | 8 (1× u64)             |
/// | mdata      | 6   | 1 (mdata: Array)       | 8 (1× u64)              |
pub fn build_expr_meta_data(node: &ExprMetaData) -> LeanIxonExprMetaData {
  let obj = match node {
    ExprMetaData::Leaf => LeanObject::box_usize(0),

    ExprMetaData::App { children } => {
      // Tag 1, 0 obj fields, 16 scalar bytes (2× u64)
      let ctor = LeanCtor::alloc(1, 0, 16);
      ctor.set_u64(0, children[0]);
      ctor.set_u64(8, children[1]);
      *ctor
    },

    ExprMetaData::Binder { name, info, children } => {
      // Tag 2, 1 obj field (name), scalar: 2× u64 + u8 (info)
      // Lean ABI sorts scalars by size descending: [tyChild: u64 @ 8] [bodyChild: u64 @ 16] [info: u8 @ 24]
      // Offsets from obj_cptr: 1*8=8 base for scalar area
      let ctor = LeanCtor::alloc(2, 1, 17);
      ctor.set(0, build_address_from_ixon(name));
      ctor.set_u64(8, children[0]);
      ctor.set_u64(16, children[1]);
      ctor.set_u8(24, binder_info_to_u8(info));
      *ctor
    },

    ExprMetaData::LetBinder { name, children } => {
      // Tag 3, 1 obj field (name), 24 scalar bytes (3× u64)
      let ctor = LeanCtor::alloc(3, 1, 24);
      ctor.set(0, build_address_from_ixon(name));
      ctor.set_u64(8, children[0]);
      ctor.set_u64(16, children[1]);
      ctor.set_u64(24, children[2]);
      *ctor
    },

    ExprMetaData::Ref { name } => {
      // Tag 4, 1 obj field (name), 0 scalar bytes
      let ctor = LeanCtor::alloc(4, 1, 0);
      ctor.set(0, build_address_from_ixon(name));
      *ctor
    },

    ExprMetaData::Prj { struct_name, child } => {
      // Tag 5, 1 obj field (structName), 8 scalar bytes (1× u64)
      let ctor = LeanCtor::alloc(5, 1, 8);
      ctor.set(0, build_address_from_ixon(struct_name));
      ctor.set_u64(8, *child);
      *ctor
    },

    ExprMetaData::Mdata { mdata, child } => {
      // Tag 6, 1 obj field (mdata: Array KVMap), 8 scalar bytes (1× u64)
      let mdata_arr = build_kvmap_array(mdata);
      let ctor = LeanCtor::alloc(6, 1, 8);
      ctor.set(0, mdata_arr);
      ctor.set_u64(8, *child);
      *ctor
    },
  };
  LeanIxonExprMetaData::new(obj)
}

/// Decode Ixon.ExprMetaData from Lean pointer.
pub fn decode_expr_meta_data(obj: LeanIxonExprMetaData) -> ExprMetaData {
  // Leaf (tag 0, no fields) is represented as a scalar lean_box(0)
  if obj.is_scalar() {
    let tag = obj.as_ptr() as usize >> 1;
    assert_eq!(tag, 0, "Invalid scalar ExprMetaData tag: {}", tag);
    return ExprMetaData::Leaf;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    1 => {
      // app: 0 obj fields, 2× u64 scalar
      let fun_ = ctor.scalar_u64(0, 0);
      let arg = ctor.scalar_u64(0, 8);
      ExprMetaData::App { children: [fun_, arg] }
    },

    2 => {
      // binder: 1 obj field (name), scalar (Lean ABI: u64s first, then u8):
      // [tyChild: u64 @ 0] [bodyChild: u64 @ 8] [info: u8 @ 16]
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let ty_child = ctor.scalar_u64(1, 0);
      let body_child = ctor.scalar_u64(1, 8);
      let info_byte = ctor.scalar_u8(1, 16);
      let info = match info_byte {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => panic!("Invalid BinderInfo tag: {}", info_byte),
      };
      ExprMetaData::Binder { name, info, children: [ty_child, body_child] }
    },

    3 => {
      // letBinder: 1 obj field (name), 3× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let ty_child = ctor.scalar_u64(1, 0);
      let val_child = ctor.scalar_u64(1, 8);
      let body_child = ctor.scalar_u64(1, 16);
      ExprMetaData::LetBinder {
        name,
        children: [ty_child, val_child, body_child],
      }
    },

    4 => {
      // ref: 1 obj field (name), 0 scalar
      ExprMetaData::Ref {
        name: decode_ixon_address(ctor.get(0).as_byte_array()),
      }
    },

    5 => {
      // prj: 1 obj field (structName), 1× u64 scalar
      let struct_name = decode_ixon_address(ctor.get(0).as_byte_array());
      let child = ctor.scalar_u64(1, 0);
      ExprMetaData::Prj { struct_name, child }
    },

    6 => {
      // mdata: 1 obj field (mdata: Array KVMap), 1× u64 scalar
      let mdata = decode_kvmap_array(ctor.get(0).as_array());
      let child = ctor.scalar_u64(1, 0);
      ExprMetaData::Mdata { mdata, child }
    },

    tag => panic!("Invalid Ixon.ExprMetaData tag: {}", tag),
  }
}

// =============================================================================
// ExprMetaArena Build/Decode
// =============================================================================

/// Build Ixon.ExprMetaArena Lean object.
/// ExprMetaArena is a single-field structure (nodes : Array ExprMetaData),
/// which Lean unboxes — the value IS the Array directly.
pub fn build_expr_meta_arena(arena: &ExprMeta) -> LeanArray {
  let arr = LeanArray::alloc(arena.nodes.len());
  for (i, node) in arena.nodes.iter().enumerate() {
    arr.set(i, build_expr_meta_data(node));
  }
  arr
}

/// Decode Ixon.ExprMetaArena from Lean pointer.
/// Single-field struct is unboxed — obj IS the Array directly.
pub fn decode_expr_meta_arena(obj: LeanIxonExprMetaArena) -> ExprMeta {
  let arr = obj.as_array();
  ExprMeta {
    nodes: arr.map(|x| decode_expr_meta_data(LeanIxonExprMetaData::new(x))),
  }
}

// =============================================================================
// ConstantMeta Build/Decode
// =============================================================================

/// Build Ixon.ConstantMeta Lean object.
///
/// | Variant | Tag | Obj fields | Scalar bytes |
/// |---------|-----|-----------|-------------|
/// | empty   | 0   | 0         | 0           |
/// | defn    | 1   | 6 (name, lvls, hints, all, ctx, arena) | 16 (2× u64) |
/// | axio    | 2   | 3 (name, lvls, arena) | 8 (1× u64) |
/// | quot    | 3   | 3 (name, lvls, arena) | 8 (1× u64) |
/// | indc    | 4   | 6 (name, lvls, ctors, all, ctx, arena) | 8 (1× u64) |
/// | ctor    | 5   | 4 (name, lvls, induct, arena) | 8 (1× u64) |
/// | recr    | 6   | 7 (name, lvls, rules, all, ctx, arena, ruleRoots) | 8 (1× u64) |
pub fn build_constant_meta(meta: &ConstantMeta) -> LeanIxonConstantMeta {
  let obj = match meta {
    ConstantMeta::Empty => LeanObject::box_usize(0),

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
      ctor.set(0, build_address_from_ixon(name));
      ctor.set(1, build_address_array(lvls));
      ctor.set(2, build_reducibility_hints(hints));
      ctor.set(3, build_address_array(all));
      ctor.set(4, build_address_array(ctx));
      ctor.set(5, build_expr_meta_arena(arena));
      ctor.set_u64(6 * 8, *type_root);
      ctor.set_u64(6 * 8 + 8, *value_root);
      *ctor
    },

    ConstantMeta::Axio { name, lvls, arena, type_root } => {
      let ctor = LeanCtor::alloc(2, 3, 8);
      ctor.set(0, build_address_from_ixon(name));
      ctor.set(1, build_address_array(lvls));
      ctor.set(2, build_expr_meta_arena(arena));
      ctor.set_u64(3 * 8, *type_root);
      *ctor
    },

    ConstantMeta::Quot { name, lvls, arena, type_root } => {
      let ctor = LeanCtor::alloc(3, 3, 8);
      ctor.set(0, build_address_from_ixon(name));
      ctor.set(1, build_address_array(lvls));
      ctor.set(2, build_expr_meta_arena(arena));
      ctor.set_u64(3 * 8, *type_root);
      *ctor
    },

    ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
      let ctor = LeanCtor::alloc(4, 6, 8);
      ctor.set(0, build_address_from_ixon(name));
      ctor.set(1, build_address_array(lvls));
      ctor.set(2, build_address_array(ctors));
      ctor.set(3, build_address_array(all));
      ctor.set(4, build_address_array(ctx));
      ctor.set(5, build_expr_meta_arena(arena));
      ctor.set_u64(6 * 8, *type_root);
      *ctor
    },

    ConstantMeta::Ctor { name, lvls, induct, arena, type_root } => {
      let ctor = LeanCtor::alloc(5, 4, 8);
      ctor.set(0, build_address_from_ixon(name));
      ctor.set(1, build_address_array(lvls));
      ctor.set(2, build_address_from_ixon(induct));
      ctor.set(3, build_expr_meta_arena(arena));
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
      ctor.set(0, build_address_from_ixon(name));
      ctor.set(1, build_address_array(lvls));
      ctor.set(2, build_address_array(rules));
      ctor.set(3, build_address_array(all));
      ctor.set(4, build_address_array(ctx));
      ctor.set(5, build_expr_meta_arena(arena));
      ctor.set(6, build_u64_array(rule_roots));
      ctor.set_u64(7 * 8, *type_root);
      *ctor
    },
  };
  LeanIxonConstantMeta::new(obj)
}

/// Decode Ixon.ConstantMeta from Lean pointer.
pub fn decode_constant_meta(obj: LeanIxonConstantMeta) -> ConstantMeta {
  // Empty (tag 0, no fields) is represented as a scalar lean_box(0)
  if obj.is_scalar() {
    let tag = obj.as_ptr() as usize >> 1;
    assert_eq!(tag, 0, "Invalid scalar ConstantMeta tag: {}", tag);
    return ConstantMeta::Empty;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    1 => {
      // defn: 6 obj fields, 2× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let lvls = decode_address_array(ctor.get(1).as_array());
      let hints =
        decode_reducibility_hints(LeanIxReducibilityHints::new(ctor.get(2)));
      let all = decode_address_array(ctor.get(3).as_array());
      let ctx = decode_address_array(ctor.get(4).as_array());
      let arena =
        decode_expr_meta_arena(LeanIxonExprMetaArena::new(ctor.get(5)));
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
      // axio: 3 obj fields, 1× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let lvls = decode_address_array(ctor.get(1).as_array());
      let arena =
        decode_expr_meta_arena(LeanIxonExprMetaArena::new(ctor.get(2)));
      let type_root = ctor.scalar_u64(3, 0);
      ConstantMeta::Axio { name, lvls, arena, type_root }
    },

    3 => {
      // quot: 3 obj fields, 1× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let lvls = decode_address_array(ctor.get(1).as_array());
      let arena =
        decode_expr_meta_arena(LeanIxonExprMetaArena::new(ctor.get(2)));
      let type_root = ctor.scalar_u64(3, 0);
      ConstantMeta::Quot { name, lvls, arena, type_root }
    },

    4 => {
      // indc: 6 obj fields, 1× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let lvls = decode_address_array(ctor.get(1).as_array());
      let ctors = decode_address_array(ctor.get(2).as_array());
      let all = decode_address_array(ctor.get(3).as_array());
      let ctx = decode_address_array(ctor.get(4).as_array());
      let arena =
        decode_expr_meta_arena(LeanIxonExprMetaArena::new(ctor.get(5)));
      let type_root = ctor.scalar_u64(6, 0);
      ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root }
    },

    5 => {
      // ctor: 4 obj fields, 1× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let lvls = decode_address_array(ctor.get(1).as_array());
      let induct = decode_ixon_address(ctor.get(2).as_byte_array());
      let arena =
        decode_expr_meta_arena(LeanIxonExprMetaArena::new(ctor.get(3)));
      let type_root = ctor.scalar_u64(4, 0);
      ConstantMeta::Ctor { name, lvls, induct, arena, type_root }
    },

    6 => {
      // recr: 7 obj fields, 1× u64 scalar
      let name = decode_ixon_address(ctor.get(0).as_byte_array());
      let lvls = decode_address_array(ctor.get(1).as_array());
      let rules = decode_address_array(ctor.get(2).as_array());
      let all = decode_address_array(ctor.get(3).as_array());
      let ctx = decode_address_array(ctor.get(4).as_array());
      let arena =
        decode_expr_meta_arena(LeanIxonExprMetaArena::new(ctor.get(5)));
      let rule_roots = decode_u64_array(ctor.get(6).as_array());
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

    tag => panic!("Invalid Ixon.ConstantMeta tag: {}", tag),
  }
}

// =============================================================================
// Named and Comm Build/Decode
// =============================================================================

/// Build Ixon.Named { addr : Address, constMeta : ConstantMeta }
pub fn build_named(addr: &Address, meta: &ConstantMeta) -> LeanIxonNamed {
  let addr_obj = build_address_from_ixon(addr);
  let meta_obj = build_constant_meta(meta);
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, addr_obj);
  ctor.set(1, meta_obj);
  LeanIxonNamed::new(*ctor)
}

/// Decode Ixon.Named.
pub fn decode_named(obj: LeanIxonNamed) -> Named {
  let ctor = obj.as_ctor();
  Named {
    addr: decode_ixon_address(ctor.get(0).as_byte_array()),
    meta: decode_constant_meta(LeanIxonConstantMeta::new(ctor.get(1))),
  }
}

/// Build Ixon.Comm { secret : Address, payload : Address }
pub fn build_ixon_comm(comm: &Comm) -> LeanIxonComm {
  let secret_obj = build_address_from_ixon(&comm.secret);
  let payload_obj = build_address_from_ixon(&comm.payload);
  let ctor = LeanCtor::alloc(0, 2, 0);
  ctor.set(0, secret_obj);
  ctor.set(1, payload_obj);
  LeanIxonComm::new(*ctor)
}

/// Decode Ixon.Comm.
pub fn decode_ixon_comm(obj: LeanIxonComm) -> Comm {
  let ctor = obj.as_ctor();
  Comm {
    secret: decode_ixon_address(ctor.get(0).as_byte_array()),
    payload: decode_ixon_address(ctor.get(1).as_byte_array()),
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DataValue.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_data_value(
  obj: LeanIxonDataValue,
) -> LeanIxonDataValue {
  let dv = decode_ixon_data_value(obj);
  build_ixon_data_value(&dv)
}

/// Round-trip Ixon.Comm.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_comm(obj: LeanIxonComm) -> LeanIxonComm {
  let comm = decode_ixon_comm(obj);
  build_ixon_comm(&comm)
}

/// Round-trip Ixon.ExprMetaData.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_data(
  obj: LeanIxonExprMetaData,
) -> LeanIxonExprMetaData {
  let node = decode_expr_meta_data(obj);
  build_expr_meta_data(&node)
}

/// Round-trip Ixon.ExprMetaArena.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_arena(
  obj: LeanIxonExprMetaArena,
) -> LeanIxonExprMetaArena {
  let arena = decode_expr_meta_arena(obj);
  LeanIxonExprMetaArena::new(*build_expr_meta_arena(&arena))
}

/// Round-trip Ixon.ConstantMeta (full arena-based).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_meta(
  obj: LeanIxonConstantMeta,
) -> LeanIxonConstantMeta {
  let meta = decode_constant_meta(obj);
  build_constant_meta(&meta)
}

/// Round-trip Ixon.Named (with real metadata).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_named(obj: LeanIxonNamed) -> LeanIxonNamed {
  let named = decode_named(obj);
  build_named(&named.addr, &named.meta)
}
