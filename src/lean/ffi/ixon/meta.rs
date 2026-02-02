//! Ixon metadata types build/decode/roundtrip FFI.
//!
//! Includes: DataValue, KVMap, ExprMetaData, ExprMetaArena, ConstantMeta, Named, Comm

use std::ffi::c_void;

use crate::ix::address::Address;
use crate::ix::env::BinderInfo;
use crate::ix::ixon::Comm;
use crate::ix::ixon::env::Named;
use crate::ix::ixon::metadata::{
  ConstantMeta, DataValue as IxonDataValue, ExprMeta, ExprMetaData, KVMap,
};
use crate::lean::array::LeanArrayObject;
use crate::lean::ctor::LeanCtorObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_box_fn,
  lean_ctor_get, lean_ctor_set, lean_ctor_set_uint64, lean_ctor_set_uint8, lean_is_scalar,
  lean_obj_tag,
};

use super::constant::{build_address_array, build_address_from_ixon, decode_ixon_address};
use crate::lean::ffi::ix::constant::{build_reducibility_hints, decode_reducibility_hints};
use crate::lean::ffi::ix::expr::binder_info_to_u8;

// =============================================================================
// DataValue Build/Decode
// =============================================================================

/// Build Ixon.DataValue (for metadata)
pub fn build_ixon_data_value(dv: &IxonDataValue) -> *mut c_void {
  unsafe {
    match dv {
      IxonDataValue::OfString(addr) => {
        let addr_obj = build_address_from_ixon(addr);
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, addr_obj);
        obj
      }
      IxonDataValue::OfBool(b) => {
        let obj = lean_alloc_ctor(1, 0, 1);
        lean_ctor_set_uint8(obj, 0, if *b { 1 } else { 0 });
        obj
      }
      IxonDataValue::OfName(addr) => {
        let addr_obj = build_address_from_ixon(addr);
        let obj = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(obj, 0, addr_obj);
        obj
      }
      IxonDataValue::OfNat(addr) => {
        let addr_obj = build_address_from_ixon(addr);
        let obj = lean_alloc_ctor(3, 1, 0);
        lean_ctor_set(obj, 0, addr_obj);
        obj
      }
      IxonDataValue::OfInt(addr) => {
        let addr_obj = build_address_from_ixon(addr);
        let obj = lean_alloc_ctor(4, 1, 0);
        lean_ctor_set(obj, 0, addr_obj);
        obj
      }
      IxonDataValue::OfSyntax(addr) => {
        let addr_obj = build_address_from_ixon(addr);
        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, addr_obj);
        obj
      }
    }
  }
}

/// Decode Ixon.DataValue.
pub fn decode_ixon_data_value(ptr: *const c_void) -> IxonDataValue {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        IxonDataValue::OfString(decode_ixon_address(addr_ptr))
      }
      1 => {
        let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
        let b = ctor.get_scalar_u8(0, 0) != 0;
        IxonDataValue::OfBool(b)
      }
      2 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        IxonDataValue::OfName(decode_ixon_address(addr_ptr))
      }
      3 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        IxonDataValue::OfNat(decode_ixon_address(addr_ptr))
      }
      4 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        IxonDataValue::OfInt(decode_ixon_address(addr_ptr))
      }
      5 => {
        let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
        IxonDataValue::OfSyntax(decode_ixon_address(addr_ptr))
      }
      _ => panic!("Invalid Ixon.DataValue tag: {}", tag),
    }
  }
}

// =============================================================================
// KVMap Build/Decode
// =============================================================================

/// Build an Ixon.KVMap (Array (Address × DataValue)).
pub fn build_ixon_kvmap(kvmap: &KVMap) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(kvmap.len(), kvmap.len());
    for (i, (addr, dv)) in kvmap.iter().enumerate() {
      let addr_obj = build_address_from_ixon(addr);
      let dv_obj = build_ixon_data_value(dv);
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, addr_obj);
      lean_ctor_set(pair, 1, dv_obj);
      lean_array_set_core(arr, i, pair);
    }
    arr
  }
}

/// Build Array KVMap.
pub fn build_kvmap_array(kvmaps: &[KVMap]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(kvmaps.len(), kvmaps.len());
    for (i, kvmap) in kvmaps.iter().enumerate() {
      let kvmap_obj = build_ixon_kvmap(kvmap);
      lean_array_set_core(arr, i, kvmap_obj);
    }
    arr
  }
}

/// Decode KVMap (Array (Address × DataValue)).
pub fn decode_ixon_kvmap(ptr: *const c_void) -> KVMap {
  let arr: &LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(|pair| unsafe {
    let addr_ptr = lean_ctor_get(pair as *mut _, 0);
    let dv_ptr = lean_ctor_get(pair as *mut _, 1);
    (decode_ixon_address(addr_ptr), decode_ixon_data_value(dv_ptr))
  })
}

/// Decode Array KVMap.
fn decode_kvmap_array(ptr: *const c_void) -> Vec<KVMap> {
  let arr: &LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(decode_ixon_kvmap)
}

// =============================================================================
// Address Array Helpers
// =============================================================================

/// Decode Array Address.
fn decode_address_array(ptr: *const c_void) -> Vec<Address> {
  let arr: &LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(decode_ixon_address)
}

/// Build Array UInt64.
fn build_u64_array(vals: &[u64]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(vals.len(), vals.len());
    for (i, &v) in vals.iter().enumerate() {
      let obj = crate::lean::lean_box_u64(v);
      lean_array_set_core(arr, i, obj);
    }
    arr
  }
}

/// Decode Array UInt64.
fn decode_u64_array(ptr: *const c_void) -> Vec<u64> {
  let arr: &LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(crate::lean::lean_unbox_u64)
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
pub fn build_expr_meta_data(node: &ExprMetaData) -> *mut c_void {
  unsafe {
    match node {
      ExprMetaData::Leaf => lean_box_fn(0),

      ExprMetaData::App { children } => {
        // Tag 1, 0 obj fields, 16 scalar bytes (2× u64)
        let obj = lean_alloc_ctor(1, 0, 16);
        lean_ctor_set_uint64(obj, 0, children[0]);
        lean_ctor_set_uint64(obj, 8, children[1]);
        obj
      }

      ExprMetaData::Binder { name, info, children } => {
        // Tag 2, 1 obj field (name), scalar: 2× u64 + u8 (info)
        // Lean ABI sorts scalars by size descending: [tyChild: u64 @ 0] [bodyChild: u64 @ 8] [info: u8 @ 16]
        let obj = lean_alloc_ctor(2, 1, 17);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set_uint64(obj, 8, children[0]);
        lean_ctor_set_uint64(obj, 8 + 8, children[1]);
        lean_ctor_set_uint8(obj, 8 + 16, binder_info_to_u8(info));
        obj
      }

      ExprMetaData::LetBinder { name, children } => {
        // Tag 3, 1 obj field (name), 24 scalar bytes (3× u64)
        let obj = lean_alloc_ctor(3, 1, 24);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set_uint64(obj, 8, children[0]);
        lean_ctor_set_uint64(obj, 8 + 8, children[1]);
        lean_ctor_set_uint64(obj, 8 + 16, children[2]);
        obj
      }

      ExprMetaData::Ref { name } => {
        // Tag 4, 1 obj field (name), 0 scalar bytes
        let obj = lean_alloc_ctor(4, 1, 0);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        obj
      }

      ExprMetaData::Prj { struct_name, child } => {
        // Tag 5, 1 obj field (structName), 8 scalar bytes (1× u64)
        let obj = lean_alloc_ctor(5, 1, 8);
        lean_ctor_set(obj, 0, build_address_from_ixon(struct_name));
        lean_ctor_set_uint64(obj, 8, *child);
        obj
      }

      ExprMetaData::Mdata { mdata, child } => {
        // Tag 6, 1 obj field (mdata: Array KVMap), 8 scalar bytes (1× u64)
        let mdata_obj = build_kvmap_array(mdata);
        let obj = lean_alloc_ctor(6, 1, 8);
        lean_ctor_set(obj, 0, mdata_obj);
        lean_ctor_set_uint64(obj, 8, *child);
        obj
      }
    }
  }
}

/// Decode Ixon.ExprMetaData from Lean pointer.
pub fn decode_expr_meta_data(ptr: *const c_void) -> ExprMetaData {
  unsafe {
    // Leaf (tag 0, no fields) is represented as a scalar lean_box(0)
    if lean_is_scalar(ptr) {
      let tag = (ptr as usize) >> 1;
      assert_eq!(tag, 0, "Invalid scalar ExprMetaData tag: {}", tag);
      return ExprMetaData::Leaf;
    }
    let tag = lean_obj_tag(ptr as *mut _);
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match tag {
      1 => {
        // app: 0 obj fields, 2× u64 scalar
        let fun_ = ctor.get_scalar_u64(0, 0);
        let arg = ctor.get_scalar_u64(0, 8);
        ExprMetaData::App { children: [fun_, arg] }
      }

      2 => {
        // binder: 1 obj field (name), scalar (Lean ABI: u64s first, then u8):
        // [tyChild: u64 @ 0] [bodyChild: u64 @ 8] [info: u8 @ 16]
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_child = ctor.get_scalar_u64(1, 0);
        let body_child = ctor.get_scalar_u64(1, 8);
        let info_byte = ctor.get_scalar_u8(1, 16);
        let info = match info_byte {
          0 => BinderInfo::Default,
          1 => BinderInfo::Implicit,
          2 => BinderInfo::StrictImplicit,
          3 => BinderInfo::InstImplicit,
          _ => panic!("Invalid BinderInfo tag: {}", info_byte),
        };
        ExprMetaData::Binder {
          name: decode_ixon_address(name_ptr),
          info,
          children: [ty_child, body_child],
        }
      }

      3 => {
        // letBinder: 1 obj field (name), 3× u64 scalar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_child = ctor.get_scalar_u64(1, 0);
        let val_child = ctor.get_scalar_u64(1, 8);
        let body_child = ctor.get_scalar_u64(1, 16);
        ExprMetaData::LetBinder {
          name: decode_ixon_address(name_ptr),
          children: [ty_child, val_child, body_child],
        }
      }

      4 => {
        // ref: 1 obj field (name), 0 scalar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        ExprMetaData::Ref { name: decode_ixon_address(name_ptr) }
      }

      5 => {
        // prj: 1 obj field (structName), 1× u64 scalar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let child = ctor.get_scalar_u64(1, 0);
        ExprMetaData::Prj {
          struct_name: decode_ixon_address(name_ptr),
          child,
        }
      }

      6 => {
        // mdata: 1 obj field (mdata: Array KVMap), 1× u64 scalar
        let mdata_ptr = lean_ctor_get(ptr as *mut _, 0);
        let child = ctor.get_scalar_u64(1, 0);
        ExprMetaData::Mdata {
          mdata: decode_kvmap_array(mdata_ptr),
          child,
        }
      }

      _ => panic!("Invalid Ixon.ExprMetaData tag: {}", tag),
    }
  }
}

// =============================================================================
// ExprMetaArena Build/Decode
// =============================================================================

/// Build Ixon.ExprMetaArena Lean object.
/// ExprMetaArena is a single-field structure (nodes : Array ExprMetaData),
/// which Lean unboxes — the value IS the Array directly.
pub fn build_expr_meta_arena(arena: &ExprMeta) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(arena.nodes.len(), arena.nodes.len());
    for (i, node) in arena.nodes.iter().enumerate() {
      lean_array_set_core(arr, i, build_expr_meta_data(node));
    }
    arr
  }
}

/// Decode Ixon.ExprMetaArena from Lean pointer.
/// Single-field struct is unboxed — ptr IS the Array directly.
pub fn decode_expr_meta_arena(ptr: *const c_void) -> ExprMeta {
  let arr: &LeanArrayObject = as_ref_unsafe(ptr.cast());
  ExprMeta {
    nodes: arr.to_vec(decode_expr_meta_data),
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
pub fn build_constant_meta(meta: &ConstantMeta) -> *mut c_void {
  unsafe {
    match meta {
      ConstantMeta::Empty => lean_box_fn(0),

      ConstantMeta::Def { name, lvls, hints, all, ctx, arena, type_root, value_root } => {
        let obj = lean_alloc_ctor(1, 6, 16);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set(obj, 1, build_address_array(lvls));
        lean_ctor_set(obj, 2, build_reducibility_hints(hints));
        lean_ctor_set(obj, 3, build_address_array(all));
        lean_ctor_set(obj, 4, build_address_array(ctx));
        lean_ctor_set(obj, 5, build_expr_meta_arena(arena));
        lean_ctor_set_uint64(obj, 6 * 8, *type_root);
        lean_ctor_set_uint64(obj, 6 * 8 + 8, *value_root);
        obj
      }

      ConstantMeta::Axio { name, lvls, arena, type_root } => {
        let obj = lean_alloc_ctor(2, 3, 8);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set(obj, 1, build_address_array(lvls));
        lean_ctor_set(obj, 2, build_expr_meta_arena(arena));
        lean_ctor_set_uint64(obj, 3 * 8, *type_root);
        obj
      }

      ConstantMeta::Quot { name, lvls, arena, type_root } => {
        let obj = lean_alloc_ctor(3, 3, 8);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set(obj, 1, build_address_array(lvls));
        lean_ctor_set(obj, 2, build_expr_meta_arena(arena));
        lean_ctor_set_uint64(obj, 3 * 8, *type_root);
        obj
      }

      ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        let obj = lean_alloc_ctor(4, 6, 8);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set(obj, 1, build_address_array(lvls));
        lean_ctor_set(obj, 2, build_address_array(ctors));
        lean_ctor_set(obj, 3, build_address_array(all));
        lean_ctor_set(obj, 4, build_address_array(ctx));
        lean_ctor_set(obj, 5, build_expr_meta_arena(arena));
        lean_ctor_set_uint64(obj, 6 * 8, *type_root);
        obj
      }

      ConstantMeta::Ctor { name, lvls, induct, arena, type_root } => {
        let obj = lean_alloc_ctor(5, 4, 8);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set(obj, 1, build_address_array(lvls));
        lean_ctor_set(obj, 2, build_address_from_ixon(induct));
        lean_ctor_set(obj, 3, build_expr_meta_arena(arena));
        lean_ctor_set_uint64(obj, 4 * 8, *type_root);
        obj
      }

      ConstantMeta::Rec { name, lvls, rules, all, ctx, arena, type_root, rule_roots } => {
        let obj = lean_alloc_ctor(6, 7, 8);
        lean_ctor_set(obj, 0, build_address_from_ixon(name));
        lean_ctor_set(obj, 1, build_address_array(lvls));
        lean_ctor_set(obj, 2, build_address_array(rules));
        lean_ctor_set(obj, 3, build_address_array(all));
        lean_ctor_set(obj, 4, build_address_array(ctx));
        lean_ctor_set(obj, 5, build_expr_meta_arena(arena));
        lean_ctor_set(obj, 6, build_u64_array(rule_roots));
        lean_ctor_set_uint64(obj, 7 * 8, *type_root);
        obj
      }
    }
  }
}

/// Decode Ixon.ConstantMeta from Lean pointer.
pub fn decode_constant_meta(ptr: *const c_void) -> ConstantMeta {
  unsafe {
    // Empty (tag 0, no fields) is represented as a scalar lean_box(0)
    if lean_is_scalar(ptr) {
      let tag = (ptr as usize) >> 1;
      assert_eq!(tag, 0, "Invalid scalar ConstantMeta tag: {}", tag);
      return ConstantMeta::Empty;
    }
    let tag = lean_obj_tag(ptr as *mut _);
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match tag {

      1 => {
        // defn: 6 obj fields, 2× u64 scalar
        let name = decode_ixon_address(lean_ctor_get(ptr as *mut _, 0));
        let lvls = decode_address_array(lean_ctor_get(ptr as *mut _, 1));
        let hints = decode_reducibility_hints(lean_ctor_get(ptr as *mut _, 2));
        let all = decode_address_array(lean_ctor_get(ptr as *mut _, 3));
        let ctx = decode_address_array(lean_ctor_get(ptr as *mut _, 4));
        let arena = decode_expr_meta_arena(lean_ctor_get(ptr as *mut _, 5));
        let type_root = ctor.get_scalar_u64(6, 0);
        let value_root = ctor.get_scalar_u64(6, 8);
        ConstantMeta::Def { name, lvls, hints, all, ctx, arena, type_root, value_root }
      }

      2 => {
        // axio: 3 obj fields, 1× u64 scalar
        let name = decode_ixon_address(lean_ctor_get(ptr as *mut _, 0));
        let lvls = decode_address_array(lean_ctor_get(ptr as *mut _, 1));
        let arena = decode_expr_meta_arena(lean_ctor_get(ptr as *mut _, 2));
        let type_root = ctor.get_scalar_u64(3, 0);
        ConstantMeta::Axio { name, lvls, arena, type_root }
      }

      3 => {
        // quot: 3 obj fields, 1× u64 scalar
        let name = decode_ixon_address(lean_ctor_get(ptr as *mut _, 0));
        let lvls = decode_address_array(lean_ctor_get(ptr as *mut _, 1));
        let arena = decode_expr_meta_arena(lean_ctor_get(ptr as *mut _, 2));
        let type_root = ctor.get_scalar_u64(3, 0);
        ConstantMeta::Quot { name, lvls, arena, type_root }
      }

      4 => {
        // indc: 6 obj fields, 1× u64 scalar
        let name = decode_ixon_address(lean_ctor_get(ptr as *mut _, 0));
        let lvls = decode_address_array(lean_ctor_get(ptr as *mut _, 1));
        let ctors = decode_address_array(lean_ctor_get(ptr as *mut _, 2));
        let all = decode_address_array(lean_ctor_get(ptr as *mut _, 3));
        let ctx = decode_address_array(lean_ctor_get(ptr as *mut _, 4));
        let arena = decode_expr_meta_arena(lean_ctor_get(ptr as *mut _, 5));
        let type_root = ctor.get_scalar_u64(6, 0);
        ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root }
      }

      5 => {
        // ctor: 4 obj fields, 1× u64 scalar
        let name = decode_ixon_address(lean_ctor_get(ptr as *mut _, 0));
        let lvls = decode_address_array(lean_ctor_get(ptr as *mut _, 1));
        let induct = decode_ixon_address(lean_ctor_get(ptr as *mut _, 2));
        let arena = decode_expr_meta_arena(lean_ctor_get(ptr as *mut _, 3));
        let type_root = ctor.get_scalar_u64(4, 0);
        ConstantMeta::Ctor { name, lvls, induct, arena, type_root }
      }

      6 => {
        // recr: 7 obj fields, 1× u64 scalar
        let name = decode_ixon_address(lean_ctor_get(ptr as *mut _, 0));
        let lvls = decode_address_array(lean_ctor_get(ptr as *mut _, 1));
        let rules = decode_address_array(lean_ctor_get(ptr as *mut _, 2));
        let all = decode_address_array(lean_ctor_get(ptr as *mut _, 3));
        let ctx = decode_address_array(lean_ctor_get(ptr as *mut _, 4));
        let arena = decode_expr_meta_arena(lean_ctor_get(ptr as *mut _, 5));
        let rule_roots = decode_u64_array(lean_ctor_get(ptr as *mut _, 6));
        let type_root = ctor.get_scalar_u64(7, 0);
        ConstantMeta::Rec { name, lvls, rules, all, ctx, arena, type_root, rule_roots }
      }

      _ => panic!("Invalid Ixon.ConstantMeta tag: {}", tag),
    }
  }
}

// =============================================================================
// Named and Comm Build/Decode
// =============================================================================

/// Build Ixon.Named { addr : Address, constMeta : ConstantMeta }
pub fn build_named(addr: &Address, meta: &ConstantMeta) -> *mut c_void {
  unsafe {
    let addr_obj = build_address_from_ixon(addr);
    let meta_obj = build_constant_meta(meta);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, addr_obj);
    lean_ctor_set(obj, 1, meta_obj);
    obj
  }
}

/// Decode Ixon.Named.
pub fn decode_named(ptr: *const c_void) -> Named {
  unsafe {
    let addr_ptr = lean_ctor_get(ptr as *mut _, 0);
    let meta_ptr = lean_ctor_get(ptr as *mut _, 1);
    Named {
      addr: decode_ixon_address(addr_ptr),
      meta: decode_constant_meta(meta_ptr),
    }
  }
}

/// Build Ixon.Comm { secret : Address, payload : Address }
pub fn build_ixon_comm(comm: &Comm) -> *mut c_void {
  unsafe {
    let secret_obj = build_address_from_ixon(&comm.secret);
    let payload_obj = build_address_from_ixon(&comm.payload);
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, secret_obj);
    lean_ctor_set(obj, 1, payload_obj);
    obj
  }
}

/// Decode Ixon.Comm.
pub fn decode_ixon_comm(ptr: *const c_void) -> Comm {
  unsafe {
    let secret_ptr = lean_ctor_get(ptr as *mut _, 0);
    let payload_ptr = lean_ctor_get(ptr as *mut _, 1);
    Comm {
      secret: decode_ixon_address(secret_ptr),
      payload: decode_ixon_address(payload_ptr),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DataValue.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_data_value(ptr: *const c_void) -> *mut c_void {
  let dv = decode_ixon_data_value(ptr);
  build_ixon_data_value(&dv)
}

/// Round-trip Ixon.Comm.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_comm(ptr: *const c_void) -> *mut c_void {
  let comm = decode_ixon_comm(ptr);
  build_ixon_comm(&comm)
}

/// Round-trip Ixon.ExprMetaData.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_data(ptr: *const c_void) -> *mut c_void {
  let node = decode_expr_meta_data(ptr);
  build_expr_meta_data(&node)
}

/// Round-trip Ixon.ExprMetaArena.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_arena(ptr: *const c_void) -> *mut c_void {
  let arena = decode_expr_meta_arena(ptr);
  build_expr_meta_arena(&arena)
}

/// Round-trip Ixon.ConstantMeta (full arena-based).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_meta(ptr: *const c_void) -> *mut c_void {
  let meta = decode_constant_meta(ptr);
  build_constant_meta(&meta)
}

/// Round-trip Ixon.Named (with real metadata).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_named(ptr: *const c_void) -> *mut c_void {
  let named = decode_named(ptr);
  build_named(&named.addr, &named.meta)
}
