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

use crate::lean::LeanIxAddress;
use crate::lean::LeanIxBinderInfo;

// =============================================================================
// KVMap Build/Decode (not domain types, kept as free functions)
// =============================================================================

/// Build an Ixon.KVMap (Array (Address × DataValue)).
pub fn build_ixon_kvmap(kvmap: &KVMap) -> LeanArray {
  let arr = LeanArray::alloc(kvmap.len());
  for (i, (addr, dv)) in kvmap.iter().enumerate() {
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, LeanIxAddress::build(addr));
    pair.set(1, LeanIxonDataValue::build(dv));
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
        LeanIxAddress::new(pair_ctor.get(0)).decode(),
        LeanIxonDataValue::new(pair_ctor.get(1)).decode(),
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
  LeanIxAddress::decode_array(obj)
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
// DataValue Build/Decode
// =============================================================================

impl LeanIxonDataValue {
  /// Build Ixon.DataValue (for metadata)
  pub fn build(dv: &IxonDataValue) -> Self {
    let obj = match dv {
      IxonDataValue::OfString(addr) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        *ctor
      },
      IxonDataValue::OfBool(b) => {
        let ctor = LeanCtor::alloc(1, 0, 1);
        ctor.set_scalar_u8(0, 0, if *b { 1 } else { 0 });
        *ctor
      },
      IxonDataValue::OfName(addr) => {
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        *ctor
      },
      IxonDataValue::OfNat(addr) => {
        let ctor = LeanCtor::alloc(3, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        *ctor
      },
      IxonDataValue::OfInt(addr) => {
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        *ctor
      },
      IxonDataValue::OfSyntax(addr) => {
        let ctor = LeanCtor::alloc(5, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.DataValue.
  pub fn decode(self) -> IxonDataValue {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => IxonDataValue::OfString(LeanIxAddress::new(ctor.get(0)).decode()),
      1 => {
        let b = ctor.scalar_u8(0, 0) != 0;
        IxonDataValue::OfBool(b)
      },
      2 => IxonDataValue::OfName(LeanIxAddress::new(ctor.get(0)).decode()),
      3 => IxonDataValue::OfNat(LeanIxAddress::new(ctor.get(0)).decode()),
      4 => IxonDataValue::OfInt(LeanIxAddress::new(ctor.get(0)).decode()),
      5 => IxonDataValue::OfSyntax(LeanIxAddress::new(ctor.get(0)).decode()),
      tag => panic!("Invalid Ixon.DataValue tag: {}", tag),
    }
  }
}

// =============================================================================
// ExprMetaData Build/Decode
// =============================================================================

impl LeanIxonExprMetaData {
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
  pub fn build(node: &ExprMetaData) -> Self {
    let obj = match node {
      ExprMetaData::Leaf => LeanObject::box_usize(0),

      ExprMetaData::App { children } => {
        // Tag 1, 0 obj fields, 16 scalar bytes (2× u64)
        let ctor = LeanCtor::alloc(1, 0, 16);
        ctor.set_scalar_u64(0, 0, children[0]);
        ctor.set_scalar_u64(0, 8, children[1]);
        *ctor
      },

      ExprMetaData::Binder { name, info, children } => {
        // Tag 2, 1 obj field (name), scalar: 2× u64 + u8 (info)
        // Lean ABI sorts scalars by size descending: [tyChild: u64 @ 8] [bodyChild: u64 @ 16] [info: u8 @ 24]
        // Offsets from obj_cptr: 1*8=8 base for scalar area
        let ctor = LeanCtor::alloc(2, 1, 17);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set_scalar_u64(1, 0, children[0]);
        ctor.set_scalar_u64(1, 8, children[1]);
        ctor.set_scalar_u8(1, 16, LeanIxBinderInfo::to_u8(info));
        *ctor
      },

      ExprMetaData::LetBinder { name, children } => {
        // Tag 3, 1 obj field (name), 24 scalar bytes (3× u64)
        let ctor = LeanCtor::alloc(3, 1, 24);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set_scalar_u64(1, 0, children[0]);
        ctor.set_scalar_u64(1, 8, children[1]);
        ctor.set_scalar_u64(1, 16, children[2]);
        *ctor
      },

      ExprMetaData::Ref { name } => {
        // Tag 4, 1 obj field (name), 0 scalar bytes
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, LeanIxAddress::build(name));
        *ctor
      },

      ExprMetaData::Prj { struct_name, child } => {
        // Tag 5, 1 obj field (structName), 8 scalar bytes (1× u64)
        let ctor = LeanCtor::alloc(5, 1, 8);
        ctor.set(0, LeanIxAddress::build(struct_name));
        ctor.set_scalar_u64(1, 0, *child);
        *ctor
      },

      ExprMetaData::Mdata { mdata, child } => {
        // Tag 6, 1 obj field (mdata: Array KVMap), 8 scalar bytes (1× u64)
        let mdata_arr = build_kvmap_array(mdata);
        let ctor = LeanCtor::alloc(6, 1, 8);
        ctor.set(0, mdata_arr);
        ctor.set_scalar_u64(1, 0, *child);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.ExprMetaData from Lean pointer.
  pub fn decode(self) -> ExprMetaData {
    // Leaf (tag 0, no fields) is represented as a scalar lean_box(0)
    if self.is_scalar() {
      let tag = self.as_ptr() as usize >> 1;
      assert_eq!(tag, 0, "Invalid scalar ExprMetaData tag: {}", tag);
      return ExprMetaData::Leaf;
    }
    let ctor = self.as_ctor();
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
        let name = LeanIxAddress::new(ctor.get(0)).decode();
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
        let name = LeanIxAddress::new(ctor.get(0)).decode();
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
        ExprMetaData::Ref { name: LeanIxAddress::new(ctor.get(0)).decode() }
      },

      5 => {
        // prj: 1 obj field (structName), 1× u64 scalar
        let struct_name = LeanIxAddress::new(ctor.get(0)).decode();
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
}

// =============================================================================
// ExprMetaArena Build/Decode
// =============================================================================

impl LeanIxonExprMetaArena {
  /// Build Ixon.ExprMetaArena Lean object.
  /// ExprMetaArena is a single-field structure (nodes : Array ExprMetaData),
  /// which Lean unboxes — the value IS the Array directly.
  pub fn build(arena: &ExprMeta) -> Self {
    let arr = LeanArray::alloc(arena.nodes.len());
    for (i, node) in arena.nodes.iter().enumerate() {
      arr.set(i, LeanIxonExprMetaData::build(node));
    }
    Self::new(*arr)
  }

  /// Decode Ixon.ExprMetaArena from Lean pointer.
  /// Single-field struct is unboxed — obj IS the Array directly.
  pub fn decode(self) -> ExprMeta {
    let arr = self.as_array();
    ExprMeta { nodes: arr.map(|x| LeanIxonExprMetaData::new(x).decode()) }
  }
}

// =============================================================================
// ConstantMeta Build/Decode
// =============================================================================

impl LeanIxonConstantMeta {
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
  pub fn build(meta: &ConstantMeta) -> Self {
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
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxReducibilityHints::build(hints));
        ctor.set(3, LeanIxAddress::build_array(all));
        ctor.set(4, LeanIxAddress::build_array(ctx));
        ctor.set(5, LeanIxonExprMetaArena::build(arena));
        ctor.set_scalar_u64(6, 0, *type_root);
        ctor.set_scalar_u64(6, 8, *value_root);
        *ctor
      },

      ConstantMeta::Axio { name, lvls, arena, type_root } => {
        let ctor = LeanCtor::alloc(2, 3, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_scalar_u64(3, 0, *type_root);
        *ctor
      },

      ConstantMeta::Quot { name, lvls, arena, type_root } => {
        let ctor = LeanCtor::alloc(3, 3, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_scalar_u64(3, 0, *type_root);
        *ctor
      },

      ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        let ctor = LeanCtor::alloc(4, 6, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxAddress::build_array(ctors));
        ctor.set(3, LeanIxAddress::build_array(all));
        ctor.set(4, LeanIxAddress::build_array(ctx));
        ctor.set(5, LeanIxonExprMetaArena::build(arena));
        ctor.set_scalar_u64(6, 0, *type_root);
        *ctor
      },

      ConstantMeta::Ctor { name, lvls, induct, arena, type_root } => {
        let ctor = LeanCtor::alloc(5, 4, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxAddress::build(induct));
        ctor.set(3, LeanIxonExprMetaArena::build(arena));
        ctor.set_scalar_u64(4, 0, *type_root);
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
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxAddress::build_array(rules));
        ctor.set(3, LeanIxAddress::build_array(all));
        ctor.set(4, LeanIxAddress::build_array(ctx));
        ctor.set(5, LeanIxonExprMetaArena::build(arena));
        ctor.set(6, build_u64_array(rule_roots));
        ctor.set_scalar_u64(7, 0, *type_root);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.ConstantMeta from Lean pointer.
  pub fn decode(self) -> ConstantMeta {
    // Empty (tag 0, no fields) is represented as a scalar lean_box(0)
    if self.is_scalar() {
      let tag = self.as_ptr() as usize >> 1;
      assert_eq!(tag, 0, "Invalid scalar ConstantMeta tag: {}", tag);
      return ConstantMeta::Empty;
    }
    let ctor = self.as_ctor();
    match ctor.tag() {
      1 => {
        // defn: 6 obj fields, 2× u64 scalar
        let name = LeanIxAddress::new(ctor.get(0)).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let hints = LeanIxReducibilityHints::new(ctor.get(2)).decode();
        let all = decode_address_array(ctor.get(3).as_array());
        let ctx = decode_address_array(ctor.get(4).as_array());
        let arena = LeanIxonExprMetaArena::new(ctor.get(5)).decode();
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
        let name = LeanIxAddress::new(ctor.get(0)).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let arena = LeanIxonExprMetaArena::new(ctor.get(2)).decode();
        let type_root = ctor.scalar_u64(3, 0);
        ConstantMeta::Axio { name, lvls, arena, type_root }
      },

      3 => {
        // quot: 3 obj fields, 1× u64 scalar
        let name = LeanIxAddress::new(ctor.get(0)).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let arena = LeanIxonExprMetaArena::new(ctor.get(2)).decode();
        let type_root = ctor.scalar_u64(3, 0);
        ConstantMeta::Quot { name, lvls, arena, type_root }
      },

      4 => {
        // indc: 6 obj fields, 1× u64 scalar
        let name = LeanIxAddress::new(ctor.get(0)).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let ctors = decode_address_array(ctor.get(2).as_array());
        let all = decode_address_array(ctor.get(3).as_array());
        let ctx = decode_address_array(ctor.get(4).as_array());
        let arena = LeanIxonExprMetaArena::new(ctor.get(5)).decode();
        let type_root = ctor.scalar_u64(6, 0);
        ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root }
      },

      5 => {
        // ctor: 4 obj fields, 1× u64 scalar
        let name = LeanIxAddress::new(ctor.get(0)).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let induct = LeanIxAddress::new(ctor.get(2)).decode();
        let arena = LeanIxonExprMetaArena::new(ctor.get(3)).decode();
        let type_root = ctor.scalar_u64(4, 0);
        ConstantMeta::Ctor { name, lvls, induct, arena, type_root }
      },

      6 => {
        // recr: 7 obj fields, 1× u64 scalar
        let name = LeanIxAddress::new(ctor.get(0)).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let rules = decode_address_array(ctor.get(2).as_array());
        let all = decode_address_array(ctor.get(3).as_array());
        let ctx = decode_address_array(ctor.get(4).as_array());
        let arena = LeanIxonExprMetaArena::new(ctor.get(5)).decode();
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
}

// =============================================================================
// Named and Comm Build/Decode
// =============================================================================

impl LeanIxonNamed {
  /// Build Ixon.Named { addr : Address, constMeta : ConstantMeta }
  pub fn build(addr: &Address, meta: &ConstantMeta) -> Self {
    let addr_obj = LeanIxAddress::build(addr);
    let meta_obj = LeanIxonConstantMeta::build(meta);
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, addr_obj);
    ctor.set(1, meta_obj);
    Self::new(*ctor)
  }

  /// Decode Ixon.Named.
  pub fn decode(self) -> Named {
    let ctor = self.as_ctor();
    Named {
      addr: LeanIxAddress::new(ctor.get(0)).decode(),
      meta: LeanIxonConstantMeta::new(ctor.get(1)).decode(),
    }
  }
}

impl LeanIxonComm {
  /// Build Ixon.Comm { secret : Address, payload : Address }
  pub fn build(comm: &Comm) -> Self {
    let secret_obj = LeanIxAddress::build(&comm.secret);
    let payload_obj = LeanIxAddress::build(&comm.payload);
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, secret_obj);
    ctor.set(1, payload_obj);
    Self::new(*ctor)
  }

  /// Decode Ixon.Comm.
  pub fn decode(self) -> Comm {
    let ctor = self.as_ctor();
    Comm {
      secret: LeanIxAddress::new(ctor.get(0)).decode(),
      payload: LeanIxAddress::new(ctor.get(1)).decode(),
    }
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
  let dv = obj.decode();
  LeanIxonDataValue::build(&dv)
}

/// Round-trip Ixon.Comm.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_comm(obj: LeanIxonComm) -> LeanIxonComm {
  let comm = obj.decode();
  LeanIxonComm::build(&comm)
}

/// Round-trip Ixon.ExprMetaData.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_data(
  obj: LeanIxonExprMetaData,
) -> LeanIxonExprMetaData {
  let node = obj.decode();
  LeanIxonExprMetaData::build(&node)
}

/// Round-trip Ixon.ExprMetaArena.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_arena(
  obj: LeanIxonExprMetaArena,
) -> LeanIxonExprMetaArena {
  let arena = obj.decode();
  LeanIxonExprMetaArena::build(&arena)
}

/// Round-trip Ixon.ConstantMeta (full arena-based).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_meta(
  obj: LeanIxonConstantMeta,
) -> LeanIxonConstantMeta {
  let meta = obj.decode();
  LeanIxonConstantMeta::build(&meta)
}

/// Round-trip Ixon.Named (with real metadata).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_named(obj: LeanIxonNamed) -> LeanIxonNamed {
  let named = obj.decode();
  LeanIxonNamed::build(&named.addr, &named.meta)
}
