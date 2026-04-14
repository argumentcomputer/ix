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
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanCtor, LeanOwned, LeanRef};

use crate::lean::LeanIxAddress;
use crate::lean::LeanIxBinderInfo;

// =============================================================================
// KVMap Build/Decode (not domain types, kept as free functions)
// =============================================================================

/// Build an Ixon.KVMap (Array (Address × DataValue)).
pub fn build_ixon_kvmap(kvmap: &KVMap) -> LeanArray<LeanOwned> {
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
pub fn build_kvmap_array(kvmaps: &[KVMap]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(kvmaps.len());
  for (i, kvmap) in kvmaps.iter().enumerate() {
    arr.set(i, build_ixon_kvmap(kvmap));
  }
  arr
}

/// Decode KVMap (Array (Address × DataValue)).
pub fn decode_ixon_kvmap(obj: LeanArray<LeanBorrowed<'_>>) -> KVMap {
  obj
    .iter()
    .map(|pair| {
      let pair_ctor = pair.as_ctor();
      (
        LeanIxAddress::from_borrowed(pair_ctor.get(0).as_byte_array()).decode(),
        LeanIxonDataValue::new(pair_ctor.get(1).to_owned_ref()).decode(),
      )
    })
    .collect()
}

/// Decode Array KVMap.
fn decode_kvmap_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<KVMap> {
  obj.map(|x| decode_ixon_kvmap(x.as_array()))
}

// =============================================================================
// Address Array Helpers
// =============================================================================

/// Decode Array Address.
fn decode_address_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<Address> {
  LeanIxAddress::decode_array(obj)
}

/// Build Array UInt64.
fn build_u64_array(vals: &[u64]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(vals.len());
  for (i, &v) in vals.iter().enumerate() {
    arr.set(i, LeanOwned::box_u64(v));
  }
  arr
}

/// Decode Array UInt64.
fn decode_u64_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<u64> {
  obj.iter().map(|elem| elem.unbox_u64()).collect()
}

// =============================================================================
// DataValue Build/Decode
// =============================================================================

impl LeanIxonDataValue<LeanOwned> {
  /// Build Ixon.DataValue (for metadata)
  pub fn build(dv: &IxonDataValue) -> Self {
    let obj = match dv {
      IxonDataValue::OfString(addr) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        ctor.into()
      },
      IxonDataValue::OfBool(b) => {
        let ctor = LeanCtor::alloc(1, 0, 1);
        ctor.set_bool(ctor.scalar_base(0), *b);
        ctor.into()
      },
      IxonDataValue::OfName(addr) => {
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        ctor.into()
      },
      IxonDataValue::OfNat(addr) => {
        let ctor = LeanCtor::alloc(3, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        ctor.into()
      },
      IxonDataValue::OfInt(addr) => {
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        ctor.into()
      },
      IxonDataValue::OfSyntax(addr) => {
        let ctor = LeanCtor::alloc(5, 1, 0);
        ctor.set(0, LeanIxAddress::build(addr));
        ctor.into()
      },
    };
    Self::new(obj)
  }
}

impl<R: LeanRef> LeanIxonDataValue<R> {
  /// Decode Ixon.DataValue.
  pub fn decode(&self) -> IxonDataValue {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => IxonDataValue::OfString(
        LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      ),
      1 => {
        let b = ctor.get_bool(ctor.scalar_base(0));
        IxonDataValue::OfBool(b)
      },
      2 => IxonDataValue::OfName(
        LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      ),
      3 => IxonDataValue::OfNat(
        LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      ),
      4 => IxonDataValue::OfInt(
        LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      ),
      5 => IxonDataValue::OfSyntax(
        LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      ),
      tag => panic!("Invalid Ixon.DataValue tag: {}", tag),
    }
  }
}

// =============================================================================
// ExprMetaData Build/Decode
// =============================================================================

impl LeanIxonExprMetaData<LeanOwned> {
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
      ExprMetaData::Leaf => LeanOwned::box_usize(0),

      ExprMetaData::App { children } => {
        // Tag 1, 0 obj fields, 16 scalar bytes (2× u64)
        let ctor = LeanCtor::alloc(1, 0, 16);
        ctor.set_scalars::<2, u64>(ctor.scalar_base(0), *children);
        ctor.into()
      },

      ExprMetaData::Binder { name, info, children } => {
        // Tag 2, 1 obj field (name), scalar: 2× u64 + u8 (info)
        // Lean ABI sorts scalars by size descending: [tyChild: u64 @ 8] [bodyChild: u64 @ 16] [info: u8 @ 24]
        // Offsets from obj_cptr: 1*8=8 base for scalar area
        let ctor = LeanCtor::alloc(2, 1, 17);
        ctor.set(0, LeanIxAddress::build(name));
        let s = ctor.scalar_base(0);
        ctor.set_scalars::<2, u64>(s, *children);
        ctor.set_u8(s + 16, LeanIxBinderInfo::to_u8(info));
        ctor.into()
      },

      ExprMetaData::LetBinder { name, children } => {
        // Tag 3, 1 obj field (name), 24 scalar bytes (3× u64)
        let ctor = LeanCtor::alloc(3, 1, 24);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set_scalars::<3, u64>(ctor.scalar_base(0), *children);
        ctor.into()
      },

      ExprMetaData::Ref { name } => {
        // Tag 4, 1 obj field (name), 0 scalar bytes
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.into()
      },

      ExprMetaData::Prj { struct_name, child } => {
        // Tag 5, 1 obj field (structName), 8 scalar bytes (1× u64)
        let ctor = LeanCtor::alloc(5, 1, 8);
        ctor.set(0, LeanIxAddress::build(struct_name));
        ctor.set_u64(ctor.scalar_base(0), *child);
        ctor.into()
      },

      ExprMetaData::Mdata { mdata, child } => {
        // Tag 6, 1 obj field (mdata: Array KVMap), 8 scalar bytes (1× u64)
        let mdata_arr = build_kvmap_array(mdata);
        let ctor = LeanCtor::alloc(6, 1, 8);
        ctor.set(0, mdata_arr);
        ctor.set_u64(ctor.scalar_base(0), *child);
        ctor.into()
      },
    };
    Self::new(obj)
  }
}

impl<R: LeanRef> LeanIxonExprMetaData<R> {
  /// Decode Ixon.ExprMetaData from Lean pointer.
  pub fn decode(&self) -> ExprMetaData {
    // Leaf (tag 0, no fields) is represented as a scalar lean_box(0)
    if self.inner().is_scalar() {
      let tag = self.inner().as_raw() as usize >> 1;
      assert_eq!(tag, 0, "Invalid scalar ExprMetaData tag: {}", tag);
      return ExprMetaData::Leaf;
    }
    let ctor = self.as_ctor();
    match ctor.tag() {
      1 => {
        // app: 0 obj fields, 2× u64 scalar
        let children = ctor.get_scalars::<2, u64>(ctor.scalar_base(0));
        ExprMetaData::App { children }
      },

      2 => {
        // binder: 1 obj field (name), scalar (Lean ABI: u64s first, then u8):
        // [tyChild: u64 @ 0] [bodyChild: u64 @ 8] [info: u8 @ 16]
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let s = ctor.scalar_base(0);
        let [ty_child, body_child] = ctor.get_scalars::<2, u64>(s);
        let info_byte = ctor.get_u8(s + 16);
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
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let children = ctor.get_scalars::<3, u64>(ctor.scalar_base(0));
        ExprMetaData::LetBinder { name, children }
      },

      4 => {
        // ref: 1 obj field (name), 0 scalar
        ExprMetaData::Ref {
          name: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array())
            .decode(),
        }
      },

      5 => {
        // prj: 1 obj field (structName), 1× u64 scalar
        let struct_name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let child = ctor.get_u64(ctor.scalar_base(0));
        ExprMetaData::Prj { struct_name, child }
      },

      6 => {
        // mdata: 1 obj field (mdata: Array KVMap), 1× u64 scalar
        let mdata = decode_kvmap_array(ctor.get(0).as_array());
        let child = ctor.get_u64(ctor.scalar_base(0));
        ExprMetaData::Mdata { mdata, child }
      },

      tag => panic!("Invalid Ixon.ExprMetaData tag: {}", tag),
    }
  }
}

// =============================================================================
// ExprMetaArena Build/Decode
// =============================================================================

impl LeanIxonExprMetaArena<LeanOwned> {
  /// Build Ixon.ExprMetaArena Lean object.
  /// ExprMetaArena is a single-field structure (nodes : Array ExprMetaData),
  /// which Lean unboxes — the value IS the Array directly.
  pub fn build(arena: &ExprMeta) -> Self {
    let arr = LeanArray::alloc(arena.nodes.len());
    for (i, node) in arena.nodes.iter().enumerate() {
      arr.set(i, LeanIxonExprMetaData::build(node));
    }
    Self::new(arr.into())
  }
}

impl<R: LeanRef> LeanIxonExprMetaArena<R> {
  /// Decode Ixon.ExprMetaArena from Lean pointer.
  /// Single-field struct is unboxed — obj IS the Array directly.
  pub fn decode(&self) -> ExprMeta {
    let arr = unsafe { LeanBorrowed::from_raw(self.as_raw()) }.as_array();
    ExprMeta {
      nodes: arr.map(|x| LeanIxonExprMetaData::new(x.to_owned_ref()).decode()),
    }
  }
}

// =============================================================================
// ConstantMeta Build/Decode
// =============================================================================

impl LeanIxonConstantMeta<LeanOwned> {
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
      ConstantMeta::Empty => LeanOwned::box_usize(0),

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
        ctor.set_scalars::<2, u64>(ctor.scalar_base(0), [*type_root, *value_root]);
        ctor.into()
      },

      ConstantMeta::Axio { name, lvls, arena, type_root } => {
        let ctor = LeanCtor::alloc(2, 3, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_u64(ctor.scalar_base(0), *type_root);
        ctor.into()
      },

      ConstantMeta::Quot { name, lvls, arena, type_root } => {
        let ctor = LeanCtor::alloc(3, 3, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_u64(ctor.scalar_base(0), *type_root);
        ctor.into()
      },

      ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        let ctor = LeanCtor::alloc(4, 6, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxAddress::build_array(ctors));
        ctor.set(3, LeanIxAddress::build_array(all));
        ctor.set(4, LeanIxAddress::build_array(ctx));
        ctor.set(5, LeanIxonExprMetaArena::build(arena));
        ctor.set_u64(ctor.scalar_base(0), *type_root);
        ctor.into()
      },

      ConstantMeta::Ctor { name, lvls, induct, arena, type_root } => {
        let ctor = LeanCtor::alloc(5, 4, 8);
        ctor.set(0, LeanIxAddress::build(name));
        ctor.set(1, LeanIxAddress::build_array(lvls));
        ctor.set(2, LeanIxAddress::build(induct));
        ctor.set(3, LeanIxonExprMetaArena::build(arena));
        ctor.set_u64(ctor.scalar_base(0), *type_root);
        ctor.into()
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
        ctor.set_u64(ctor.scalar_base(0), *type_root);
        ctor.into()
      },
    };
    Self::new(obj)
  }
}

impl<R: LeanRef> LeanIxonConstantMeta<R> {
  /// Decode Ixon.ConstantMeta from Lean pointer.
  pub fn decode(&self) -> ConstantMeta {
    // Empty (tag 0, no fields) is represented as a scalar lean_box(0)
    if self.inner().is_scalar() {
      let tag = self.inner().as_raw() as usize >> 1;
      assert_eq!(tag, 0, "Invalid scalar ConstantMeta tag: {}", tag);
      return ConstantMeta::Empty;
    }
    let ctor = self.as_ctor();
    match ctor.tag() {
      1 => {
        // defn: 6 obj fields, 2× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let hints =
          LeanIxReducibilityHints::new(ctor.get(2).to_owned_ref()).decode();
        let all = decode_address_array(ctor.get(3).as_array());
        let ctx = decode_address_array(ctor.get(4).as_array());
        let arena =
          LeanIxonExprMetaArena::new(ctor.get(5).to_owned_ref()).decode();
        let [type_root, value_root] = ctor.get_scalars::<2, u64>(ctor.scalar_base(0));
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
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let arena =
          LeanIxonExprMetaArena::new(ctor.get(2).to_owned_ref()).decode();
        let type_root = ctor.get_u64(ctor.scalar_base(0));
        ConstantMeta::Axio { name, lvls, arena, type_root }
      },

      3 => {
        // quot: 3 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let arena =
          LeanIxonExprMetaArena::new(ctor.get(2).to_owned_ref()).decode();
        let type_root = ctor.get_u64(ctor.scalar_base(0));
        ConstantMeta::Quot { name, lvls, arena, type_root }
      },

      4 => {
        // indc: 6 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let ctors = decode_address_array(ctor.get(2).as_array());
        let all = decode_address_array(ctor.get(3).as_array());
        let ctx = decode_address_array(ctor.get(4).as_array());
        let arena =
          LeanIxonExprMetaArena::new(ctor.get(5).to_owned_ref()).decode();
        let type_root = ctor.get_u64(ctor.scalar_base(0));
        ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root }
      },

      5 => {
        // ctor: 4 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let induct =
          LeanIxAddress::from_borrowed(ctor.get(2).as_byte_array()).decode();
        let arena =
          LeanIxonExprMetaArena::new(ctor.get(3).to_owned_ref()).decode();
        let type_root = ctor.get_u64(ctor.scalar_base(0));
        ConstantMeta::Ctor { name, lvls, induct, arena, type_root }
      },

      6 => {
        // recr: 7 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
        let lvls = decode_address_array(ctor.get(1).as_array());
        let rules = decode_address_array(ctor.get(2).as_array());
        let all = decode_address_array(ctor.get(3).as_array());
        let ctx = decode_address_array(ctor.get(4).as_array());
        let arena =
          LeanIxonExprMetaArena::new(ctor.get(5).to_owned_ref()).decode();
        let rule_roots = decode_u64_array(ctor.get(6).as_array());
        let type_root = ctor.get_u64(ctor.scalar_base(0));
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

impl LeanIxonNamed<LeanOwned> {
  /// Build Ixon.Named { addr : Address, constMeta : ConstantMeta }
  pub fn build(addr: &Address, meta: &ConstantMeta) -> Self {
    let addr_obj = LeanIxAddress::build(addr);
    let meta_obj = LeanIxonConstantMeta::build(meta);
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, addr_obj);
    ctor.set(1, meta_obj);
    Self::new(ctor.into())
  }
}

impl<R: LeanRef> LeanIxonNamed<R> {
  /// Decode Ixon.Named.
  pub fn decode(&self) -> Named {
    let ctor = self.as_ctor();
    Named {
      addr: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode(),
      meta: LeanIxonConstantMeta::new(ctor.get(1).to_owned_ref()).decode(),
    }
  }
}

impl LeanIxonComm<LeanOwned> {
  /// Build Ixon.Comm { secret : Address, payload : Address }
  pub fn build(comm: &Comm) -> Self {
    let secret_obj = LeanIxAddress::build(&comm.secret);
    let payload_obj = LeanIxAddress::build(&comm.payload);
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, secret_obj);
    ctor.set(1, payload_obj);
    Self::new(ctor.into())
  }
}

impl<R: LeanRef> LeanIxonComm<R> {
  /// Decode Ixon.Comm.
  pub fn decode(&self) -> Comm {
    let ctor = self.as_ctor();
    Comm {
      secret: LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array())
        .decode(),
      payload: LeanIxAddress::from_borrowed(ctor.get(1).as_byte_array())
        .decode(),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.DataValue.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_data_value(
  obj: LeanIxonDataValue<LeanBorrowed<'_>>,
) -> LeanIxonDataValue<LeanOwned> {
  let dv = obj.decode();
  LeanIxonDataValue::build(&dv)
}

/// Round-trip Ixon.Comm.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_comm(
  obj: LeanIxonComm<LeanBorrowed<'_>>,
) -> LeanIxonComm<LeanOwned> {
  let comm = obj.decode();
  LeanIxonComm::build(&comm)
}

/// Round-trip Ixon.ExprMetaData.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_data(
  obj: LeanIxonExprMetaData<LeanBorrowed<'_>>,
) -> LeanIxonExprMetaData<LeanOwned> {
  let node = obj.decode();
  LeanIxonExprMetaData::build(&node)
}

/// Round-trip Ixon.ExprMetaArena.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr_meta_arena(
  obj: LeanIxonExprMetaArena<LeanBorrowed<'_>>,
) -> LeanIxonExprMetaArena<LeanOwned> {
  let arena = obj.decode();
  LeanIxonExprMetaArena::build(&arena)
}

/// Round-trip Ixon.ConstantMeta (full arena-based).
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_meta(
  obj: LeanIxonConstantMeta<LeanBorrowed<'_>>,
) -> LeanIxonConstantMeta<LeanOwned> {
  let meta = obj.decode();
  LeanIxonConstantMeta::build(&meta)
}

/// Round-trip Ixon.Named (with real metadata).
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_named(
  obj: LeanIxonNamed<LeanBorrowed<'_>>,
) -> LeanIxonNamed<LeanOwned> {
  let named = obj.decode();
  LeanIxonNamed::build(&named.addr, &named.meta)
}
