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
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanOwned, LeanProd, LeanRef};

use crate::lean::LeanIxAddress;
use crate::lean::LeanIxBinderInfo;

// =============================================================================
// KVMap Build/Decode (not domain types, kept as free functions)
// =============================================================================

/// Build an Ixon.KVMap (Array (Address × DataValue)).
pub fn build_ixon_kvmap(kvmap: &KVMap) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(kvmap.len());
  for (i, (addr, dv)) in kvmap.iter().enumerate() {
    let pair =
      LeanProd::new(LeanIxAddress::build(addr), LeanIxonDataValue::build(dv));
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
    match dv {
      IxonDataValue::OfString(addr) => {
        let ctor = LeanIxonDataValue::alloc(0);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      IxonDataValue::OfBool(b) => {
        let ctor = LeanIxonDataValue::alloc(1);
        ctor.set_num_8(0, *b as u8);
        ctor
      },
      IxonDataValue::OfName(addr) => {
        let ctor = LeanIxonDataValue::alloc(2);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      IxonDataValue::OfNat(addr) => {
        let ctor = LeanIxonDataValue::alloc(3);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      IxonDataValue::OfInt(addr) => {
        let ctor = LeanIxonDataValue::alloc(4);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
      IxonDataValue::OfSyntax(addr) => {
        let ctor = LeanIxonDataValue::alloc(5);
        ctor.set_obj(0, LeanIxAddress::build(addr));
        ctor
      },
    }
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
        let b = self.get_num_8(0) != 0;
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
    match node {
      ExprMetaData::Leaf => Self::new(LeanOwned::box_usize(0)),

      ExprMetaData::App { children } => {
        let ctor = LeanIxonExprMetaData::alloc(1);
        ctor.set_num_64(0, children[0]);
        ctor.set_num_64(1, children[1]);
        ctor
      },

      ExprMetaData::Binder { name, info, children } => {
        let ctor = LeanIxonExprMetaData::alloc(2);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_num_64(0, children[0]);
        ctor.set_num_64(1, children[1]);
        ctor.set_num_8(0, LeanIxBinderInfo::to_u8(info));
        ctor
      },

      ExprMetaData::LetBinder { name, children } => {
        let ctor = LeanIxonExprMetaData::alloc(3);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_num_64(0, children[0]);
        ctor.set_num_64(1, children[1]);
        ctor.set_num_64(2, children[2]);
        ctor
      },

      ExprMetaData::Ref { name } => {
        let ctor = LeanIxonExprMetaData::alloc(4);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor
      },

      ExprMetaData::Prj { struct_name, child } => {
        let ctor = LeanIxonExprMetaData::alloc(5);
        ctor.set_obj(0, LeanIxAddress::build(struct_name));
        ctor.set_num_64(0, *child);
        ctor
      },

      ExprMetaData::Mdata { mdata, child } => {
        let mdata_arr = build_kvmap_array(mdata);
        let ctor = LeanIxonExprMetaData::alloc(6);
        ctor.set_obj(0, mdata_arr);
        ctor.set_num_64(0, *child);
        ctor
      },
    }
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
        let fun_ = self.get_num_64(0);
        let arg = self.get_num_64(1);
        ExprMetaData::App { children: [fun_, arg] }
      },

      2 => {
        // binder: 1 obj field (name), scalar (Lean ABI: u64s first, then u8):
        let name =
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let ty_child = self.get_num_64(0);
        let body_child = self.get_num_64(1);
        let info_byte = self.get_num_8(0);
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
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let ty_child = self.get_num_64(0);
        let val_child = self.get_num_64(1);
        let body_child = self.get_num_64(2);
        ExprMetaData::LetBinder {
          name,
          children: [ty_child, val_child, body_child],
        }
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
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let child = self.get_num_64(0);
        ExprMetaData::Prj { struct_name, child }
      },

      6 => {
        // mdata: 1 obj field (mdata: Array KVMap), 1× u64 scalar
        let mdata = decode_kvmap_array(self.get_obj(0).as_array());
        let child = self.get_num_64(0);
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
    match meta {
      ConstantMeta::Empty => Self::new(LeanOwned::box_usize(0)),

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
        let ctor = LeanIxonConstantMeta::alloc(1);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxReducibilityHints::build(hints));
        ctor.set_obj(3, LeanIxAddress::build_array(all));
        ctor.set_obj(4, LeanIxAddress::build_array(ctx));
        ctor.set_obj(5, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor.set_num_64(1, *value_root);
        ctor
      },

      ConstantMeta::Axio { name, lvls, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(2);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
      },

      ConstantMeta::Quot { name, lvls, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(3);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
      },

      ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(4);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxAddress::build_array(ctors));
        ctor.set_obj(3, LeanIxAddress::build_array(all));
        ctor.set_obj(4, LeanIxAddress::build_array(ctx));
        ctor.set_obj(5, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
      },

      ConstantMeta::Ctor { name, lvls, induct, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(5);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxAddress::build(induct));
        ctor.set_obj(3, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
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
        let ctor = LeanIxonConstantMeta::alloc(6);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxAddress::build_array(rules));
        ctor.set_obj(3, LeanIxAddress::build_array(all));
        ctor.set_obj(4, LeanIxAddress::build_array(ctx));
        ctor.set_obj(5, LeanIxonExprMetaArena::build(arena));
        ctor.set_obj(6, build_u64_array(rule_roots));
        ctor.set_num_64(0, *type_root);
        ctor
      },
    }
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
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let lvls = decode_address_array(self.get_obj(1).as_array());
        let hints =
          LeanIxReducibilityHints::new(self.get_obj(2).to_owned_ref()).decode();
        let all = decode_address_array(self.get_obj(3).as_array());
        let ctx = decode_address_array(self.get_obj(4).as_array());
        let arena =
          LeanIxonExprMetaArena::new(self.get_obj(5).to_owned_ref()).decode();
        let type_root = self.get_num_64(0);
        let value_root = self.get_num_64(1);
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
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let lvls = decode_address_array(self.get_obj(1).as_array());
        let arena =
          LeanIxonExprMetaArena::new(self.get_obj(2).to_owned_ref()).decode();
        let type_root = self.get_num_64(0);
        ConstantMeta::Axio { name, lvls, arena, type_root }
      },

      3 => {
        // quot: 3 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let lvls = decode_address_array(self.get_obj(1).as_array());
        let arena =
          LeanIxonExprMetaArena::new(self.get_obj(2).to_owned_ref()).decode();
        let type_root = self.get_num_64(0);
        ConstantMeta::Quot { name, lvls, arena, type_root }
      },

      4 => {
        // indc: 6 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let lvls = decode_address_array(self.get_obj(1).as_array());
        let ctors = decode_address_array(self.get_obj(2).as_array());
        let all = decode_address_array(self.get_obj(3).as_array());
        let ctx = decode_address_array(self.get_obj(4).as_array());
        let arena =
          LeanIxonExprMetaArena::new(self.get_obj(5).to_owned_ref()).decode();
        let type_root = self.get_num_64(0);
        ConstantMeta::Indc { name, lvls, ctors, all, ctx, arena, type_root }
      },

      5 => {
        // ctor: 4 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let lvls = decode_address_array(self.get_obj(1).as_array());
        let induct =
          LeanIxAddress::from_borrowed(self.get_obj(2).as_byte_array())
            .decode();
        let arena =
          LeanIxonExprMetaArena::new(self.get_obj(3).to_owned_ref()).decode();
        let type_root = self.get_num_64(0);
        ConstantMeta::Ctor { name, lvls, induct, arena, type_root }
      },

      6 => {
        // recr: 7 obj fields, 1× u64 scalar
        let name =
          LeanIxAddress::from_borrowed(self.get_obj(0).as_byte_array())
            .decode();
        let lvls = decode_address_array(self.get_obj(1).as_array());
        let rules = decode_address_array(self.get_obj(2).as_array());
        let all = decode_address_array(self.get_obj(3).as_array());
        let ctx = decode_address_array(self.get_obj(4).as_array());
        let arena =
          LeanIxonExprMetaArena::new(self.get_obj(5).to_owned_ref()).decode();
        let rule_roots = decode_u64_array(self.get_obj(6).as_array());
        let type_root = self.get_num_64(0);
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
    let ctor = LeanIxonNamed::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(addr));
    ctor.set_obj(1, LeanIxonConstantMeta::build(meta));
    ctor
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
    let ctor = LeanIxonComm::alloc(0);
    ctor.set_obj(0, LeanIxAddress::build(&comm.secret));
    ctor.set_obj(1, LeanIxAddress::build(&comm.payload));
    ctor
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
