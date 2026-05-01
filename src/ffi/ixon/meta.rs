//! Ixon metadata types build/decode/roundtrip FFI.
//!
//! Includes: DataValue, KVMap, ExprMetaData, ExprMetaArena, ConstantMeta, Named, Comm

use crate::ix::address::Address;
use crate::ix::env::BinderInfo;
use crate::ix::ixon::Comm;
use crate::ix::ixon::env::Named;
use crate::ix::ixon::metadata::{
  ConstantMeta, ConstantMetaInfo, DataValue as IxonDataValue, ExprMeta,
  ExprMetaData, KVMap,
};
use crate::lean::{
  LeanIxReducibilityHints, LeanIxonComm, LeanIxonConstantMeta,
  LeanIxonDataValue, LeanIxonExprMetaArena, LeanIxonExprMetaData,
  LeanIxonNamed,
};
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanCtor, LeanOwned, LeanProd, LeanRef,
};

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

      ExprMetaData::CallSite { .. } => {
        // CallSite is internal to the Rust surgery pipeline and is not
        // exposed to the Lean FFI. Represent as a Leaf for now.
        Self::new(LeanOwned::box_usize(0))
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
    match &meta.info {
      ConstantMetaInfo::Empty => Self::new(LeanOwned::box_usize(0)),

      ConstantMetaInfo::Def {
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

      ConstantMetaInfo::Axio { name, lvls, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(2);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
      },

      ConstantMetaInfo::Quot { name, lvls, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(3);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
      },

      ConstantMetaInfo::Indc {
        name,
        lvls,
        ctors,
        all,
        ctx,
        arena,
        type_root,
      } => {
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

      ConstantMetaInfo::Ctor { name, lvls, induct, arena, type_root } => {
        let ctor = LeanIxonConstantMeta::alloc(5);
        ctor.set_obj(0, LeanIxAddress::build(name));
        ctor.set_obj(1, LeanIxAddress::build_array(lvls));
        ctor.set_obj(2, LeanIxAddress::build(induct));
        ctor.set_obj(3, LeanIxonExprMetaArena::build(arena));
        ctor.set_num_64(0, *type_root);
        ctor
      },

      ConstantMetaInfo::Rec {
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

      ConstantMetaInfo::Muts { all, aux_layout: _ } => {
        // Muts is a Rust-only ConstantMeta variant (Lean's ConstantMeta
        // has no `muts` constructor — `Ix/Ixon.lean`). The FFI build
        // path for Muts is effectively dead because Lean never materializes
        // a Muts meta; keeping the stub here preserves the historical
        // tag-7 encoding for any Rust-side code that still reflects a
        // Muts meta through the FFI roundtrip test (`rs_roundtrip_ixon_named`).
        //
        // `aux_layout` is intentionally NOT encoded through the FFI —
        // the Lean side has no field for it, and anything crossing the
        // FFI would immediately drop it on the next Rust-side build.
        // Aux_layout round-tripping lives entirely in `put_indexed` /
        // `get_indexed` (Rust-internal serialization).
        let ctor = LeanIxonConstantMeta::alloc(7);
        let outer = LeanArray::alloc(all.len());
        for (i, group) in all.iter().enumerate() {
          outer.set(i, LeanIxAddress::build_array(group));
        }
        ctor.set_obj(0, outer);
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
      return ConstantMeta::default();
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
        ConstantMeta::new(ConstantMetaInfo::Def {
          name,
          lvls,
          hints,
          all,
          ctx,
          arena,
          type_root,
          value_root,
        })
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
        ConstantMeta::new(ConstantMetaInfo::Axio {
          name,
          lvls,
          arena,
          type_root,
        })
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
        ConstantMeta::new(ConstantMetaInfo::Quot {
          name,
          lvls,
          arena,
          type_root,
        })
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
        ConstantMeta::new(ConstantMetaInfo::Indc {
          name,
          lvls,
          ctors,
          all,
          ctx,
          arena,
          type_root,
        })
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
        ConstantMeta::new(ConstantMetaInfo::Ctor {
          name,
          lvls,
          induct,
          arena,
          type_root,
        })
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
        ConstantMeta::new(ConstantMetaInfo::Rec {
          name,
          lvls,
          rules,
          all,
          ctx,
          arena,
          type_root,
          rule_roots,
        })
      },

      7 => {
        // muts: 1 obj field (Array (Array Address)), 0 scalar
        //
        // `aux_layout` is not carried across the FFI — Lean's
        // ConstantMeta has no `muts` variant, so the only path here is
        // the Rust-internal roundtrip test. We default to `None` on
        // decode; the real aux_layout data survives through the
        // Rust-side `put_indexed` / `get_indexed` path instead.
        let outer = ctor.get(0).as_array();
        let mut all = Vec::with_capacity(outer.len());
        for i in 0..outer.len() {
          all.push(decode_address_array(outer.get(i).as_array()));
        }
        ConstantMeta::new(ConstantMetaInfo::Muts { all, aux_layout: None })
      },

      tag => panic!("Invalid Ixon.ConstantMeta tag: {}", tag),
    }
  }
}

// =============================================================================
// Named and Comm Build/Decode
// =============================================================================

impl LeanIxonNamed<LeanOwned> {
  /// Build Ixon.Named { addr, constMeta, original }.
  ///
  /// The Lean structure (see `Ix/Ixon.lean` `structure Named`) has three
  /// fields: the constant's address, its typed metadata, and an optional
  /// pre-aux_gen original form used by the decompile path for roundtrip
  /// fidelity. We must match that 3-slot layout exactly — allocating a
  /// 2-slot ctor causes Lean-side reads of slot 2 to walk past the
  /// constructor and SIGSEGV. See the FFI roundtrip test
  /// `Ixon.Named roundtrip` in `Tests/FFI/Ixon.lean`.
  ///
  /// The `original` slot encodes `Option (Address × ConstantMeta)` using
  /// Lean's boxed-tagged-union convention:
  ///   `none`        → tag 0, 0 fields
  ///   `some (a, m)` → tag 1, 1 field (a `Prod`: tag 0, 2 fields)
  pub fn build(
    addr: &Address,
    meta: &ConstantMeta,
    original: &Option<(Address, ConstantMeta)>,
  ) -> Self {
    let addr_obj = LeanIxAddress::build(addr);
    let meta_obj = LeanIxonConstantMeta::build(meta);
    let original_obj: LeanOwned = match original {
      None => {
        // `Option.none` — zero-field ctor with tag 0.
        LeanCtor::alloc(0, 0, 0).into()
      },
      Some((orig_addr, orig_meta)) => {
        // Build the inner pair `(orig_addr, orig_meta) : Address × ConstantMeta`.
        let pair = LeanCtor::alloc(0, 2, 0);
        pair.set(0, LeanIxAddress::build(orig_addr));
        pair.set(1, LeanIxonConstantMeta::build(orig_meta));
        // Wrap in `Option.some` — tag 1, one field.
        let some_ctor = LeanCtor::alloc(1, 1, 0);
        some_ctor.set(0, pair);
        some_ctor.into()
      },
    };
    let ctor = LeanCtor::alloc(0, 3, 0);
    ctor.set(0, addr_obj);
    ctor.set(1, meta_obj);
    ctor.set(2, original_obj);
    Self::new(ctor.into())
  }
}

impl<R: LeanRef> LeanIxonNamed<R> {
  /// Decode Ixon.Named.
  ///
  /// Mirrors `build`: reads three slots. The third slot is an
  /// `Option (Address × ConstantMeta)` which Lean may represent either as
  /// a scalar-optimized `Option.none` or as a boxed tagged ctor. We handle
  /// both by checking `is_scalar()` before calling `as_ctor()`.
  pub fn decode(&self) -> Named {
    let ctor = self.as_ctor();
    let addr =
      LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
    let meta = LeanIxonConstantMeta::new(ctor.get(1).to_owned_ref()).decode();
    let original_obj = ctor.get(2);
    let original: Option<(Address, ConstantMeta)> = if original_obj.is_scalar()
    {
      // Scalar-optimized `Option.none`.
      None
    } else {
      let opt = original_obj.as_ctor();
      match opt.tag() {
        0 => None,
        1 => {
          let pair = opt.get(0).as_ctor();
          let orig_addr =
            LeanIxAddress::from_borrowed(pair.get(0).as_byte_array()).decode();
          let orig_meta =
            LeanIxonConstantMeta::new(pair.get(1).to_owned_ref()).decode();
          Some((orig_addr, orig_meta))
        },
        tag => panic!("Invalid Option tag for Named.original: {tag}"),
      }
    };
    Named { addr, meta, original }
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

/// Round-trip Ixon.Named (with real metadata and optional pre-aux_gen
/// original form).
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_named(
  obj: LeanIxonNamed<LeanBorrowed<'_>>,
) -> LeanIxonNamed<LeanOwned> {
  let named = obj.decode();
  LeanIxonNamed::build(&named.addr, &named.meta, &named.original)
}
