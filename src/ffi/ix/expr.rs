//! Ix.Expr build/decode/roundtrip FFI.
//!
//! Ix.Expr layout (12 constructors):
//! - Tag 0: bvar (idx : Nat) (hash : Address)
//! - Tag 1: fvar (name : Name) (hash : Address)
//! - Tag 2: mvar (name : Name) (hash : Address)
//! - Tag 3: sort (level : Level) (hash : Address)
//! - Tag 4: const (name : Name) (levels : Array Level) (hash : Address)
//! - Tag 5: app (fn arg : Expr) (hash : Address)
//! - Tag 6: lam (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address)
//! - Tag 7: forallE (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address)
//! - Tag 8: letE (name : Name) (ty val body : Expr) (nonDep : Bool) (hash : Address)
//! - Tag 9: lit (l : Literal) (hash : Address)
//! - Tag 10: mdata (data : Array (Name × DataValue)) (expr : Expr) (hash : Address)
//! - Tag 11: proj (typeName : Name) (idx : Nat) (struct : Expr) (hash : Address)

use crate::ix::env::{
  BinderInfo, DataValue, Expr, ExprData, Level, Literal, Name,
};
use crate::lean::nat::Nat;
use crate::lean::object::{
  LeanArray, LeanCtor, LeanIxExpr, LeanObject, LeanString,
};

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::ix::address::build_address;
use crate::ffi::ix::data::{build_data_value, decode_data_value};
use crate::ffi::ix::level::{build_level, build_level_array, decode_ix_level};
use crate::ffi::ix::name::{build_name, decode_ix_name};
use crate::ffi::primitives::build_nat;

/// Build a Lean Ix.Expr with embedded hash.
/// Uses caching to avoid rebuilding the same expression.
pub fn build_expr(cache: &mut LeanBuildCache, expr: &Expr) -> LeanIxExpr {
  let hash = *expr.get_hash();
  if let Some(&cached) = cache.exprs.get(&hash) {
    cached.inc_ref();
    return cached;
  }

  let result = match expr.as_data() {
    ExprData::Bvar(idx, h) => {
      let obj = LeanCtor::alloc(0, 2, 0);
      obj.set(0, build_nat(idx));
      obj.set(1, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Fvar(name, h) => {
      let obj = LeanCtor::alloc(1, 2, 0);
      obj.set(0, build_name(cache, name));
      obj.set(1, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Mvar(name, h) => {
      let obj = LeanCtor::alloc(2, 2, 0);
      obj.set(0, build_name(cache, name));
      obj.set(1, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Sort(level, h) => {
      let obj = LeanCtor::alloc(3, 2, 0);
      obj.set(0, build_level(cache, level));
      obj.set(1, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Const(name, levels, h) => {
      let name_obj = build_name(cache, name);
      let levels_obj = build_level_array(cache, levels);
      let obj = LeanCtor::alloc(4, 3, 0);
      obj.set(0, name_obj);
      obj.set(1, levels_obj);
      obj.set(2, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::App(fn_expr, arg_expr, h) => {
      let fn_obj = build_expr(cache, fn_expr);
      let arg_obj = build_expr(cache, arg_expr);
      let obj = LeanCtor::alloc(5, 3, 0);
      obj.set(0, fn_obj);
      obj.set(1, arg_obj);
      obj.set(2, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Lam(name, ty, body, bi, h) => {
      let name_obj = build_name(cache, name);
      let ty_obj = build_expr(cache, ty);
      let body_obj = build_expr(cache, body);
      let hash_obj = build_address(h);
      // 4 object fields, 1 scalar byte for BinderInfo
      let obj = LeanCtor::alloc(6, 4, 1);
      obj.set(0, name_obj);
      obj.set(1, ty_obj);
      obj.set(2, body_obj);
      obj.set(3, hash_obj);
      obj.set_u8(4 * 8, binder_info_to_u8(bi));
      LeanIxExpr::new(*obj)
    },
    ExprData::ForallE(name, ty, body, bi, h) => {
      let name_obj = build_name(cache, name);
      let ty_obj = build_expr(cache, ty);
      let body_obj = build_expr(cache, body);
      let hash_obj = build_address(h);
      let obj = LeanCtor::alloc(7, 4, 1);
      obj.set(0, name_obj);
      obj.set(1, ty_obj);
      obj.set(2, body_obj);
      obj.set(3, hash_obj);
      obj.set_u8(4 * 8, binder_info_to_u8(bi));
      LeanIxExpr::new(*obj)
    },
    ExprData::LetE(name, ty, val, body, non_dep, h) => {
      let name_obj = build_name(cache, name);
      let ty_obj = build_expr(cache, ty);
      let val_obj = build_expr(cache, val);
      let body_obj = build_expr(cache, body);
      let hash_obj = build_address(h);
      // 5 object fields, 1 scalar byte for Bool
      let obj = LeanCtor::alloc(8, 5, 1);
      obj.set(0, name_obj);
      obj.set(1, ty_obj);
      obj.set(2, val_obj);
      obj.set(3, body_obj);
      obj.set(4, hash_obj);
      obj.set_u8(5 * 8, *non_dep as u8);
      LeanIxExpr::new(*obj)
    },
    ExprData::Lit(lit, h) => {
      let lit_obj = build_literal(lit);
      let obj = LeanCtor::alloc(9, 2, 0);
      obj.set(0, lit_obj);
      obj.set(1, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Mdata(md, inner, h) => {
      let md_obj = build_mdata_array(cache, md);
      let inner_obj = build_expr(cache, inner);
      let obj = LeanCtor::alloc(10, 3, 0);
      obj.set(0, md_obj);
      obj.set(1, inner_obj);
      obj.set(2, build_address(h));
      LeanIxExpr::new(*obj)
    },
    ExprData::Proj(type_name, idx, struct_expr, h) => {
      let name_obj = build_name(cache, type_name);
      let idx_obj = build_nat(idx);
      let struct_obj = build_expr(cache, struct_expr);
      let obj = LeanCtor::alloc(11, 4, 0);
      obj.set(0, name_obj);
      obj.set(1, idx_obj);
      obj.set(2, struct_obj);
      obj.set(3, build_address(h));
      LeanIxExpr::new(*obj)
    },
  };

  cache.exprs.insert(hash, result);
  result
}

/// Build an Array of (Name × DataValue) for mdata.
fn build_mdata_array(
  cache: &mut LeanBuildCache,
  md: &[(Name, DataValue)],
) -> LeanArray {
  let arr = LeanArray::alloc(md.len());
  for (i, (name, dv)) in md.iter().enumerate() {
    let pair = build_name_datavalue_pair(cache, name, dv);
    arr.set(i, pair);
  }
  arr
}

/// Build a (Name, DataValue) pair (Prod).
fn build_name_datavalue_pair(
  cache: &mut LeanBuildCache,
  name: &Name,
  dv: &DataValue,
) -> LeanObject {
  let name_obj = build_name(cache, name);
  let dv_obj = build_data_value(cache, dv);
  let pair = LeanCtor::alloc(0, 2, 0);
  pair.set(0, name_obj);
  pair.set(1, dv_obj);
  *pair
}

/// Build a Literal (natVal or strVal).
pub fn build_literal(lit: &Literal) -> LeanObject {
  match lit {
    Literal::NatVal(n) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, build_nat(n));
      *obj
    },
    Literal::StrVal(s) => {
      let obj = LeanCtor::alloc(1, 1, 0);
      obj.set(0, LeanString::new(s.as_str()));
      *obj
    },
  }
}

/// Build Ix.BinderInfo enum.
/// BinderInfo is a 4-constructor enum with no fields, stored as boxed scalar.
pub fn build_binder_info(bi: &BinderInfo) -> LeanObject {
  LeanObject::box_usize(binder_info_to_u8(bi) as usize)
}

/// Convert BinderInfo to u8 tag.
pub fn binder_info_to_u8(bi: &BinderInfo) -> u8 {
  match bi {
    BinderInfo::Default => 0,
    BinderInfo::Implicit => 1,
    BinderInfo::StrictImplicit => 2,
    BinderInfo::InstImplicit => 3,
  }
}

/// Decode a Lean Ix.Expr to Rust Expr.
pub fn decode_ix_expr(obj: LeanObject) -> Expr {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      // bvar
      let idx = Nat::from_obj(ctor.get(0));
      Expr::bvar(idx)
    },
    1 => {
      // fvar
      let name = decode_ix_name(ctor.get(0));
      Expr::fvar(name)
    },
    2 => {
      // mvar
      let name = decode_ix_name(ctor.get(0));
      Expr::mvar(name)
    },
    3 => {
      // sort
      let level = decode_ix_level(ctor.get(0));
      Expr::sort(level)
    },
    4 => {
      // const
      let name = decode_ix_name(ctor.get(0));
      let levels: Vec<Level> = ctor.get(1).as_array().map(decode_ix_level);

      Expr::cnst(name, levels)
    },
    5 => {
      // app
      let fn_expr = decode_ix_expr(ctor.get(0));
      let arg_expr = decode_ix_expr(ctor.get(1));
      Expr::app(fn_expr, arg_expr)
    },
    6 => {
      // lam: name, ty, body, hash, bi (scalar)
      let name = decode_ix_name(ctor.get(0));
      let ty = decode_ix_expr(ctor.get(1));
      let body = decode_ix_expr(ctor.get(2));

      // Read BinderInfo scalar (4 obj fields: name, ty, body, hash)
      let bi_byte = ctor.scalar_u8(4, 0);
      let bi = decode_binder_info(bi_byte);

      Expr::lam(name, ty, body, bi)
    },
    7 => {
      // forallE: same layout as lam
      let name = decode_ix_name(ctor.get(0));
      let ty = decode_ix_expr(ctor.get(1));
      let body = decode_ix_expr(ctor.get(2));

      // 4 obj fields: name, ty, body, hash
      let bi_byte = ctor.scalar_u8(4, 0);
      let bi = decode_binder_info(bi_byte);

      Expr::all(name, ty, body, bi)
    },
    8 => {
      // letE: name, ty, val, body, hash, nonDep (scalar)
      let name = decode_ix_name(ctor.get(0));
      let ty = decode_ix_expr(ctor.get(1));
      let val = decode_ix_expr(ctor.get(2));
      let body = decode_ix_expr(ctor.get(3));

      // 5 obj fields: name, ty, val, body, hash
      let non_dep = ctor.scalar_u8(5, 0) != 0;

      Expr::letE(name, ty, val, body, non_dep)
    },
    9 => {
      // lit
      let lit = decode_literal(ctor.get(0));
      Expr::lit(lit)
    },
    10 => {
      // mdata: data, expr, hash
      let data: Vec<(Name, DataValue)> =
        ctor.get(0).as_array().map(decode_name_data_value);

      let inner = decode_ix_expr(ctor.get(1));
      Expr::mdata(data, inner)
    },
    11 => {
      // proj: typeName, idx, struct, hash
      let type_name = decode_ix_name(ctor.get(0));
      let idx = Nat::from_obj(ctor.get(1));
      let struct_expr = decode_ix_expr(ctor.get(2));

      Expr::proj(type_name, idx, struct_expr)
    },
    _ => panic!("Invalid Ix.Expr tag: {}", ctor.tag()),
  }
}

/// Decode Lean.Literal from a Lean object.
pub fn decode_literal(obj: LeanObject) -> Literal {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      // natVal
      let nat = Nat::from_obj(ctor.get(0));
      Literal::NatVal(nat)
    },
    1 => {
      // strVal
      Literal::StrVal(ctor.get(0).as_string().to_string())
    },
    _ => panic!("Invalid Literal tag: {}", ctor.tag()),
  }
}

/// Decode a (Name × DataValue) pair for mdata.
fn decode_name_data_value(obj: LeanObject) -> (Name, DataValue) {
  // Prod: ctor 0 with 2 fields
  let ctor = obj.as_ctor();
  let name = decode_ix_name(ctor.get(0));
  let dv = decode_data_value(ctor.get(1));
  (name, dv)
}

/// Decode BinderInfo from byte.
pub fn decode_binder_info(bi_byte: u8) -> BinderInfo {
  match bi_byte {
    0 => BinderInfo::Default,
    1 => BinderInfo::Implicit,
    2 => BinderInfo::StrictImplicit,
    3 => BinderInfo::InstImplicit,
    _ => panic!("Invalid BinderInfo: {}", bi_byte),
  }
}

/// Round-trip an Ix.Expr: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_expr(expr_ptr: LeanIxExpr) -> LeanIxExpr {
  let expr = decode_ix_expr(*expr_ptr);
  let mut cache = LeanBuildCache::new();
  build_expr(&mut cache, &expr)
}
