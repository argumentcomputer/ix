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

use std::ffi::{c_void, CString};

use crate::ix::env::{BinderInfo, DataValue, Expr, ExprData, Level, Literal, Name};
use crate::lean::array::LeanArrayObject;
use crate::lean::nat::Nat;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_box_fn,
  lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_inc, lean_mk_string, lean_obj_tag,
};

use super::super::builder::LeanBuildCache;
use super::super::primitives::build_nat;
use super::address::build_address;
use super::data::{build_data_value, decode_data_value};
use super::level::{build_level, build_level_array, decode_ix_level};
use super::name::{build_name, decode_ix_name};

/// Build a Lean Ix.Expr with embedded hash.
/// Uses caching to avoid rebuilding the same expression.
pub fn build_expr(cache: &mut LeanBuildCache, expr: &Expr) -> *mut c_void {
  let hash = *expr.get_hash();
  if let Some(&cached) = cache.exprs.get(&hash) {
    unsafe { lean_inc(cached) };
    return cached;
  }

  let result = unsafe {
    match expr.as_data() {
      ExprData::Bvar(idx, h) => {
        let obj = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(obj, 0, build_nat(idx));
        lean_ctor_set(obj, 1, build_address(h));
        obj
      }
      ExprData::Fvar(name, h) => {
        let obj = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(obj, 0, build_name(cache, name));
        lean_ctor_set(obj, 1, build_address(h));
        obj
      }
      ExprData::Mvar(name, h) => {
        let obj = lean_alloc_ctor(2, 2, 0);
        lean_ctor_set(obj, 0, build_name(cache, name));
        lean_ctor_set(obj, 1, build_address(h));
        obj
      }
      ExprData::Sort(level, h) => {
        let obj = lean_alloc_ctor(3, 2, 0);
        lean_ctor_set(obj, 0, build_level(cache, level));
        lean_ctor_set(obj, 1, build_address(h));
        obj
      }
      ExprData::Const(name, levels, h) => {
        let name_obj = build_name(cache, name);
        let levels_obj = build_level_array(cache, levels);
        let obj = lean_alloc_ctor(4, 3, 0);
        lean_ctor_set(obj, 0, name_obj);
        lean_ctor_set(obj, 1, levels_obj);
        lean_ctor_set(obj, 2, build_address(h));
        obj
      }
      ExprData::App(fn_expr, arg_expr, h) => {
        let fn_obj = build_expr(cache, fn_expr);
        let arg_obj = build_expr(cache, arg_expr);
        let obj = lean_alloc_ctor(5, 3, 0);
        lean_ctor_set(obj, 0, fn_obj);
        lean_ctor_set(obj, 1, arg_obj);
        lean_ctor_set(obj, 2, build_address(h));
        obj
      }
      ExprData::Lam(name, ty, body, bi, h) => {
        let name_obj = build_name(cache, name);
        let ty_obj = build_expr(cache, ty);
        let body_obj = build_expr(cache, body);
        let hash_obj = build_address(h);
        // 4 object fields, 1 scalar byte for BinderInfo
        let obj = lean_alloc_ctor(6, 4, 1);
        lean_ctor_set(obj, 0, name_obj);
        lean_ctor_set(obj, 1, ty_obj);
        lean_ctor_set(obj, 2, body_obj);
        lean_ctor_set(obj, 3, hash_obj);
        lean_ctor_set_uint8(obj, 4 * 8, binder_info_to_u8(bi));
        obj
      }
      ExprData::ForallE(name, ty, body, bi, h) => {
        let name_obj = build_name(cache, name);
        let ty_obj = build_expr(cache, ty);
        let body_obj = build_expr(cache, body);
        let hash_obj = build_address(h);
        let obj = lean_alloc_ctor(7, 4, 1);
        lean_ctor_set(obj, 0, name_obj);
        lean_ctor_set(obj, 1, ty_obj);
        lean_ctor_set(obj, 2, body_obj);
        lean_ctor_set(obj, 3, hash_obj);
        lean_ctor_set_uint8(obj, 4 * 8, binder_info_to_u8(bi));
        obj
      }
      ExprData::LetE(name, ty, val, body, non_dep, h) => {
        let name_obj = build_name(cache, name);
        let ty_obj = build_expr(cache, ty);
        let val_obj = build_expr(cache, val);
        let body_obj = build_expr(cache, body);
        let hash_obj = build_address(h);
        // 5 object fields, 1 scalar byte for Bool
        let obj = lean_alloc_ctor(8, 5, 1);
        lean_ctor_set(obj, 0, name_obj);
        lean_ctor_set(obj, 1, ty_obj);
        lean_ctor_set(obj, 2, val_obj);
        lean_ctor_set(obj, 3, body_obj);
        lean_ctor_set(obj, 4, hash_obj);
        lean_ctor_set_uint8(obj, 5 * 8, *non_dep as u8);
        obj
      }
      ExprData::Lit(lit, h) => {
        let lit_obj = build_literal(lit);
        let obj = lean_alloc_ctor(9, 2, 0);
        lean_ctor_set(obj, 0, lit_obj);
        lean_ctor_set(obj, 1, build_address(h));
        obj
      }
      ExprData::Mdata(md, inner, h) => {
        let md_obj = build_mdata_array(cache, md);
        let inner_obj = build_expr(cache, inner);
        let obj = lean_alloc_ctor(10, 3, 0);
        lean_ctor_set(obj, 0, md_obj);
        lean_ctor_set(obj, 1, inner_obj);
        lean_ctor_set(obj, 2, build_address(h));
        obj
      }
      ExprData::Proj(type_name, idx, struct_expr, h) => {
        let name_obj = build_name(cache, type_name);
        let idx_obj = build_nat(idx);
        let struct_obj = build_expr(cache, struct_expr);
        let obj = lean_alloc_ctor(11, 4, 0);
        lean_ctor_set(obj, 0, name_obj);
        lean_ctor_set(obj, 1, idx_obj);
        lean_ctor_set(obj, 2, struct_obj);
        lean_ctor_set(obj, 3, build_address(h));
        obj
      }
    }
  };

  cache.exprs.insert(hash, result);
  result
}

/// Build an Array of (Name × DataValue) for mdata.
fn build_mdata_array(cache: &mut LeanBuildCache, md: &[(Name, DataValue)]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(md.len(), md.len());
    for (i, (name, dv)) in md.iter().enumerate() {
      let pair = build_name_datavalue_pair(cache, name, dv);
      lean_array_set_core(arr, i, pair);
    }
    arr
  }
}

/// Build a (Name, DataValue) pair (Prod).
fn build_name_datavalue_pair(cache: &mut LeanBuildCache, name: &Name, dv: &DataValue) -> *mut c_void {
  unsafe {
    let name_obj = build_name(cache, name);
    let dv_obj = build_data_value(cache, dv);
    let pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, name_obj);
    lean_ctor_set(pair, 1, dv_obj);
    pair
  }
}

/// Build a Literal (natVal or strVal).
pub fn build_literal(lit: &Literal) -> *mut c_void {
  unsafe {
    match lit {
      Literal::NatVal(n) => {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_nat(n));
        obj
      }
      Literal::StrVal(s) => {
        let s_cstr = CString::new(s.as_str()).unwrap();
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, lean_mk_string(s_cstr.as_ptr()));
        obj
      }
    }
  }
}

/// Build Ix.BinderInfo enum.
/// BinderInfo is a 4-constructor enum with no fields, stored as boxed scalar.
pub fn build_binder_info(bi: &BinderInfo) -> *mut c_void {
  lean_box_fn(binder_info_to_u8(bi) as usize)
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
pub fn decode_ix_expr(ptr: *const c_void) -> Expr {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // bvar
        let idx_ptr = lean_ctor_get(ptr as *mut _, 0);
        let idx = Nat::from_ptr(idx_ptr);
        Expr::bvar(idx)
      }
      1 => {
        // fvar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let name = decode_ix_name(name_ptr);
        Expr::fvar(name)
      }
      2 => {
        // mvar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let name = decode_ix_name(name_ptr);
        Expr::mvar(name)
      }
      3 => {
        // sort
        let level_ptr = lean_ctor_get(ptr as *mut _, 0);
        let level = decode_ix_level(level_ptr);
        Expr::sort(level)
      }
      4 => {
        // const
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let levels_ptr = lean_ctor_get(ptr as *mut _, 1);

        let name = decode_ix_name(name_ptr);
        let levels_obj: &LeanArrayObject = as_ref_unsafe(levels_ptr.cast());
        let levels: Vec<Level> = levels_obj.data().iter().map(|&p| decode_ix_level(p)).collect();

        Expr::cnst(name, levels)
      }
      5 => {
        // app
        let fn_ptr = lean_ctor_get(ptr as *mut _, 0);
        let arg_ptr = lean_ctor_get(ptr as *mut _, 1);
        let fn_expr = decode_ix_expr(fn_ptr);
        let arg_expr = decode_ix_expr(arg_ptr);
        Expr::app(fn_expr, arg_expr)
      }
      6 => {
        // lam: name, ty, body, hash, bi (scalar)
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_ptr = lean_ctor_get(ptr as *mut _, 1);
        let body_ptr = lean_ctor_get(ptr as *mut _, 2);
        // hash at field 3
        // bi is a scalar byte at offset 4*8

        let name = decode_ix_name(name_ptr);
        let ty = decode_ix_expr(ty_ptr);
        let body = decode_ix_expr(body_ptr);

        // Read BinderInfo scalar (4 obj fields: name, ty, body, hash)
        let ctor: &crate::lean::ctor::LeanCtorObject = as_ref_unsafe(ptr.cast());
        let bi_byte = ctor.get_scalar_u8(4, 0);
        let bi = decode_binder_info(bi_byte);

        Expr::lam(name, ty, body, bi)
      }
      7 => {
        // forallE: same layout as lam
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_ptr = lean_ctor_get(ptr as *mut _, 1);
        let body_ptr = lean_ctor_get(ptr as *mut _, 2);

        let name = decode_ix_name(name_ptr);
        let ty = decode_ix_expr(ty_ptr);
        let body = decode_ix_expr(body_ptr);

        // 4 obj fields: name, ty, body, hash
        let ctor: &crate::lean::ctor::LeanCtorObject = as_ref_unsafe(ptr.cast());
        let bi_byte = ctor.get_scalar_u8(4, 0);
        let bi = decode_binder_info(bi_byte);

        Expr::all(name, ty, body, bi)
      }
      8 => {
        // letE: name, ty, val, body, hash, nonDep (scalar)
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_ptr = lean_ctor_get(ptr as *mut _, 1);
        let val_ptr = lean_ctor_get(ptr as *mut _, 2);
        let body_ptr = lean_ctor_get(ptr as *mut _, 3);
        // hash at field 4
        // nonDep is scalar byte after 5 obj fields

        let name = decode_ix_name(name_ptr);
        let ty = decode_ix_expr(ty_ptr);
        let val = decode_ix_expr(val_ptr);
        let body = decode_ix_expr(body_ptr);

        // 5 obj fields: name, ty, val, body, hash
        let ctor: &crate::lean::ctor::LeanCtorObject = as_ref_unsafe(ptr.cast());
        let non_dep = ctor.get_scalar_u8(5, 0) != 0;

        Expr::letE(name, ty, val, body, non_dep)
      }
      9 => {
        // lit
        let lit_ptr = lean_ctor_get(ptr as *mut _, 0);
        let lit = decode_literal(lit_ptr);
        Expr::lit(lit)
      }
      10 => {
        // mdata: data, expr, hash
        let data_ptr = lean_ctor_get(ptr as *mut _, 0);
        let expr_ptr = lean_ctor_get(ptr as *mut _, 1);

        let data_obj: &LeanArrayObject = as_ref_unsafe(data_ptr.cast());
        let data: Vec<(Name, DataValue)> = data_obj
          .data()
          .iter()
          .map(|&p| decode_name_data_value(p))
          .collect();

        let inner = decode_ix_expr(expr_ptr);
        Expr::mdata(data, inner)
      }
      11 => {
        // proj: typeName, idx, struct, hash
        let type_name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let idx_ptr = lean_ctor_get(ptr as *mut _, 1);
        let struct_ptr = lean_ctor_get(ptr as *mut _, 2);

        let type_name = decode_ix_name(type_name_ptr);
        let idx = Nat::from_ptr(idx_ptr);
        let struct_expr = decode_ix_expr(struct_ptr);

        Expr::proj(type_name, idx, struct_expr)
      }
      _ => panic!("Invalid Ix.Expr tag: {}", tag),
    }
  }
}

/// Decode Lean.Literal from a Lean pointer.
pub fn decode_literal(ptr: *const c_void) -> Literal {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // natVal
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let nat = Nat::from_ptr(nat_ptr);
        Literal::NatVal(nat)
      }
      1 => {
        // strVal
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_obj: &LeanStringObject = as_ref_unsafe(str_ptr.cast());
        Literal::StrVal(str_obj.as_string())
      }
      _ => panic!("Invalid Literal tag: {}", tag),
    }
  }
}

/// Decode a (Name × DataValue) pair for mdata.
fn decode_name_data_value(ptr: *const c_void) -> (Name, DataValue) {
  unsafe {
    // Prod: ctor 0 with 2 fields
    let name_ptr = lean_ctor_get(ptr as *mut _, 0);
    let dv_ptr = lean_ctor_get(ptr as *mut _, 1);

    let name = decode_ix_name(name_ptr);
    let dv = decode_data_value(dv_ptr);

    (name, dv)
  }
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
pub extern "C" fn rs_roundtrip_ix_expr(expr_ptr: *const c_void) -> *mut c_void {
  let expr = decode_ix_expr(expr_ptr);
  let mut cache = LeanBuildCache::new();
  build_expr(&mut cache, &expr)
}
