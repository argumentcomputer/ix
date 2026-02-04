//! Ixon.Expr build/decode/roundtrip FFI.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core,
  lean_ctor_get, lean_ctor_set, lean_obj_tag,
};
use crate::lean_unbox;

/// Build Ixon.Expr (12 constructors).
pub fn build_ixon_expr(expr: &IxonExpr) -> *mut c_void {
  unsafe {
    match expr {
      IxonExpr::Sort(idx) => {
        let obj = lean_alloc_ctor(0, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *idx;
        obj
      },
      IxonExpr::Var(idx) => {
        let obj = lean_alloc_ctor(1, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *idx;
        obj
      },
      IxonExpr::Ref(ref_idx, univ_idxs) => {
        let arr = lean_alloc_array(univ_idxs.len(), univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          // Build heap-boxed UInt64: ctor with tag 0, 0 obj fields, 8 scalar bytes
          let uint64_obj = lean_alloc_ctor(0, 0, 8);
          let base = uint64_obj.cast::<u8>();
          *base.add(8).cast::<u64>() = *idx;
          lean_array_set_core(arr, i, uint64_obj);
        }
        let obj = lean_alloc_ctor(2, 1, 8);
        lean_ctor_set(obj, 0, arr);
        let base = obj.cast::<u8>();
        *base.add(8 + 8).cast::<u64>() = *ref_idx;
        obj
      },
      IxonExpr::Rec(rec_idx, univ_idxs) => {
        let arr = lean_alloc_array(univ_idxs.len(), univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = lean_alloc_ctor(0, 0, 8);
          let base = uint64_obj.cast::<u8>();
          *base.add(8).cast::<u64>() = *idx;
          lean_array_set_core(arr, i, uint64_obj);
        }
        let obj = lean_alloc_ctor(3, 1, 8);
        lean_ctor_set(obj, 0, arr);
        let base = obj.cast::<u8>();
        *base.add(8 + 8).cast::<u64>() = *rec_idx;
        obj
      },
      IxonExpr::Prj(type_ref_idx, field_idx, val) => {
        let val_obj = build_ixon_expr(val);
        let obj = lean_alloc_ctor(4, 1, 16);
        lean_ctor_set(obj, 0, val_obj);
        let base = obj.cast::<u8>();
        *base.add(8 + 8).cast::<u64>() = *type_ref_idx;
        *base.add(8 + 16).cast::<u64>() = *field_idx;
        obj
      },
      IxonExpr::Str(ref_idx) => {
        let obj = lean_alloc_ctor(5, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *ref_idx;
        obj
      },
      IxonExpr::Nat(ref_idx) => {
        let obj = lean_alloc_ctor(6, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *ref_idx;
        obj
      },
      IxonExpr::App(fun, arg) => {
        let fun_obj = build_ixon_expr(fun);
        let arg_obj = build_ixon_expr(arg);
        let obj = lean_alloc_ctor(7, 2, 0);
        lean_ctor_set(obj, 0, fun_obj);
        lean_ctor_set(obj, 1, arg_obj);
        obj
      },
      IxonExpr::Lam(ty, body) => {
        let ty_obj = build_ixon_expr(ty);
        let body_obj = build_ixon_expr(body);
        let obj = lean_alloc_ctor(8, 2, 0);
        lean_ctor_set(obj, 0, ty_obj);
        lean_ctor_set(obj, 1, body_obj);
        obj
      },
      IxonExpr::All(ty, body) => {
        let ty_obj = build_ixon_expr(ty);
        let body_obj = build_ixon_expr(body);
        let obj = lean_alloc_ctor(9, 2, 0);
        lean_ctor_set(obj, 0, ty_obj);
        lean_ctor_set(obj, 1, body_obj);
        obj
      },
      IxonExpr::Let(non_dep, ty, val, body) => {
        let ty_obj = build_ixon_expr(ty);
        let val_obj = build_ixon_expr(val);
        let body_obj = build_ixon_expr(body);
        let obj = lean_alloc_ctor(10, 3, 1);
        lean_ctor_set(obj, 0, ty_obj);
        lean_ctor_set(obj, 1, val_obj);
        lean_ctor_set(obj, 2, body_obj);
        let base = obj.cast::<u8>();
        *base.add(3 * 8 + 8) = if *non_dep { 1 } else { 0 };
        obj
      },
      IxonExpr::Share(idx) => {
        let obj = lean_alloc_ctor(11, 0, 8);
        let base = obj.cast::<u8>();
        *base.add(8).cast::<u64>() = *idx;
        obj
      },
    }
  }
}

/// Build an Array of Ixon.Expr.
pub fn build_ixon_expr_array(exprs: &[Arc<IxonExpr>]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(exprs.len(), exprs.len());
    for (i, expr) in exprs.iter().enumerate() {
      let expr_obj = build_ixon_expr(expr);
      lean_array_set_core(arr, i, expr_obj);
    }
    arr
  }
}

// =============================================================================
// Decode Functions
// =============================================================================

/// Decode Array UInt64 from Lean.
/// UInt64 values in arrays are stored as:
/// - Scalars (odd pointers) for small values: use lean_unbox
/// - Heap objects (even pointers) with the u64 value at offset 8
fn decode_u64_array(ptr: *const c_void) -> Vec<u64> {
  use crate::lean::lean_is_scalar;

  let arr: &crate::lean::array::LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(|elem| {
    if lean_is_scalar(elem) {
      // Small scalar value
      lean_unbox!(u64, elem)
    } else {
      // Heap-boxed UInt64: value is at offset 8 (after 8-byte header)
      unsafe {
        let base = elem.cast::<u8>();
        *base.add(8).cast::<u64>()
      }
    }
  })
}

/// Decode Ixon.Expr (12 constructors).
pub fn decode_ixon_expr(ptr: *const c_void) -> IxonExpr {
  unsafe {
    let tag = lean_obj_tag(ptr.cast_mut());
    match tag {
      0 => {
        // sort (idx : UInt64)
        let base = ptr.cast::<u8>();
        let idx = *base.add(8).cast::<u64>();
        IxonExpr::Sort(idx)
      },
      1 => {
        // var (idx : UInt64)
        let base = ptr.cast::<u8>();
        let idx = *base.add(8).cast::<u64>();
        IxonExpr::Var(idx)
      },
      2 => {
        // ref (refIdx : UInt64) (univIdxs : Array UInt64)
        let arr_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let base = ptr.cast::<u8>();
        let ref_idx = *base.add(8 + 8).cast::<u64>();
        let univ_idxs = decode_u64_array(arr_ptr);
        IxonExpr::Ref(ref_idx, univ_idxs)
      },
      3 => {
        // recur (recIdx : UInt64) (univIdxs : Array UInt64)
        let arr_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let base = ptr.cast::<u8>();
        let rec_idx = *base.add(8 + 8).cast::<u64>();
        let univ_idxs = decode_u64_array(arr_ptr);
        IxonExpr::Rec(rec_idx, univ_idxs)
      },
      4 => {
        // prj (typeRefIdx : UInt64) (fieldIdx : UInt64) (val : Expr)
        let val_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let base = ptr.cast::<u8>();
        let type_ref_idx = *base.add(8 + 8).cast::<u64>();
        let field_idx = *base.add(8 + 16).cast::<u64>();
        IxonExpr::Prj(
          type_ref_idx,
          field_idx,
          Arc::new(decode_ixon_expr(val_ptr)),
        )
      },
      5 => {
        // str (refIdx : UInt64)
        let base = ptr.cast::<u8>();
        let ref_idx = *base.add(8).cast::<u64>();
        IxonExpr::Str(ref_idx)
      },
      6 => {
        // nat (refIdx : UInt64)
        let base = ptr.cast::<u8>();
        let ref_idx = *base.add(8).cast::<u64>();
        IxonExpr::Nat(ref_idx)
      },
      7 => {
        // app (f a : Expr)
        let f_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let a_ptr = lean_ctor_get(ptr.cast_mut(), 1);
        IxonExpr::App(
          Arc::new(decode_ixon_expr(f_ptr)),
          Arc::new(decode_ixon_expr(a_ptr)),
        )
      },
      8 => {
        // lam (ty body : Expr)
        let ty_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let body_ptr = lean_ctor_get(ptr.cast_mut(), 1);
        IxonExpr::Lam(
          Arc::new(decode_ixon_expr(ty_ptr)),
          Arc::new(decode_ixon_expr(body_ptr)),
        )
      },
      9 => {
        // all (ty body : Expr)
        let ty_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let body_ptr = lean_ctor_get(ptr.cast_mut(), 1);
        IxonExpr::All(
          Arc::new(decode_ixon_expr(ty_ptr)),
          Arc::new(decode_ixon_expr(body_ptr)),
        )
      },
      10 => {
        // letE (nonDep : Bool) (ty val body : Expr)
        let ty_ptr = lean_ctor_get(ptr.cast_mut(), 0);
        let val_ptr = lean_ctor_get(ptr.cast_mut(), 1);
        let body_ptr = lean_ctor_get(ptr.cast_mut(), 2);
        let base = ptr.cast::<u8>();
        let non_dep = *base.add(3 * 8 + 8) != 0;
        IxonExpr::Let(
          non_dep,
          Arc::new(decode_ixon_expr(ty_ptr)),
          Arc::new(decode_ixon_expr(val_ptr)),
          Arc::new(decode_ixon_expr(body_ptr)),
        )
      },
      11 => {
        // share (idx : UInt64)
        let base = ptr.cast::<u8>();
        let idx = *base.add(8).cast::<u64>();
        IxonExpr::Share(idx)
      },
      _ => panic!("Invalid Ixon.Expr tag: {}", tag),
    }
  }
}

/// Decode Array Ixon.Expr.
pub fn decode_ixon_expr_array(ptr: *const c_void) -> Vec<Arc<IxonExpr>> {
  let arr: &crate::lean::array::LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr.to_vec(|e| Arc::new(decode_ixon_expr(e)))
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Expr.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr(ptr: *const c_void) -> *mut c_void {
  let expr = decode_ixon_expr(ptr);
  build_ixon_expr(&expr)
}
