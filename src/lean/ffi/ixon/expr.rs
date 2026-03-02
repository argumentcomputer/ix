//! Ixon.Expr build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::expr::Expr;
use crate::lean::obj::{IxonExpr, LeanArray, LeanCtor, LeanObj};

/// Decode Array UInt64 from Lean.
/// UInt64 values in arrays are stored as:
/// - Scalars (odd pointers) for small values: use unbox_usize
/// - Heap objects (even pointers) with the u64 value at offset 8
fn decode_u64_array(obj: LeanObj) -> Vec<u64> {
  let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
  arr.map(|elem| {
    if elem.is_scalar() {
      elem.unbox_usize() as u64
    } else {
      let ctor = unsafe { LeanCtor::from_raw(elem.as_ptr()) };
      ctor.scalar_u64(0, 0)
    }
  })
}

impl IxonExpr {
  /// Build Ixon.Expr (12 constructors).
  pub fn build(expr: &Expr) -> Self {
    let obj = match expr {
      Expr::Sort(idx) => {
        let ctor = LeanCtor::alloc(0, 0, 8);
        ctor.set_u64(0, *idx);
        *ctor
      },
      Expr::Var(idx) => {
        let ctor = LeanCtor::alloc(1, 0, 8);
        ctor.set_u64(0, *idx);
        *ctor
      },
      Expr::Ref(ref_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = LeanCtor::alloc(0, 0, 8);
          uint64_obj.set_u64(0, *idx);
          arr.set(i, uint64_obj);
        }
        let ctor = LeanCtor::alloc(2, 1, 8);
        ctor.set(0, arr);
        ctor.set_u64(8, *ref_idx);
        *ctor
      },
      Expr::Rec(rec_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = LeanCtor::alloc(0, 0, 8);
          uint64_obj.set_u64(0, *idx);
          arr.set(i, uint64_obj);
        }
        let ctor = LeanCtor::alloc(3, 1, 8);
        ctor.set(0, arr);
        ctor.set_u64(8, *rec_idx);
        *ctor
      },
      Expr::Prj(type_ref_idx, field_idx, val) => {
        let val_obj = Self::build(val);
        let ctor = LeanCtor::alloc(4, 1, 16);
        ctor.set(0, val_obj);
        ctor.set_u64(8, *type_ref_idx);
        ctor.set_u64(16, *field_idx);
        *ctor
      },
      Expr::Str(ref_idx) => {
        let ctor = LeanCtor::alloc(5, 0, 8);
        ctor.set_u64(0, *ref_idx);
        *ctor
      },
      Expr::Nat(ref_idx) => {
        let ctor = LeanCtor::alloc(6, 0, 8);
        ctor.set_u64(0, *ref_idx);
        *ctor
      },
      Expr::App(fun, arg) => {
        let fun_obj = Self::build(fun);
        let arg_obj = Self::build(arg);
        let ctor = LeanCtor::alloc(7, 2, 0);
        ctor.set(0, fun_obj);
        ctor.set(1, arg_obj);
        *ctor
      },
      Expr::Lam(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(8, 2, 0);
        ctor.set(0, ty_obj);
        ctor.set(1, body_obj);
        *ctor
      },
      Expr::All(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(9, 2, 0);
        ctor.set(0, ty_obj);
        ctor.set(1, body_obj);
        *ctor
      },
      Expr::Let(non_dep, ty, val, body) => {
        let ty_obj = Self::build(ty);
        let val_obj = Self::build(val);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(10, 3, 1);
        ctor.set(0, ty_obj);
        ctor.set(1, val_obj);
        ctor.set(2, body_obj);
        ctor.set_u8(3 * 8, if *non_dep { 1 } else { 0 });
        *ctor
      },
      Expr::Share(idx) => {
        let ctor = LeanCtor::alloc(11, 0, 8);
        ctor.set_u64(0, *idx);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Build an Array of Ixon.Expr.
  pub fn build_array(exprs: &[Arc<Expr>]) -> LeanArray {
    let arr = LeanArray::alloc(exprs.len());
    for (i, expr) in exprs.iter().enumerate() {
      arr.set(i, Self::build(expr));
    }
    arr
  }

  /// Decode Ixon.Expr (12 constructors).
  pub fn decode(self) -> Expr {
    let obj: LeanObj = *self;
    let ctor = unsafe { LeanCtor::from_raw(obj.as_ptr()) };
    match ctor.tag() {
      0 => Expr::Sort(ctor.scalar_u64(0, 0)),
      1 => Expr::Var(ctor.scalar_u64(0, 0)),
      2 => {
        let ref_idx = ctor.scalar_u64(1, 0);
        let univ_idxs = decode_u64_array(ctor.get(0));
        Expr::Ref(ref_idx, univ_idxs)
      },
      3 => {
        let rec_idx = ctor.scalar_u64(1, 0);
        let univ_idxs = decode_u64_array(ctor.get(0));
        Expr::Rec(rec_idx, univ_idxs)
      },
      4 => {
        let type_ref_idx = ctor.scalar_u64(1, 0);
        let field_idx = ctor.scalar_u64(1, 8);
        Expr::Prj(
          type_ref_idx,
          field_idx,
          Arc::new(Self::new(ctor.get(0)).decode()),
        )
      },
      5 => Expr::Str(ctor.scalar_u64(0, 0)),
      6 => Expr::Nat(ctor.scalar_u64(0, 0)),
      7 => Expr::App(
        Arc::new(Self::new(ctor.get(0)).decode()),
        Arc::new(Self::new(ctor.get(1)).decode()),
      ),
      8 => Expr::Lam(
        Arc::new(Self::new(ctor.get(0)).decode()),
        Arc::new(Self::new(ctor.get(1)).decode()),
      ),
      9 => Expr::All(
        Arc::new(Self::new(ctor.get(0)).decode()),
        Arc::new(Self::new(ctor.get(1)).decode()),
      ),
      10 => {
        let non_dep = ctor.scalar_bool(3, 0);
        Expr::Let(
          non_dep,
          Arc::new(Self::new(ctor.get(0)).decode()),
          Arc::new(Self::new(ctor.get(1)).decode()),
          Arc::new(Self::new(ctor.get(2)).decode()),
        )
      },
      11 => Expr::Share(ctor.scalar_u64(0, 0)),
      tag => panic!("Invalid Ixon.Expr tag: {tag}"),
    }
  }

  /// Decode Array Ixon.Expr.
  pub fn decode_array(obj: LeanObj) -> Vec<Arc<Expr>> {
    let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
    arr.map(|e| Arc::new(Self::new(e).decode()))
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Expr.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr(obj: LeanObj) -> LeanObj {
  let expr = IxonExpr::new(obj).decode();
  IxonExpr::build(&expr).into()
}
