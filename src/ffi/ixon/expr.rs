//! Ixon.Expr build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::lean::LeanIxonExpr;
use lean_ffi::object::{LeanArray, LeanCtor};

/// Decode Array UInt64 from Lean.
fn decode_u64_array(obj: LeanArray) -> Vec<u64> {
  obj
    .iter()
    .map(|elem| {
      if elem.is_scalar() {
        elem.unbox_usize() as u64
      } else {
        let ctor = elem.as_ctor();
        ctor.scalar_u64(0, 0)
      }
    })
    .collect()
}

impl LeanIxonExpr {
  /// Build Ixon.Expr (12 constructors).
  pub fn build(expr: &IxonExpr) -> Self {
    let obj = match expr {
      IxonExpr::Sort(idx) => {
        let ctor = LeanCtor::alloc(0, 0, 8);
        ctor.set_scalar_u64(0, 0, *idx);
        *ctor
      },
      IxonExpr::Var(idx) => {
        let ctor = LeanCtor::alloc(1, 0, 8);
        ctor.set_scalar_u64(0, 0, *idx);
        *ctor
      },
      IxonExpr::Ref(ref_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = LeanCtor::alloc(0, 0, 8);
          uint64_obj.set_scalar_u64(0, 0, *idx);
          arr.set(i, uint64_obj);
        }
        let ctor = LeanCtor::alloc(2, 1, 8);
        ctor.set(0, arr);
        ctor.set_scalar_u64(1, 0, *ref_idx);
        *ctor
      },
      IxonExpr::Rec(rec_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = LeanCtor::alloc(0, 0, 8);
          uint64_obj.set_scalar_u64(0, 0, *idx);
          arr.set(i, uint64_obj);
        }
        let ctor = LeanCtor::alloc(3, 1, 8);
        ctor.set(0, arr);
        ctor.set_scalar_u64(1, 0, *rec_idx);
        *ctor
      },
      IxonExpr::Prj(type_ref_idx, field_idx, val) => {
        let val_obj = Self::build(val);
        let ctor = LeanCtor::alloc(4, 1, 16);
        ctor.set(0, val_obj);
        ctor.set_scalar_u64(1, 0, *type_ref_idx);
        ctor.set_scalar_u64(1, 8, *field_idx);
        *ctor
      },
      IxonExpr::Str(ref_idx) => {
        let ctor = LeanCtor::alloc(5, 0, 8);
        ctor.set_scalar_u64(0, 0, *ref_idx);
        *ctor
      },
      IxonExpr::Nat(ref_idx) => {
        let ctor = LeanCtor::alloc(6, 0, 8);
        ctor.set_scalar_u64(0, 0, *ref_idx);
        *ctor
      },
      IxonExpr::App(fun, arg) => {
        let fun_obj = Self::build(fun);
        let arg_obj = Self::build(arg);
        let ctor = LeanCtor::alloc(7, 2, 0);
        ctor.set(0, fun_obj);
        ctor.set(1, arg_obj);
        *ctor
      },
      IxonExpr::Lam(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(8, 2, 0);
        ctor.set(0, ty_obj);
        ctor.set(1, body_obj);
        *ctor
      },
      IxonExpr::All(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(9, 2, 0);
        ctor.set(0, ty_obj);
        ctor.set(1, body_obj);
        *ctor
      },
      IxonExpr::Let(non_dep, ty, val, body) => {
        let ty_obj = Self::build(ty);
        let val_obj = Self::build(val);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(10, 3, 1);
        ctor.set(0, ty_obj);
        ctor.set(1, val_obj);
        ctor.set(2, body_obj);
        ctor.set_scalar_u8(3, 0, if *non_dep { 1 } else { 0 });
        *ctor
      },
      IxonExpr::Share(idx) => {
        let ctor = LeanCtor::alloc(11, 0, 8);
        ctor.set_scalar_u64(0, 0, *idx);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Build an Array of Ixon.Expr.
  pub fn build_array(exprs: &[Arc<IxonExpr>]) -> LeanArray {
    let arr = LeanArray::alloc(exprs.len());
    for (i, expr) in exprs.iter().enumerate() {
      arr.set(i, Self::build(expr));
    }
    arr
  }

  /// Decode Ixon.Expr (12 constructors).
  pub fn decode(self) -> IxonExpr {
    let ctor = self.as_ctor();
    let tag = ctor.tag();
    match tag {
      0 => {
        let idx = ctor.scalar_u64(0, 0);
        IxonExpr::Sort(idx)
      },
      1 => {
        let idx = ctor.scalar_u64(0, 0);
        IxonExpr::Var(idx)
      },
      2 => {
        let ref_idx = ctor.scalar_u64(1, 0);
        let univ_idxs = decode_u64_array(ctor.get(0).as_array());
        IxonExpr::Ref(ref_idx, univ_idxs)
      },
      3 => {
        let rec_idx = ctor.scalar_u64(1, 0);
        let univ_idxs = decode_u64_array(ctor.get(0).as_array());
        IxonExpr::Rec(rec_idx, univ_idxs)
      },
      4 => {
        let val_obj = Self::new(ctor.get(0));
        let type_ref_idx = ctor.scalar_u64(1, 0);
        let field_idx = ctor.scalar_u64(1, 8);
        IxonExpr::Prj(type_ref_idx, field_idx, Arc::new(val_obj.decode()))
      },
      5 => {
        let ref_idx = ctor.scalar_u64(0, 0);
        IxonExpr::Str(ref_idx)
      },
      6 => {
        let ref_idx = ctor.scalar_u64(0, 0);
        IxonExpr::Nat(ref_idx)
      },
      7 => {
        let f_obj = Self::new(ctor.get(0));
        let a_obj = Self::new(ctor.get(1));
        IxonExpr::App(Arc::new(f_obj.decode()), Arc::new(a_obj.decode()))
      },
      8 => {
        let ty_obj = Self::new(ctor.get(0));
        let body_obj = Self::new(ctor.get(1));
        IxonExpr::Lam(Arc::new(ty_obj.decode()), Arc::new(body_obj.decode()))
      },
      9 => {
        let ty_obj = Self::new(ctor.get(0));
        let body_obj = Self::new(ctor.get(1));
        IxonExpr::All(Arc::new(ty_obj.decode()), Arc::new(body_obj.decode()))
      },
      10 => {
        let ty_obj = Self::new(ctor.get(0));
        let val_obj = Self::new(ctor.get(1));
        let body_obj = Self::new(ctor.get(2));
        let non_dep = ctor.scalar_u8(3, 0) != 0;
        IxonExpr::Let(
          non_dep,
          Arc::new(ty_obj.decode()),
          Arc::new(val_obj.decode()),
          Arc::new(body_obj.decode()),
        )
      },
      11 => {
        let idx = ctor.scalar_u64(0, 0);
        IxonExpr::Share(idx)
      },
      _ => panic!("Invalid Ixon.Expr tag: {}", tag),
    }
  }

  /// Decode Array Ixon.Expr.
  pub fn decode_array(obj: LeanArray) -> Vec<Arc<IxonExpr>> {
    obj.map(|e| Arc::new(Self::new(e).decode()))
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Expr.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr(obj: LeanIxonExpr) -> LeanIxonExpr {
  let expr = obj.decode();
  LeanIxonExpr::build(&expr)
}
