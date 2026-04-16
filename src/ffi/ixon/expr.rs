//! Ixon.Expr build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::lean::LeanIxonExpr;
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanOwned, LeanRef};

/// Decode Array UInt64 from Lean.
fn decode_u64_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<u64> {
  obj
    .iter()
    .map(|elem| {
      if elem.is_scalar() {
        elem.unbox_usize() as u64
      } else {
        elem.unbox_u64()
      }
    })
    .collect()
}

impl LeanIxonExpr<LeanOwned> {
  /// Build Ixon.Expr (12 constructors).
  pub fn build(expr: &IxonExpr) -> Self {
    match expr {
      IxonExpr::Sort(idx) => {
        let ctor = LeanIxonExpr::alloc(0);
        ctor.set_num_64(0, *idx);
        ctor
      },
      IxonExpr::Var(idx) => {
        let ctor = LeanIxonExpr::alloc(1);
        ctor.set_num_64(0, *idx);
        ctor
      },
      IxonExpr::Ref(ref_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          arr.set(i, LeanOwned::box_u64(*idx));
        }
        let ctor = LeanIxonExpr::alloc(2);
        ctor.set_obj(0, arr);
        ctor.set_num_64(0, *ref_idx);
        ctor
      },
      IxonExpr::Rec(rec_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          arr.set(i, LeanOwned::box_u64(*idx));
        }
        let ctor = LeanIxonExpr::alloc(3);
        ctor.set_obj(0, arr);
        ctor.set_num_64(0, *rec_idx);
        ctor
      },
      IxonExpr::Prj(type_ref_idx, field_idx, val) => {
        let val_obj = Self::build(val);
        let ctor = LeanIxonExpr::alloc(4);
        ctor.set_obj(0, val_obj);
        ctor.set_num_64(0, *type_ref_idx);
        ctor.set_num_64(1, *field_idx);
        ctor
      },
      IxonExpr::Str(ref_idx) => {
        let ctor = LeanIxonExpr::alloc(5);
        ctor.set_num_64(0, *ref_idx);
        ctor
      },
      IxonExpr::Nat(ref_idx) => {
        let ctor = LeanIxonExpr::alloc(6);
        ctor.set_num_64(0, *ref_idx);
        ctor
      },
      IxonExpr::App(fun, arg) => {
        let fun_obj = Self::build(fun);
        let arg_obj = Self::build(arg);
        let ctor = LeanIxonExpr::alloc(7);
        ctor.set_obj(0, fun_obj);
        ctor.set_obj(1, arg_obj);
        ctor
      },
      IxonExpr::Lam(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanIxonExpr::alloc(8);
        ctor.set_obj(0, ty_obj);
        ctor.set_obj(1, body_obj);
        ctor
      },
      IxonExpr::All(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanIxonExpr::alloc(9);
        ctor.set_obj(0, ty_obj);
        ctor.set_obj(1, body_obj);
        ctor
      },
      IxonExpr::Let(non_dep, ty, val, body) => {
        let ty_obj = Self::build(ty);
        let val_obj = Self::build(val);
        let body_obj = Self::build(body);
        let ctor = LeanIxonExpr::alloc(10);
        ctor.set_obj(0, ty_obj);
        ctor.set_obj(1, val_obj);
        ctor.set_obj(2, body_obj);
        ctor.set_num_8(0, *non_dep as u8);
        ctor
      },
      IxonExpr::Share(idx) => {
        let ctor = LeanIxonExpr::alloc(11);
        ctor.set_num_64(0, *idx);
        ctor
      },
    }
  }

  /// Build an Array of Ixon.Expr.
  pub fn build_array(exprs: &[Arc<IxonExpr>]) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(exprs.len());
    for (i, expr) in exprs.iter().enumerate() {
      arr.set(i, Self::build(expr));
    }
    arr
  }
}

impl<R: LeanRef> LeanIxonExpr<R> {
  /// Decode Ixon.Expr (12 constructors).
  pub fn decode(&self) -> IxonExpr {
    let ctor = self.as_ctor();
    let tag = ctor.tag();
    match tag {
      0 => {
        let idx = self.get_num_64(0);
        IxonExpr::Sort(idx)
      },
      1 => {
        let idx = self.get_num_64(0);
        IxonExpr::Var(idx)
      },
      2 => {
        let ref_idx = self.get_num_64(0);
        let univ_idxs = decode_u64_array(self.get_obj(0).as_array());
        IxonExpr::Ref(ref_idx, univ_idxs)
      },
      3 => {
        let rec_idx = self.get_num_64(0);
        let univ_idxs = decode_u64_array(self.get_obj(0).as_array());
        IxonExpr::Rec(rec_idx, univ_idxs)
      },
      4 => {
        let type_ref_idx = self.get_num_64(0);
        let field_idx = self.get_num_64(1);
        IxonExpr::Prj(
          type_ref_idx,
          field_idx,
          Arc::new(LeanIxonExpr(self.get_obj(0)).decode()),
        )
      },
      5 => {
        let ref_idx = self.get_num_64(0);
        IxonExpr::Str(ref_idx)
      },
      6 => {
        let ref_idx = self.get_num_64(0);
        IxonExpr::Nat(ref_idx)
      },
      7 => IxonExpr::App(
        Arc::new(LeanIxonExpr(ctor.get(0)).decode()),
        Arc::new(LeanIxonExpr(ctor.get(1)).decode()),
      ),
      8 => IxonExpr::Lam(
        Arc::new(LeanIxonExpr(ctor.get(0)).decode()),
        Arc::new(LeanIxonExpr(ctor.get(1)).decode()),
      ),
      9 => IxonExpr::All(
        Arc::new(LeanIxonExpr(ctor.get(0)).decode()),
        Arc::new(LeanIxonExpr(ctor.get(1)).decode()),
      ),
      10 => {
        let non_dep = self.get_num_8(0) != 0;
        IxonExpr::Let(
          non_dep,
          Arc::new(LeanIxonExpr(self.get_obj(0)).decode()),
          Arc::new(LeanIxonExpr(self.get_obj(1)).decode()),
          Arc::new(LeanIxonExpr(self.get_obj(2)).decode()),
        )
      },
      11 => {
        let idx = self.get_num_64(0);
        IxonExpr::Share(idx)
      },
      _ => panic!("Invalid Ixon.Expr tag: {}", tag),
    }
  }
}

impl LeanIxonExpr<LeanOwned> {
  /// Decode Array Ixon.Expr.
  pub fn decode_array<R: LeanRef>(obj: &LeanArray<R>) -> Vec<Arc<IxonExpr>> {
    obj.map(|e| Arc::new(LeanIxonExpr(e).decode()))
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Expr.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_expr(
  obj: LeanIxonExpr<LeanBorrowed<'_>>,
) -> LeanIxonExpr<LeanOwned> {
  let expr = obj.decode();
  LeanIxonExpr::build(&expr)
}
