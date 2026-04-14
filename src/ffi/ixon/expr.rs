//! Ixon.Expr build/decode/roundtrip FFI.

use std::sync::Arc;

use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::lean::LeanIxonExpr;
use lean_ffi::object::{LeanArray, LeanBorrowed, LeanCtor, LeanOwned, LeanRef};

use lean_ffi::object::scalar_base;

/// Decode Array UInt64 from Lean.
fn decode_u64_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<u64> {
  obj
    .iter()
    .map(|elem| {
      if elem.is_scalar() {
        elem.unbox_usize() as u64
      } else {
        let ctor = elem.as_ctor();
        ctor.get_u64(scalar_base(&ctor, 0))
      }
    })
    .collect()
}

impl LeanIxonExpr<LeanOwned> {
  /// Build Ixon.Expr (12 constructors).
  pub fn build(expr: &IxonExpr) -> Self {
    let obj = match expr {
      IxonExpr::Sort(idx) => {
        let ctor = LeanCtor::alloc(0, 0, 8);
        ctor.set_u64(scalar_base(&ctor, 0), *idx);
        ctor.into()
      },
      IxonExpr::Var(idx) => {
        let ctor = LeanCtor::alloc(1, 0, 8);
        ctor.set_u64(scalar_base(&ctor, 0), *idx);
        ctor.into()
      },
      IxonExpr::Ref(ref_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = LeanCtor::alloc(0, 0, 8);
          uint64_obj.set_u64(scalar_base(&uint64_obj, 0), *idx);
          arr.set(i, uint64_obj);
        }
        let ctor = LeanCtor::alloc(2, 1, 8);
        ctor.set(0, arr);
        ctor.set_u64(scalar_base(&ctor, 0), *ref_idx);
        ctor.into()
      },
      IxonExpr::Rec(rec_idx, univ_idxs) => {
        let arr = LeanArray::alloc(univ_idxs.len());
        for (i, idx) in univ_idxs.iter().enumerate() {
          let uint64_obj = LeanCtor::alloc(0, 0, 8);
          uint64_obj.set_u64(scalar_base(&uint64_obj, 0), *idx);
          arr.set(i, uint64_obj);
        }
        let ctor = LeanCtor::alloc(3, 1, 8);
        ctor.set(0, arr);
        ctor.set_u64(scalar_base(&ctor, 0), *rec_idx);
        ctor.into()
      },
      IxonExpr::Prj(type_ref_idx, field_idx, val) => {
        let val_obj = Self::build(val);
        let ctor = LeanCtor::alloc(4, 1, 16);
        ctor.set(0, val_obj);
        let s = scalar_base(&ctor, 0);
        ctor.set_u64(s, *type_ref_idx);
        ctor.set_u64(s + 8, *field_idx);
        ctor.into()
      },
      IxonExpr::Str(ref_idx) => {
        let ctor = LeanCtor::alloc(5, 0, 8);
        ctor.set_u64(scalar_base(&ctor, 0), *ref_idx);
        ctor.into()
      },
      IxonExpr::Nat(ref_idx) => {
        let ctor = LeanCtor::alloc(6, 0, 8);
        ctor.set_u64(scalar_base(&ctor, 0), *ref_idx);
        ctor.into()
      },
      IxonExpr::App(fun, arg) => {
        let fun_obj = Self::build(fun);
        let arg_obj = Self::build(arg);
        let ctor = LeanCtor::alloc(7, 2, 0);
        ctor.set(0, fun_obj);
        ctor.set(1, arg_obj);
        ctor.into()
      },
      IxonExpr::Lam(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(8, 2, 0);
        ctor.set(0, ty_obj);
        ctor.set(1, body_obj);
        ctor.into()
      },
      IxonExpr::All(ty, body) => {
        let ty_obj = Self::build(ty);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(9, 2, 0);
        ctor.set(0, ty_obj);
        ctor.set(1, body_obj);
        ctor.into()
      },
      IxonExpr::Let(non_dep, ty, val, body) => {
        let ty_obj = Self::build(ty);
        let val_obj = Self::build(val);
        let body_obj = Self::build(body);
        let ctor = LeanCtor::alloc(10, 3, 1);
        ctor.set(0, ty_obj);
        ctor.set(1, val_obj);
        ctor.set(2, body_obj);
        ctor.set_bool(scalar_base(&ctor, 0), *non_dep);
        ctor.into()
      },
      IxonExpr::Share(idx) => {
        let ctor = LeanCtor::alloc(11, 0, 8);
        ctor.set_u64(scalar_base(&ctor, 0), *idx);
        ctor.into()
      },
    };
    Self::new(obj)
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
        let idx = ctor.get_u64(scalar_base(&ctor, 0));
        IxonExpr::Sort(idx)
      },
      1 => {
        let idx = ctor.get_u64(scalar_base(&ctor, 0));
        IxonExpr::Var(idx)
      },
      2 => {
        let ref_idx = ctor.get_u64(scalar_base(&ctor, 0));
        let univ_idxs = decode_u64_array(ctor.get(0).as_array());
        IxonExpr::Ref(ref_idx, univ_idxs)
      },
      3 => {
        let rec_idx = ctor.get_u64(scalar_base(&ctor, 0));
        let univ_idxs = decode_u64_array(ctor.get(0).as_array());
        IxonExpr::Rec(rec_idx, univ_idxs)
      },
      4 => {
        let s = scalar_base(&ctor, 0);
        let type_ref_idx = ctor.get_u64(s);
        let field_idx = ctor.get_u64(s + 8);
        IxonExpr::Prj(
          type_ref_idx,
          field_idx,
          Arc::new(LeanIxonExpr(ctor.get(0)).decode()),
        )
      },
      5 => {
        let ref_idx = ctor.get_u64(scalar_base(&ctor, 0));
        IxonExpr::Str(ref_idx)
      },
      6 => {
        let ref_idx = ctor.get_u64(scalar_base(&ctor, 0));
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
        let non_dep = ctor.get_bool(scalar_base(&ctor, 0));
        IxonExpr::Let(
          non_dep,
          Arc::new(LeanIxonExpr(ctor.get(0)).decode()),
          Arc::new(LeanIxonExpr(ctor.get(1)).decode()),
          Arc::new(LeanIxonExpr(ctor.get(2)).decode()),
        )
      },
      11 => {
        let idx = ctor.get_u64(scalar_base(&ctor, 0));
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
