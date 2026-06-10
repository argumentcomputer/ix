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
  ///
  /// Iterative post-order construction: expression trees can nest
  /// arbitrarily deep (`.ixe`-derived data), and FFI entry points run on
  /// default-size stacks where structural recursion overflows — a hard
  /// process abort under `panic = "abort"`.
  pub fn build(expr: &IxonExpr) -> Self {
    enum Walk<'a> {
      Visit(&'a IxonExpr),
      Assemble(&'a IxonExpr),
    }
    let mut work: Vec<Walk<'_>> = vec![Walk::Visit(expr)];
    let mut out: Vec<LeanIxonExpr<LeanOwned>> = Vec::new();
    while let Some(w) = work.pop() {
      match w {
        Walk::Visit(e) => match e {
          // Leaves: assemble immediately.
          IxonExpr::Sort(idx) => {
            let ctor = LeanIxonExpr::alloc(0);
            ctor.set_num_64(0, *idx);
            out.push(ctor);
          },
          IxonExpr::Var(idx) => {
            let ctor = LeanIxonExpr::alloc(1);
            ctor.set_num_64(0, *idx);
            out.push(ctor);
          },
          IxonExpr::Ref(ref_idx, univ_idxs) => {
            let arr = LeanArray::alloc(univ_idxs.len());
            for (i, idx) in univ_idxs.iter().enumerate() {
              arr.set(i, LeanOwned::box_u64(*idx));
            }
            let ctor = LeanIxonExpr::alloc(2);
            ctor.set_obj(0, arr);
            ctor.set_num_64(0, *ref_idx);
            out.push(ctor);
          },
          IxonExpr::Rec(rec_idx, univ_idxs) => {
            let arr = LeanArray::alloc(univ_idxs.len());
            for (i, idx) in univ_idxs.iter().enumerate() {
              arr.set(i, LeanOwned::box_u64(*idx));
            }
            let ctor = LeanIxonExpr::alloc(3);
            ctor.set_obj(0, arr);
            ctor.set_num_64(0, *rec_idx);
            out.push(ctor);
          },
          IxonExpr::Str(ref_idx) => {
            let ctor = LeanIxonExpr::alloc(5);
            ctor.set_num_64(0, *ref_idx);
            out.push(ctor);
          },
          IxonExpr::Nat(ref_idx) => {
            let ctor = LeanIxonExpr::alloc(6);
            ctor.set_num_64(0, *ref_idx);
            out.push(ctor);
          },
          IxonExpr::Share(idx) => {
            let ctor = LeanIxonExpr::alloc(11);
            ctor.set_num_64(0, *idx);
            out.push(ctor);
          },
          // Interior nodes: assemble after children. Children are pushed
          // in reverse so they complete left-to-right; `Assemble` then
          // pops them right-to-left.
          IxonExpr::Prj(_, _, val) => {
            work.push(Walk::Assemble(e));
            work.push(Walk::Visit(val));
          },
          IxonExpr::App(fun, arg) => {
            work.push(Walk::Assemble(e));
            work.push(Walk::Visit(arg));
            work.push(Walk::Visit(fun));
          },
          IxonExpr::Lam(ty, body) | IxonExpr::All(ty, body) => {
            work.push(Walk::Assemble(e));
            work.push(Walk::Visit(body));
            work.push(Walk::Visit(ty));
          },
          IxonExpr::Let(_, ty, val, body) => {
            work.push(Walk::Assemble(e));
            work.push(Walk::Visit(body));
            work.push(Walk::Visit(val));
            work.push(Walk::Visit(ty));
          },
        },
        Walk::Assemble(e) => match e {
          IxonExpr::Prj(type_ref_idx, field_idx, _) => {
            let val_obj = out.pop().expect("Prj child");
            let ctor = LeanIxonExpr::alloc(4);
            ctor.set_obj(0, val_obj);
            ctor.set_num_64(0, *type_ref_idx);
            ctor.set_num_64(1, *field_idx);
            out.push(ctor);
          },
          IxonExpr::App(..) => {
            let arg_obj = out.pop().expect("App arg");
            let fun_obj = out.pop().expect("App fun");
            let ctor = LeanIxonExpr::alloc(7);
            ctor.set_obj(0, fun_obj);
            ctor.set_obj(1, arg_obj);
            out.push(ctor);
          },
          IxonExpr::Lam(..) | IxonExpr::All(..) => {
            let body_obj = out.pop().expect("binder body");
            let ty_obj = out.pop().expect("binder type");
            let tag = if matches!(e, IxonExpr::Lam(..)) { 8 } else { 9 };
            let ctor = LeanIxonExpr::alloc(tag);
            ctor.set_obj(0, ty_obj);
            ctor.set_obj(1, body_obj);
            out.push(ctor);
          },
          IxonExpr::Let(non_dep, ..) => {
            let body_obj = out.pop().expect("Let body");
            let val_obj = out.pop().expect("Let val");
            let ty_obj = out.pop().expect("Let type");
            let ctor = LeanIxonExpr::alloc(10);
            ctor.set_obj(0, ty_obj);
            ctor.set_obj(1, val_obj);
            ctor.set_obj(2, body_obj);
            ctor.set_num_8(0, u8::from(*non_dep));
            out.push(ctor);
          },
          _ => unreachable!("leaves are assembled at Visit"),
        },
      }
    }
    out.pop().expect("build: exactly one root")
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
