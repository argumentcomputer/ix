//! Frozen pre-memoization interner for differential tests and benchmarks.
//! Keep the traversal, rebuilding, and first-insert-wins behavior unchanged.

use super::{InternTable, expr_key, univ_key};
use crate::{expr::KExpr, level::KUniv, mode::KernelMode};

impl<M: KernelMode> InternTable<M> {
  /// Intern a universe: returns the canonical value for its structural
  /// identity, recursively canonicalizing children as needed so the
  /// shallow key is meaningful.
  pub(super) fn intern_univ_reference(&mut self, u: KUniv<M>) -> KUniv<M> {
    use crate::level::UnivData;
    crate::profile::bump_intern_nodes();
    if self.canon_univs.contains(u.addr()) {
      return u;
    }
    // Canonicalize children first; rebuild only if any child changed.
    let u = match u.data() {
      UnivData::Succ(inner, _) => {
        let ci = self.intern_univ_reference(inner.clone());
        if ci.ptr_eq(inner) {
          u
        } else {
          KUniv::new(UnivData::Succ(ci, crate::expr::fresh_uid()))
        }
      },
      UnivData::Max(a, b, _) => {
        let ca = self.intern_univ_reference(a.clone());
        let cb = self.intern_univ_reference(b.clone());
        if ca.ptr_eq(a) && cb.ptr_eq(b) {
          u
        } else {
          KUniv::new(UnivData::Max(ca, cb, crate::expr::fresh_uid()))
        }
      },
      UnivData::IMax(a, b, _) => {
        let ca = self.intern_univ_reference(a.clone());
        let cb = self.intern_univ_reference(b.clone());
        if ca.ptr_eq(a) && cb.ptr_eq(b) {
          u
        } else {
          KUniv::new(UnivData::IMax(ca, cb, crate::expr::fresh_uid()))
        }
      },
      UnivData::Zero(_) | UnivData::Param(..) => u,
    };
    let key = univ_key(&u);
    if let Some(existing) = self.univs.get(&key) {
      return existing.clone();
    }
    self.canon_univs.insert(*u.addr());
    self.univs.insert(key, u.clone());
    u
  }

  /// Intern an expression: returns the canonical value for its structural
  /// identity. Children are canonicalized recursively when needed (a node
  /// built outside the table has non-canonical children whose uids would
  /// make the shallow key meaningless), preserving the historical
  /// content-hash interning semantics.
  pub(super) fn intern_expr_reference(&mut self, e: KExpr<M>) -> KExpr<M> {
    use crate::expr::ExprData;
    crate::profile::bump_intern_nodes();
    if self.canon_exprs.contains(e.addr()) {
      return e;
    }
    let e = match e.data() {
      ExprData::Sort(un, _) => {
        let cu = self.intern_univ_reference(un.clone());
        if cu.ptr_eq(un) {
          e
        } else {
          // Child canonicalization only — same semantic level, same
          // occurrence: the spelling decoration rides along.
          KExpr::sort_full(cu, e.mdata().clone(), e.univ_decor().clone())
        }
      },
      ExprData::Const(id, us, _) => {
        let cus: Box<[KUniv<M>]> =
          us.iter().map(|un| self.intern_univ_reference(un.clone())).collect();
        if cus.iter().zip(us.iter()).all(|(a, b)| a.ptr_eq(b)) {
          e
        } else {
          KExpr::cnst_full(
            id.clone(),
            cus,
            e.mdata().clone(),
            e.univ_decor().clone(),
          )
        }
      },
      ExprData::App(f, a, _) => {
        let cf = self.intern_expr_reference(f.clone());
        let ca = self.intern_expr_reference(a.clone());
        if cf.ptr_eq(f) && ca.ptr_eq(a) {
          e
        } else {
          KExpr::app_mdata(cf, ca, e.mdata().clone())
        }
      },
      ExprData::Lam(n, bi, t, b, _) => {
        let ct = self.intern_expr_reference(t.clone());
        let cb = self.intern_expr_reference(b.clone());
        if ct.ptr_eq(t) && cb.ptr_eq(b) {
          e
        } else {
          KExpr::lam_mdata(n.clone(), bi.clone(), ct, cb, e.mdata().clone())
        }
      },
      ExprData::All(n, bi, t, b, _) => {
        let ct = self.intern_expr_reference(t.clone());
        let cb = self.intern_expr_reference(b.clone());
        if ct.ptr_eq(t) && cb.ptr_eq(b) {
          e
        } else {
          KExpr::all_mdata(n.clone(), bi.clone(), ct, cb, e.mdata().clone())
        }
      },
      ExprData::Let(n, t, v, b, nd, _) => {
        let ct = self.intern_expr_reference(t.clone());
        let cv = self.intern_expr_reference(v.clone());
        let cb = self.intern_expr_reference(b.clone());
        if ct.ptr_eq(t) && cv.ptr_eq(v) && cb.ptr_eq(b) {
          e
        } else {
          KExpr::let_mdata(n.clone(), ct, cv, cb, *nd, e.mdata().clone())
        }
      },
      ExprData::Prj(id, f, v, _) => {
        let cv = self.intern_expr_reference(v.clone());
        if cv.ptr_eq(v) {
          e
        } else {
          KExpr::prj_mdata(id.clone(), *f, cv, e.mdata().clone())
        }
      },
      ExprData::Var(..)
      | ExprData::FVar(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => e,
    };
    let key = expr_key(&e);
    if let Some(existing) = self.exprs.get(&key) {
      // The shallow key (exact structural Eq over variant tag + child
      // uids + payload — never a truncated or content-hashed key) plus
      // canonical children make this hit structurally exact. Checked in
      // debug builds; a violation here would be an interning bug, not
      // an input an adversary can craft (uids are assigned, not hashed).
      debug_assert!(existing == &e, "intern hit is not structurally equal");
      return existing.clone();
    }
    self.canon_exprs.insert(*e.addr());
    self.exprs.insert(key, e.clone());
    e
  }
}
