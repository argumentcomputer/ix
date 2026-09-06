//! Application inference with delayed telescope substitution.
//!
//! At each step, `ty` under `pending` denotes exactly the type obtained by
//! sequential App inference. Check the next instantiated domain, then peel
//! its raw Pi body. Materialize the residual type only at a non-Pi boundary
//! or at the end. Arguments live in the caller's context, NOT under the
//! peeled binders, so simultaneous substitution must lift them under nested
//! binders; `instantiate_rev`'s FVar-only shortcut is not appropriate here.

use smallvec::SmallVec;

use super::*;
use crate::subst::simul_subst;

impl<M: KernelMode> TypeChecker<'_, M> {
  pub(super) fn infer_app_spine(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    // Borrow original prefix nodes (no reconstruction just to probe a cache).
    // Stop at the nearest cached prefix in the caller's inference mode.
    let mut prefixes: SmallVec<[&KExpr<M>; 8]> = SmallVec::new();
    let mut args: SmallVec<[KExpr<M>; 8]> = SmallVec::new();
    let mut head = e;
    let cached = loop {
      let ExprData::App(f, a, _) = head.data() else { break None };
      if !args.is_empty() {
        let key = self.infer_key(head);
        if let Some(ty) = self.env.infer_cache.get(&key) {
          self.env.perf.record_infer_hit();
          break Some(ty.clone());
        }
        self.env.perf.record_infer_miss();
        if self.infer_only
          && let Some(ty) = self.env.infer_only_cache.get(&key)
        {
          self.env.perf.record_infer_only_hit();
          break Some(ty.clone());
        }
        if self.infer_only {
          self.env.perf.record_infer_only_miss();
          self.record_hot_miss("infer-only", head);
        } else {
          self.record_hot_miss("infer", head);
        }
      }
      prefixes.push(head);
      args.push(a.clone());
      head = f;
    };
    let mut ty = match cached {
      Some(ty) => ty,
      None => self.infer(head)?,
    };

    // args is innermost-de-Bruijn-first (reverse application order). At
    // position i, args[i+1..end] contains the already-consumed arguments
    // since the last materialization. Slicing avoids reversing/copying a
    // growing argument vector for every dependent domain.
    let mut end = args.len();
    for i in (0..args.len()).rev() {
      let ExprData::App(f, _, _) = prefixes[i].data() else {
        unreachable!("only application prefixes were collected")
      };
      let (dom, cod) = if let ExprData::All(_, _, dom, cod, _) = ty.data() {
        let dom =
          instantiate_pending(&mut self.env.intern, dom, &args[i + 1..end]);
        (dom, cod.clone())
      } else {
        // A reducible type/let or a substituted type variable hides the
        // next Pi. Flush in the ambient context BEFORE normalization.
        ty = instantiate_pending(&mut self.env.intern, &ty, &args[i + 1..end]);
        end = i + 1;
        let result = self.ensure_forall(&ty);
        if result.is_err()
          && *IX_INFER_APP_FORALL_DUMP
          && self.debug_label_matches_env()
        {
          log::info!(
            "[infer App batch] ensure_forall FAILED: f={f}, f_ty={ty}, a={}",
            args[i]
          );
        }
        result?
      };
      self.check_app_argument(f, &args[i], &dom)?;
      ty = cod;

      // Preserve cheap prefix results. Do not build a dependent Pi suffix
      // solely to cache it: that would reintroduce the quadratic traversal.
      // Existing dependent-prefix entries were already honored above.
      if i > 0 && ty.lbr() == 0 {
        let key = self.infer_key(prefixes[i]);
        if self.infer_only {
          self.env.infer_only_cache.insert(key, ty.clone());
        } else {
          self.env.infer_cache.insert(key, ty.clone());
        }
        end = i;
      }
    }
    Ok(instantiate_pending(&mut self.env.intern, &ty, &args[..end]))
  }

  /// Shared by the single-App and batched paths. Validation is never elided
  /// by batching; infer-only continues to have a separate cache contract.
  pub(super) fn check_app_argument(
    &mut self,
    f: &KExpr<M>,
    a: &KExpr<M>,
    dom: &KExpr<M>,
  ) -> Result<(), TcError<M>> {
    if self.infer_only {
      return Ok(());
    }
    let a_ty = self.infer(a)?;
    let saved_eager = self.eager_reduce;
    self.eager_reduce |= self.is_eager_reduce(a);
    let eq = self.is_def_eq(&a_ty, dom);
    // Restore even on errors and preserve an enclosing eager scope.
    self.eager_reduce = saved_eager;
    if eq? {
      return Ok(());
    }
    if *IX_APP_DIFF && self.debug_label_matches_env() {
      let a_whnf = self.whnf(&a_ty);
      let d_whnf = self.whnf(dom);
      let depth = crate::env_var("IX_APP_DIFF_DEPTH")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(2);
      eprintln!(
        "[app diff] AppTypeMismatch at depth={} in {}",
        self.ctx.len(),
        self.debug_label.as_deref().unwrap_or("<unknown>")
      );
      eprintln!("  f:          {}", compact_expr(f));
      eprintln!("  a:          {}", compact_expr(a));
      eprintln!("  a_ty:       {}", compact_expr_deep(&a_ty, depth));
      eprintln!("  dom:        {}", compact_expr_deep(dom, depth));
      eprintln!("  a_ty data:  {:?}", a_ty.data());
      eprintln!("  dom data:   {:?}", dom.data());
      match &a_whnf {
        Ok(w) => eprintln!("  a_ty whnf:  {}", compact_expr_deep(w, depth)),
        Err(e) => eprintln!("  a_ty whnf:  ERR {e}"),
      }
      match &d_whnf {
        Ok(w) => eprintln!("  dom  whnf:  {}", compact_expr_deep(w, depth)),
        Err(e) => eprintln!("  dom  whnf:  ERR {e}"),
      }
    }
    Err(TcError::AppTypeMismatch {
      a_ty,
      dom: dom.clone(),
      depth: self.ctx.len(),
    })
  }
}

fn instantiate_pending<M: KernelMode>(
  intern: &mut crate::env::InternTable<M>,
  ty: &KExpr<M>,
  args: &[KExpr<M>],
) -> KExpr<M> {
  match args {
    [] => ty.clone(),
    [arg] => subst(intern, ty, arg, 0),
    _ => simul_subst(intern, ty, args, 0),
  }
}

#[cfg(test)]
mod tests;
