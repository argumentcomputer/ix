//! Batched opening of consecutive lambdas/foralls during inference.
//!
//! Walk the original telescope, opening each domain under its own prefix of
//! fresh locals, then instantiate the terminal body once. Substitution memos
//! remain call-local: different prefixes MUST NOT share logical entries.
//! The outer `infer` call still owns cache lookup/publication; domains and the
//! terminal body use ordinary, mode-separated cached inference. We omit
//! partially opened suffix entries rather than constructing them just to
//! cache them. An unchanged closed suffix can still use an existing result.

use super::*;

impl<M: KernelMode> TypeChecker<'_, M> {
  /// A suffix with no loose bvars is unaffected by the accumulated opening.
  /// Probe only that case: building other suffixes to probe their cache would
  /// reintroduce the repeated DAG traversals this optimization removes.
  fn has_closed_infer_result(&mut self, e: &KExpr<M>) -> bool {
    if e.lbr() != 0 {
      return false;
    }
    let key = self.infer_key(e);
    self.env.infer_cache.contains_key(&key)
      || (self.infer_only && self.env.infer_only_cache.contains_key(&key))
  }

  pub(super) fn infer_lambda_telescope(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.with_lctx_scope(|tc| {
      let mut fvars = Vec::new();
      let mut ids = Vec::new();
      let mut domains = Vec::new();
      let mut body = e;
      while let ExprData::Lam(name, bi, ty, rest, _) = body.data() {
        if !fvars.is_empty() && tc.has_closed_infer_result(body) {
          break;
        }
        // Check in dependency order, before introducing this binder. In
        // infer-only mode, preserve the existing skipped-domain validation.
        let domain = instantiate_rev(&mut tc.env.intern, ty, &fvars);
        if !tc.infer_only {
          let domain_ty = tc.infer(&domain)?;
          tc.ensure_sort(&domain_ty)?;
        }
        let id = tc.fresh_fvar_id();
        let fv = tc.intern(KExpr::fvar(id, name.clone()));
        tc.lctx.push(
          id,
          LocalDecl::CDecl {
            name: name.clone(),
            bi: bi.clone(),
            ty: domain.clone(),
          },
        );
        fvars.push(fv);
        ids.push(id);
        domains.push(domain);
        body = rest;
      }

      let opened = instantiate_rev(&mut tc.env.intern, body, &fvars);
      let body_ty = tc.infer(&opened)?;
      // In the recursive implementation only the innermost call can see a
      // head beta redex; every outer call sees the newly constructed All.
      let body_ty = cheap_beta_reduce(&mut tc.env.intern, &body_ty);
      let mut result = abstract_fvars(&mut tc.env.intern, &body_ty, &ids);
      for (i, domain) in domains.iter().enumerate().rev() {
        // Close a domain over ONLY its earlier binders. Do not reuse the
        // original raw domain: opening/closing canonicalizes variable names
        // and affected metadata just as the single-binder implementation does.
        let domain = abstract_fvars(&mut tc.env.intern, domain, &ids[..i]);
        // Inferred Pis deliberately use anonymous/default binder metadata,
        // matching the single-binder path and recursor synthesis exactly.
        result = tc.env.intern.intern_all(
          M::meta_field(ix_common::env::Name::anon()),
          M::meta_field(ix_common::env::BinderInfo::Default),
          &domain,
          &result,
        );
      }
      Ok(result)
    })
  }

  pub(super) fn infer_forall_telescope(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.with_lctx_scope(|tc| {
      let mut fvars = Vec::new();
      let mut levels = Vec::new();
      let mut body = e;
      while let ExprData::All(name, bi, ty, rest, _) = body.data() {
        if !fvars.is_empty() && tc.has_closed_infer_result(body) {
          break;
        }
        let domain = instantiate_rev(&mut tc.env.intern, ty, &fvars);
        // Foralls validate domain sorts even in infer-only mode.
        let domain_ty = tc.infer(&domain)?;
        levels.push(tc.ensure_sort(&domain_ty)?);
        let id = tc.fresh_fvar_id();
        let fv = tc.intern(KExpr::fvar(id, name.clone()));
        if crate::env_var("IX_FVAR_TRACE").is_ok() {
          log::info!(
            "[fvar All batch push] fv={id} ty.addr={:?} ty.lbr={} ctx_len_before_push={} batch_prefix={}",
            domain.addr(),
            domain.lbr(),
            tc.ctx.len(),
            fvars.len(),
          );
          log::info!("    ty data: {:?}", domain.data());
        }
        tc.lctx.push(
          id,
          LocalDecl::CDecl {
            name: name.clone(),
            bi: bi.clone(),
            ty: domain,
          },
        );
        fvars.push(fv);
        body = rest;
      }

      let opened = instantiate_rev(&mut tc.env.intern, body, &fvars);
      let mut result = tc.infer(&opened)?;
      for domain_level in levels.into_iter().rev() {
        let body_level = tc.ensure_sort(&result)?;
        // Preserve the right-associated imax and normalize each intermediate
        // sort as before. Prop codomains and symbolic universes need imax,
        // not a max over all the domains.
        result = tc.intern(KExpr::sort(KUniv::imax(domain_level, body_level)));
      }
      Ok(result)
    })
  }
}

#[cfg(test)]
mod tests;
