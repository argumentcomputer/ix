//! Positive-only batched lambda/forall congruence.
//!
//! Domains are compared under the already-accepted prefix, before adding
//! the SAME fresh local to both sides. The terminal bodies are opened once.
//! Each accepted binder therefore follows the existing single-binder rule.
//! See Ix/Tc/Verify/DefEq/Structural.lean (quickBinder_wf) and the lamDF /
//! forallEDF rules in lean4lean. Those proofs do not certify this Rust loop.
//!
//! This is not a complete conversion procedure for binder terms: skipping
//! intermediate conversion can miss reduction/proof-irrelevance/cache wins.
//! A false or exhausted probe falls back to the original single-binder path,
//! with batching disabled throughout that fallback. No pending/suffix pair
//! is published equal, and no failed probe is published as an inequality.

use super::*;
use ix_common::env::{BinderInfo, Name};

const BINDER_BATCH_MIN_LENGTH: usize = 4;
const BINDER_BATCH_FUEL: u64 = 4_096;

struct BinderPair<'a, M: KernelMode> {
  name: &'a M::MField<Name>,
  bi: &'a M::MField<BinderInfo>,
  left_ty: &'a KExpr<M>,
  right_ty: &'a KExpr<M>,
  left_body: &'a KExpr<M>,
  right_body: &'a KExpr<M>,
}

fn binder_pair<'a, M: KernelMode>(
  a: &'a KExpr<M>,
  b: &'a KExpr<M>,
) -> Option<BinderPair<'a, M>> {
  match (a.data(), b.data()) {
    (ExprData::Lam(name, bi, at, ab, _), ExprData::Lam(_, _, bt, bb, _))
    | (ExprData::All(name, bi, at, ab, _), ExprData::All(_, _, bt, bb, _)) => {
      Some(BinderPair {
        name,
        bi,
        left_ty: at,
        right_ty: bt,
        left_body: ab,
        right_body: bb,
      })
    },
    _ => None,
  }
}

fn has_batch_prefix<'a, M: KernelMode>(
  mut a: &'a KExpr<M>,
  mut b: &'a KExpr<M>,
) -> bool {
  for _ in 0..BINDER_BATCH_MIN_LENGTH {
    let Some(pair) = binder_pair(a, b) else { return false };
    a = pair.left_body;
    b = pair.right_body;
  }
  true
}

impl<M: KernelMode> TypeChecker<'_, M> {
  pub(super) fn def_eq_binders(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if self.in_binder_batch || !has_batch_prefix(a, b) {
      return self.def_eq_one_binder(a, b);
    }
    self.in_binder_batch = true;
    let saved_fuel = self.rec_fuel;
    let local_fuel = saved_fuel.min(BINDER_BATCH_FUEL);
    self.rec_fuel = local_fuel;
    let result = self.with_lctx_scope(|tc| tc.def_eq_binder_telescope(a, b));
    let consumed = local_fuel.saturating_sub(self.rec_fuel);
    self.rec_fuel = saved_fuel.saturating_sub(consumed);
    let result = match result {
      Ok(false) | Err(TcError::MaxRecDepth | TcError::MaxRecFuel) => {
        // Do not start another failed probe at every recursive suffix.
        self.def_eq_one_binder(a, b)
      },
      other => other,
    };
    self.in_binder_batch = false;
    result
  }

  /// Original binder comparison, also the reference path for differential
  /// tests. Scope cleanup occurs on success, false, and every returned error.
  fn def_eq_one_binder(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let Some(pair) = binder_pair(a, b) else { return Ok(false) };
    if !self.is_def_eq(pair.left_ty, pair.right_ty)? {
      return Ok(false);
    }
    self.with_lctx_scope(|tc| {
      let id = tc.fresh_fvar_id();
      let fv = tc.intern(KExpr::fvar(id, pair.name.clone()));
      tc.lctx.push(
        id,
        LocalDecl::CDecl {
          name: pair.name.clone(),
          bi: pair.bi.clone(),
          ty: pair.left_ty.clone(),
        },
      );
      let left = instantiate_rev(
        &mut tc.env.intern,
        pair.left_body,
        std::slice::from_ref(&fv),
      );
      let right = instantiate_rev(&mut tc.env.intern, pair.right_body, &[fv]);
      tc.is_def_eq(&left, &right)
    })
  }

  fn def_eq_binder_telescope<'a>(
    &mut self,
    mut a: &'a KExpr<M>,
    mut b: &'a KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let mut fvars = Vec::new();
    loop {
      // Opening the same raw expression under the same prefix yields the
      // same expression. This is structural identity, not an in-flight pair.
      if a.ptr_eq(b) || a.hash_key() == b.hash_key() {
        return Ok(true);
      }
      // Closed suffixes are unchanged by opening: honor existing conversion
      // caches without materializing suffixes merely to look them up.
      if !fvars.is_empty()
        && a.lbr() == 0
        && b.lbr() == 0
        && self.has_closed_binder_result(a, b)
      {
        return self.is_def_eq(a, b);
      }
      let Some(pair) = binder_pair(a, b) else { break };
      if !fvars.is_empty() {
        // Corresponds to entering another nontrivial binder comparison.
        // Keeps the iterative walk fuel-bounded without growing the stack.
        self.tick()?;
        crate::profile::bump_def_eq();
      }
      // Each substitution has its own memo: distinct prefixes must never
      // share a semantic substitution result just to reuse scratch storage.
      let left_ty = instantiate_rev(&mut self.env.intern, pair.left_ty, &fvars);
      let right_ty =
        instantiate_rev(&mut self.env.intern, pair.right_ty, &fvars);
      if !self.is_def_eq(&left_ty, &right_ty)? {
        return Ok(false);
      }
      let id = self.fresh_fvar_id();
      let fv = self.intern(KExpr::fvar(id, pair.name.clone()));
      self.lctx.push(
        id,
        LocalDecl::CDecl {
          name: pair.name.clone(),
          bi: pair.bi.clone(),
          ty: left_ty,
        },
      );
      fvars.push(fv);
      a = pair.left_body;
      b = pair.right_body;
    }
    let left = instantiate_rev(&mut self.env.intern, a, &fvars);
    let right = instantiate_rev(&mut self.env.intern, b, &fvars);
    self.is_def_eq(&left, &right)
  }

  fn has_closed_binder_result(&mut self, a: &KExpr<M>, b: &KExpr<M>) -> bool {
    let ctx = self.def_eq_ctx_key(a, b);
    let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
    let key = (lo, hi, ctx);
    self.env.def_eq_cache.contains_key(&key)
      || (self.cheap_recursion_depth > 0
        && self.env.def_eq_cheap_cache.contains_key(&key))
      || self.equiv_manager.is_equiv(
        &crate::equiv::EqKey::new(a.hash_key(), ctx, 0, 0),
        &crate::equiv::EqKey::new(b.hash_key(), ctx, 0, 0),
      )
  }
}

#[cfg(test)]
mod tests;
