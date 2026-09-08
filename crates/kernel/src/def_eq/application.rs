//! Positive-only application congruence with an explicit postorder worklist.
//!
//! Invariant: a Finish frame is reached ONLY after both child comparisons
//! succeeded in the frame's original context. Thus every published equality
//! follows from application congruence, not from a pending/visited-pair guess.
//! See Ix/Tc/Verify/DefEq/SpineArguments.lean (TrAppSpine.defEq_of_zip) for the
//! corresponding semantic rule. That theorem does not certify this Rust loop.
//!
//! No binders are opened here. All non-App pairs use ordinary conversion,
//! with recursive worklist entry disabled. A failed child abandons the probe;
//! it does NOT imply inequality of its applications (functions may ignore
//! arguments). The caller retains the original conversion path on every miss.

use super::*;
use crate::env::CtxAddr;
use crate::equiv::EqKey;

const APP_CONGRUENCE_FUEL: u64 = 4_096;
// Ordinary conversion is usually cheaper than speculative congruence. Use
// the worklist as a near-guard fallback, not a general structural fast path:
// a shallow trigger can spend much more work on arguments that reduction
// would erase. Reserve stack headroom for the ordinary leaf comparisons.
// This scheduling choice changes neither equality rules nor the depth cap.
const APP_CONGRUENCE_MIN_DEPTH: u32 = MAX_DEF_EQ_DEPTH - 512;

/// Compute these in the original context, before calling any leaf reducer.
/// Only positive entries are published, so FULL may also consume cheap-mode
/// successes, just as in is_def_eq. Negative results are never published here.
struct CompletedAppKeys {
  cache: (Addr, Addr, CtxAddr),
  left: EqKey,
  right: EqKey,
  cheap: bool,
}

enum Task<M: KernelMode> {
  Compare(KExpr<M>, KExpr<M>),
  Finish(CompletedAppKeys),
}

impl<M: KernelMode> TypeChecker<'_, M> {
  #[inline]
  pub(super) fn try_app_congruence(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if self.def_eq_depth < APP_CONGRUENCE_MIN_DEPTH {
      return Ok(false);
    }
    self.app_congruence_probe(a, b)
  }

  #[cold]
  #[inline(never)]
  fn app_congruence_probe(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if self.in_app_congruence
      || !matches!((a.data(), b.data()), (ExprData::App(..), ExprData::App(..)))
    {
      return Ok(false);
    }
    // Bound failed speculation, including leaf reductions, without changing
    // the constant's global allowance. Pending frames consume O(local_fuel)
    // space: each expansion is ticked before pushing at most three tasks.
    let saved_fuel = self.rec_fuel;
    let local_fuel = saved_fuel.min(APP_CONGRUENCE_FUEL);
    self.rec_fuel = local_fuel;
    self.in_app_congruence = true;
    let result = self.app_congruence_worklist(a, b);
    self.in_app_congruence = false;
    let consumed = local_fuel.saturating_sub(self.rec_fuel);
    self.rec_fuel = saved_fuel.saturating_sub(consumed);
    match result {
      Err(TcError::MaxRecDepth | TcError::MaxRecFuel) => Ok(false),
      other => other,
    }
  }

  fn app_congruence_worklist(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let mut work = vec![Task::Compare(a.clone(), b.clone())];
    while let Some(task) = work.pop() {
      let (a, b) = match task {
        Task::Finish(keys) => {
          // Both children completed. No pending parent can take this path
          // after a miss/error, because those return from the entire loop.
          self.env.def_eq_cache.insert(keys.cache, true);
          if keys.cheap {
            self.env.def_eq_cheap_cache.insert(keys.cache, true);
          }
          self.equiv_manager.add_equiv(keys.left, keys.right);
          continue;
        },
        Task::Compare(a, b) => (a, b),
      };
      if a.ptr_eq(&b) || a.hash_key() == b.hash_key() {
        continue;
      }
      let (ExprData::App(af, aa, _), ExprData::App(bf, ba, _)) =
        (a.data(), b.data())
      else {
        if !self.is_def_eq(&a, &b)? {
          return Ok(false);
        }
        continue;
      };

      crate::profile::bump_def_eq();
      let lbr = a.lbr().max(b.lbr());
      let ctx = self.def_eq_ctx_key(&a, &b);
      let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
      let keys = CompletedAppKeys {
        cache: (lo, hi, ctx),
        left: EqKey::new(a.hash_key(), ctx, lbr, a.lbr()),
        right: EqKey::new(b.hash_key(), ctx, lbr, b.lbr()),
        cheap: self.cheap_recursion_depth > 0,
      };
      // Completed equality is enough to skip a shared DAG branch. In-flight
      // frames are deliberately absent from both caches and the union-find.
      if self.equiv_manager.is_equiv(&keys.left, &keys.right)
        || self.env.def_eq_cache.get(&keys.cache) == Some(&true)
        || (keys.cheap
          && self.env.def_eq_cheap_cache.get(&keys.cache) == Some(&true))
      {
        self.env.perf.record_def_eq_hit();
        continue;
      }
      // A cached inequality makes this congruence attempt unproductive.
      // Abandon the probe, NOT its enclosing application comparison: a
      // surrounding function can still ignore this unequal child.
      if self.env.def_eq_cache.get(&keys.cache) == Some(&false)
        || (keys.cheap
          && self.env.def_eq_cheap_cache.get(&keys.cache) == Some(&false))
      {
        self.env.perf.record_def_eq_hit();
        return Ok(false);
      }
      self.env.perf.record_def_eq_miss();
      self.tick()?;
      // LIFO order: function first, then argument, then completion. Each
      // argument is checked after its function prefix, preserving dependent
      // application order. The caller-held roots keep descendants alive.
      work.push(Task::Finish(keys));
      work.push(Task::Compare(aa.clone(), ba.clone()));
      work.push(Task::Compare(af.clone(), bf.clone()));
    }
    Ok(true)
  }
}

#[cfg(test)]
mod tests;
