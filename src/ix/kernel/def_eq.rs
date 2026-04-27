//! Definitional equality checking.
//!
//! Multi-tier strategy following lean4lean:
//! 1. Quick structural (same constructor, same children)
//! 2. WHNF without delta, quick structural
//! 3. Proof irrelevance (before delta)
//! 4. Iterative lazy delta with same-head-spine optimization
//! 5. Full WHNF, structural comparison, eta, struct eta

use std::sync::LazyLock;

use crate::ix::ixon::constant::DefKind;

use super::canonical_check::{KMutCtx, compare_kexpr};
use super::constant::KConst;
use super::env::Addr;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, univ_eq};
use super::mode::KernelMode;
use super::subst::lift;
use super::tc::{
  MAX_DEF_EQ_DEPTH, MAX_WHNF_FUEL, TypeChecker, collect_app_spine,
  empty_ctx_addr,
};

/// When set, trace every `is_def_eq` call where one side's head constant
/// starts with the prefix in `IX_DEF_EQ_TRACE` (e.g. `IX_DEF_EQ_TRACE=bmod`
/// to watch all `Int.bmod`-involving comparisons). Prints `[deq] a <?> b`
/// before entering `is_def_eq_inner`, then the boolean outcome. Useful for
/// pinning down which sub-expression of an App-spine is stuck.
static IX_DEF_EQ_TRACE: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_DEF_EQ_TRACE").ok());

/// Global perf counter: total `is_def_eq` entries across all checks.
/// When `IX_DEF_EQ_COUNT_LOG=1`, logs every 1M calls. Useful for
/// detecting checks that explode into millions of recursive
/// comparisons \u2014 a signal that some caching optimization is
/// mis-firing or some reduction is looping.
static IX_DEF_EQ_COUNT_LOG: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_DEF_EQ_COUNT_LOG").is_ok());

/// Dump the expression pair when `is_def_eq` hits its recursion/fuel guard.
/// The optional env var value is used as a substring filter over the two head
/// constants; an empty value dumps every guard hit.
static IX_DEF_EQ_MAX_DUMP: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_DEF_EQ_MAX_DUMP").ok());

static IX_ETA_TRACE: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_ETA_TRACE").ok());

static IX_PROJ_DELTA_TRACE: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_PROJ_DELTA_TRACE").ok());

static DEF_EQ_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

impl<M: KernelMode> TypeChecker<M> {
  /// Check definitional equality of two expressions.
  pub fn is_def_eq(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if *IX_DEF_EQ_COUNT_LOG {
      let n = DEF_EQ_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n.is_multiple_of(100_000) && n > 0 {
        eprintln!("[is_def_eq] count={n}");
      }
    }
    if a.ptr_eq(b) {
      return Ok(true);
    }
    if a.hash_key() == b.hash_key() {
      return Ok(true);
    }
    if compare_kexpr(a, b, &KMutCtx::default()).ordering
      == std::cmp::Ordering::Equal
    {
      return Ok(true);
    }

    // Diagnostic trace: emit a `[deq]` line when either side's head
    // constant name contains the configured substring. Keeps output
    // manageable — a naive unconditional trace blows out the log.
    let trace_active = if let Some(prefix) = IX_DEF_EQ_TRACE.as_ref() {
      let a_hit = head_const_name(a).is_some_and(|n| n.contains(prefix));
      let b_hit = head_const_name(b).is_some_and(|n| n.contains(prefix));
      if a_hit || b_hit {
        eprintln!(
          "[deq] depth={} a={}",
          self.def_eq_depth,
          compact_def_eq_expr(a)
        );
        eprintln!(
          "[deq] depth={} b={}",
          self.def_eq_depth,
          compact_def_eq_expr(b)
        );
        true
      } else {
        false
      }
    } else {
      false
    };

    // Context-aware EquivManager/cache: closed exprs (lbr==0) share across
    // contexts. Open exprs are isolated by ctx_id because proof irrelevance
    // can consult local types even when no let-bindings are present.
    //
    // Build `a_key` and `b_key` ONCE and reuse them throughout. The
    // `eq_ctx` Arc is cloned once into `a_key`; `b_key` receives the
    // remaining owned copy. `is_equiv` and `find_root_key` take by
    // reference (see `src/ix/kernel/equiv.rs`), so no additional Arc
    // clones are paid per method call. Any true result moves the originals
    // into `add_equiv` before returning.
    let eq_ctx = if a.lbr() == 0 && b.lbr() == 0 {
      empty_ctx_addr()
    } else {
      self.ctx_id.clone()
    };
    let a_key: crate::ix::kernel::equiv::EqKey = (a.hash_key(), eq_ctx.clone());
    let b_key: crate::ix::kernel::equiv::EqKey = (b.hash_key(), eq_ctx.clone());

    if self.equiv_manager.is_equiv(&a_key, &b_key) {
      return Ok(true);
    }

    let (lo, hi) = canonical_pair(a.hash_key(), b.hash_key());
    let cache_key = (lo, hi, eq_ctx.clone());
    let cheap_mode = self.cheap_recursion_depth > 0;
    if let Some(cached) = self.env.def_eq_cache.get(&cache_key).map(|v| *v) {
      if cheap_mode {
        self.env.def_eq_cheap_cache.insert(cache_key.clone(), cached);
      }
      if cached {
        self.equiv_manager.add_equiv(a_key, b_key);
      }
      self.env.perf.record_def_eq_hit();
      return Ok(cached);
    }
    if cheap_mode
      && let Some(cached) =
        self.env.def_eq_cheap_cache.get(&cache_key).map(|v| *v)
    {
      if cached {
        self.env.def_eq_cache.insert(cache_key.clone(), true);
        self.equiv_manager.add_equiv(a_key, b_key);
      }
      self.env.perf.record_def_eq_hit();
      return Ok(cached);
    }

    // Equiv-root second-chance: if (a,b) not cached, try (root(a), root(b)).
    if let (Some(a_root), Some(b_root)) = (
      self.equiv_manager.find_root_key(&a_key),
      self.equiv_manager.find_root_key(&b_key),
    ) && (a_root != a_key || b_root != b_key)
    {
      let (rlo, rhi) = canonical_pair(a_root.0, b_root.0);
      let root_cache_key = (rlo, rhi, eq_ctx.clone());
      let mut cached = self
        .env
        .def_eq_cache
        .get(&root_cache_key)
        .map(|v| (*v, false));
      if cached.is_none() && cheap_mode {
        cached = self
          .env
          .def_eq_cheap_cache
          .get(&root_cache_key)
          .map(|v| (*v, true));
      }
      if let Some((cached, from_cheap_cache)) = cached {
        if from_cheap_cache {
          self.env.def_eq_cheap_cache.insert(cache_key.clone(), cached);
          if cached {
            self.env.def_eq_cache.insert(cache_key.clone(), true);
          }
        } else {
          self.env.def_eq_cache.insert(cache_key.clone(), cached);
          if cheap_mode {
            self.env.def_eq_cheap_cache.insert(cache_key.clone(), cached);
          }
        }
        if cached {
          self.equiv_manager.add_equiv(a_key, b_key);
        }
        self.env.perf.record_def_eq_hit();
        return Ok(cached);
      }
    }
    // Both probes missed.
    self.env.perf.record_def_eq_miss();

    // Charge recursive fuel only after the O(1) exits above. Large proof
    // terms can perform hundreds of thousands of pointer/equiv/cache hits;
    // those should not consume the same budget as an actual comparison.
    self.tick()?;

    self.def_eq_depth += 1;
    if self.def_eq_depth > self.def_eq_peak {
      self.def_eq_peak = self.def_eq_depth;
    }
    if self.def_eq_depth > MAX_DEF_EQ_DEPTH {
      self.def_eq_depth -= 1;
      self.dump_def_eq_max("depth", a, b, None, None);
      return Err(TcError::MaxRecDepth);
    }

    let result = self.is_def_eq_inner(a, b);
    self.def_eq_depth -= 1;

    let ok = result?;
    if trace_active {
      eprintln!(
        "[deq] depth={} -> {} ({})",
        self.def_eq_depth,
        ok,
        if ok { "OK" } else { "FAIL" }
      );
    }
    if ok {
      // Move the up-front `a_key` / `b_key` directly into `add_equiv`.
      //
      // SOUNDNESS: cheap-mode `true` is monotone (cheap-equal implies
      // FULL-equal), so it may be recorded as a local equivalence. WHNF
      // caches deliberately do not consult these equivalence roots; they are
      // only a def-eq shortcut.
      self.equiv_manager.add_equiv(a_key, b_key);
    }
    // SOUNDNESS: cheap-mode WHNF can leave projections stuck where FULL
    // would reduce, causing `is_def_eq` to return `false`
    // for terms FULL would judge equal. Caching such a cheap-mode `false`
    // would let a later FULL-mode caller hit the poisoned key and
    // short-circuit before doing the actual comparison.
    //
    // Cheap-mode `true` is monotone-sound to cache: cheap WHNF leaves
    // terms less-reduced, so any pair found equal at the cheap level is
    // also equal at the FULL level (further reduction preserves equality).
    // Caching cheap `true` is also performance-critical — without it,
    // heavy proof terms recompute the same comparisons inside lazy delta
    // and blow past `MAX_DEF_EQ_DEPTH`.
    //
    // The depth counter is bumped by the def-eq WHNF helpers in `whnf.rs`.
    // Any `is_def_eq` call inside a cheap reduction observes `cheap_mode`
    // and records cheap `false` only in `def_eq_cheap_cache`.
    if cheap_mode {
      self.env.def_eq_cheap_cache.insert(cache_key.clone(), ok);
      if ok {
        self.env.def_eq_cache.insert(cache_key, true);
      }
    } else {
      self.env.def_eq_cache.insert(cache_key, ok);
    }
    Ok(ok)
  }

  fn is_def_eq_inner(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    // Tier 1: quick structural
    if self.quick_def_eq(a, b)? {
      return Ok(true);
    }

    // Tier 1b: Eager Bool reduction (lean4 type_checker.cpp:1066)
    // If one side is Bool.true and the other has no loose bound vars (or eagerReduce
    // is active), try full WHNF. Critical for Decidable/decide-based definitions.
    if self.is_bool_true(b) && (a.lbr() == 0 || self.eager_reduce) {
      let wa = self.whnf(a)?;
      if self.is_bool_true(&wa) {
        return Ok(true);
      }
    } else if self.is_bool_true(a) && (b.lbr() == 0 || self.eager_reduce) {
      let wb = self.whnf(b)?;
      if self.is_bool_true(&wb) {
        return Ok(true);
      }
    }

    // Tier 1c: String literal expansion (before any WHNF).
    // Expand string literals to String.ofList [Char.ofNat c₁, ...] form so
    // both sides can reduce in lockstep through lazy delta. Must happen before
    // WHNF to avoid committing the other side to a structural form that
    // diverges from the expansion.
    if matches!(a.data(), ExprData::Str(..))
      || matches!(b.data(), ExprData::Str(..))
    {
      if self.try_string_lit_expansion(a, b)? {
        return Ok(true);
      }
      if self.try_string_lit_expansion(b, a)? {
        return Ok(true);
      }
    }

    // Tier 1d: Lean-style structural WHNF for def-eq. This uses cheap
    // projections so `a.i =?= b.i` first has a chance to compare `a =?= b`
    // before unfolding definitions hidden behind each projection.
    let ca = self.whnf_core_for_def_eq(a)?;
    let cb = self.whnf_core_for_def_eq(b)?;
    if ca.ptr_eq(&cb) {
      return Ok(true);
    }
    if self.quick_def_eq(&ca, &cb)? {
      return Ok(true);
    }
    if self.try_def_eq_app(&ca, &cb)? {
      return Ok(true);
    }

    // Ix's no-delta layer also contains primitive/native reductions needed
    // by the existing kernel model. Keep cheap projection behavior here, but
    // do not expose this as a public WHNF mode.
    let mut wa = self.whnf_no_delta_for_def_eq(a)?;
    let mut wb = self.whnf_no_delta_for_def_eq(b)?;
    if wa.ptr_eq(&wb) {
      return Ok(true);
    }
    if self.quick_def_eq(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 3: proof irrelevance (before delta)
    if self.try_proof_irrel(&wa, &wb)? {
      return Ok(true);
    }

    // Congruence before lazy delta.  This keeps open primitive-wrapper terms
    // such as `Nat.sub (x + 1) y` from unfolding to their recursive model when
    // both sides already have the same head and definitionally equal args.
    if self.try_def_eq_app(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 4: iterative lazy delta (lean4lean lazyDeltaReduction)
    let mut fuel = MAX_WHNF_FUEL;
    loop {
      if fuel == 0 {
        self.dump_def_eq_max("fuel", a, b, Some(&wa), Some(&wb));
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      // M2: Nat offset reduction at top of loop (lean4lean isDefEqOffset)
      if let Some(result) = self.try_def_eq_offset(&wa, &wb)? {
        return Ok(result);
      }

      // Nat primitive reduction inside lazy delta (lean4lean:620-623)
      if let Some(wa2) = self.try_reduce_nat(&wa)? {
        return self.is_def_eq(&wa2, &wb);
      }
      if let Some(wb2) = self.try_reduce_nat(&wb)? {
        return self.is_def_eq(&wa, &wb2);
      }

      // Int primitive reduction inside lazy delta, parallel to Nat.
      // Without this, `Int.bmod (-1) (2^32) =? -1` compared under
      // `Eq.{1} Int _ _` would never converge: the Int.bmod side would
      // delta-unfold to a stuck `Decidable.rec`, while the `-1` side
      // reduces to `Int.negSucc 0` — `lazyDeltaReduction` would never
      // find a common head.
      if let Some(wa2) = self.try_reduce_int(&wa)? {
        return self.is_def_eq(&wa2, &wb);
      }
      if let Some(wb2) = self.try_reduce_int(&wb)? {
        return self.is_def_eq(&wa, &wb2);
      }

      // Native reduction inside lazy delta (lean4lean:625-628)
      if let Some(wa2) = self.try_reduce_native(&wa)? {
        return self.is_def_eq(&wa2, &wb);
      }
      if let Some(wb2) = self.try_reduce_native(&wb)? {
        return self.is_def_eq(&wa, &wb2);
      }

      let a_head = head_const_id(&wa);
      let b_head = head_const_id(&wb);
      let a_delta = a_head.as_ref().is_some_and(|h| self.is_delta(h));
      let b_delta = b_head.as_ref().is_some_and(|h| self.is_delta(h));

      if !a_delta && !b_delta {
        break;
      }

      // C6: Before unfolding a definition, try reducing projection apps
      // on the non-definition side (lean4lean tryUnfoldProjApp).
      if a_delta && !b_delta {
        if let Some(wb2) = self.try_unfold_proj_app(&wb)? {
          wb = wb2;
          continue;
        }
      } else if b_delta
        && !a_delta
        && let Some(wa2) = self.try_unfold_proj_app(&wa)?
      {
        wa = wa2;
        continue;
      }

      if a_delta && b_delta {
        // Both `a_delta` and `b_delta` already imply a present head, so the
        // `map_or` defaults are dead code in practice. We keep the
        // "missing-head ranks above all real ranks" semantic by mapping the
        // None case to `(u8::MAX, u32::MAX)` — preserving the old `u32::MAX`
        // sentinel under the new tuple-based comparator.
        let wa_w = a_head
          .as_ref()
          .map_or((u8::MAX, u32::MAX), |h| self.def_rank_id(h));
        let wb_w = b_head
          .as_ref()
          .map_or((u8::MAX, u32::MAX), |h| self.def_rank_id(h));

        if wa_w == wb_w {
          // H2: Same-head-spine optimization — only for Regular hints, same head,
          // and only cache failure when spine args are actually compared (lean4lean:589-596)
          if let (Some(ah), Some(bh)) = (&a_head, &b_head)
            && ah.addr == bh.addr
            && self.is_regular(ah)
          {
            let (lo, hi) = canonical_pair(wa.hash_key(), wb.hash_key());
            let failure_key = (lo, hi, self.ctx_id.clone());
            if !self.env.def_eq_failure.contains(&failure_key) {
              if let Some(result) = self.try_same_head_spine(&wa, &wb)? {
                return Ok(result);
              }
              // Spine comparison was attempted and failed — cache it
              self.env.def_eq_failure.insert(failure_key);
              self.env.perf.record_def_eq_failure_insert();
            } else {
              self.env.perf.record_def_eq_failure_hit();
            }
          }
          // H1: Equal height — unfold BOTH sides (lean4lean:596)
          let ua = self.delta_unfold_one(&wa)?;
          let ub = self.delta_unfold_one(&wb)?;
          match (ua, ub) {
            (Some(ua), Some(ub)) => {
              wa = self.whnf_no_delta_for_def_eq(&ua)?;
              wb = self.whnf_no_delta_for_def_eq(&ub)?;
            },
            (Some(ua), None) => {
              wa = self.whnf_no_delta_for_def_eq(&ua)?;
            },
            (None, Some(ub)) => {
              wb = self.whnf_no_delta_for_def_eq(&ub)?;
            },
            (None, None) => break,
          }
        } else if wa_w > wb_w {
          // a is heavier — unfold a first
          if let Some(ua) = self.delta_unfold_one(&wa)? {
            wa = self.whnf_no_delta_for_def_eq(&ua)?;
          } else {
            break;
          }
        } else {
          // b is heavier — unfold b first
          if let Some(ub) = self.delta_unfold_one(&wb)? {
            wb = self.whnf_no_delta_for_def_eq(&ub)?;
          } else {
            break;
          }
        }
      } else if a_delta {
        if let Some(ua) = self.delta_unfold_one(&wa)? {
          wa = self.whnf_no_delta_for_def_eq(&ua)?;
        } else {
          break;
        }
      } else if let Some(ub) = self.delta_unfold_one(&wb)? {
        wb = self.whnf_no_delta_for_def_eq(&ub)?;
      } else {
        break;
      }

      if wa.ptr_eq(&wb) {
        return Ok(true);
      }
      if self.quick_def_eq(&wa, &wb)? {
        return Ok(true);
      }
    }

    // Tier 4b: post-delta congruence checks (lean4lean isDefEqConst/Fvar/Proj)
    if self.try_structural_congruence(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 4c: second structural pass (lean4lean:683-686, lean4 type_checker.cpp:1109-1110).
    // Use full projection reduction after lazy-delta exhaustion.
    let wa = self.whnf_core(&wa)?;
    let wb = self.whnf_core(&wb)?;
    if wa.ptr_eq(&wb) {
      return Ok(true);
    }
    if self.quick_def_eq(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 4d: app spine comparison (lean4lean isDefEqApp, lean4 type_checker.cpp:1115)
    if self.try_def_eq_app(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 5: full WHNF, structural comparison
    let wa = self.whnf(&wa)?;
    let wb = self.whnf(&wb)?;
    if wa.ptr_eq(&wb) {
      return Ok(true);
    }
    if self.try_structural_congruence(&wa, &wb)? {
      return Ok(true);
    }

    self.is_def_eq_whnf(&wa, &wb)
  }

  /// Quick structural: same constructor, recursively same children (no WHNF).
  fn quick_def_eq(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    match (a.data(), b.data()) {
      (ExprData::Sort(u1, _), ExprData::Sort(u2, _)) => Ok(univ_eq(u1, u2)),
      (
        ExprData::Lam(_, _, ty1, body1, _),
        ExprData::Lam(_, _, ty2, body2, _),
      )
      | (
        ExprData::All(_, _, ty1, body1, _),
        ExprData::All(_, _, ty2, body2, _),
      ) => {
        if !self.is_def_eq(ty1, ty2)? {
          return Ok(false);
        }
        self.push_local(ty1.clone());
        let r = self.is_def_eq(body1, body2);
        self.pop_local();
        r
      },
      _ => Ok(false),
    }
  }

  /// Same-head constant: if both are `C us args`, compare spines without unfolding.
  fn try_same_head_spine(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<Option<bool>, TcError<M>> {
    let (a_head, a_args) = collect_app_spine(a);
    let (b_head, b_args) = collect_app_spine(b);
    let (a_id, a_us) = match a_head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(None),
    };
    let (b_id, b_us) = match b_head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(None),
    };
    if a_id.addr != b_id.addr || a_args.len() != b_args.len() {
      return Ok(None);
    }
    if a_us.len() != b_us.len()
      || !a_us.iter().zip(b_us.iter()).all(|(u, v)| univ_eq(u, v))
    {
      return Ok(None);
    }
    for (ai, bi) in a_args.iter().zip(b_args.iter()) {
      if !self.is_def_eq(ai, bi)? {
        return Ok(None);
      }
    }
    Ok(Some(true))
  }

  /// Full structural comparison after WHNF.
  fn is_def_eq_whnf(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    // First try purely structural comparison
    let structural = match (a.data(), b.data()) {
      (ExprData::Sort(u1, _), ExprData::Sort(u2, _)) => {
        return Ok(univ_eq(u1, u2));
      },
      (ExprData::Var(i, _, _), ExprData::Var(j, _, _)) if i == j => {
        return Ok(true);
      },
      (ExprData::Const(id1, us1, _), ExprData::Const(id2, us2, _)) => {
        if id1.addr == id2.addr
          && us1.len() == us2.len()
          && us1.iter().zip(us2.iter()).all(|(u, v)| univ_eq(u, v))
        {
          return Ok(true);
        }
        false
      },
      (ExprData::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
        if self.is_def_eq(f1, f2)? && self.is_def_eq(a1, a2)? {
          return Ok(true);
        }
        false
      },
      (
        ExprData::Lam(_, _, ty1, body1, _),
        ExprData::Lam(_, _, ty2, body2, _),
      )
      | (
        ExprData::All(_, _, ty1, body1, _),
        ExprData::All(_, _, ty2, body2, _),
      ) => {
        if self.is_def_eq(ty1, ty2)? {
          self.push_local(ty1.clone());
          let r = self.is_def_eq(body1, body2)?;
          self.pop_local();
          if r {
            return Ok(true);
          }
        }
        false
      },
      (
        ExprData::Let(_, ty1, v1, body1, _, _),
        ExprData::Let(_, ty2, v2, body2, _, _),
      ) => {
        // H3: Let should be zeta-reduced by whnf_core before reaching this point.
        // Use push_let (not push_local) so the let-bound value is available for
        // reduction in the body comparison, in case this code IS reached.
        if self.is_def_eq(ty1, ty2)? && self.is_def_eq(v1, v2)? {
          self.push_let(ty1.clone(), v1.clone());
          let r = self.is_def_eq(body1, body2)?;
          self.pop_local();
          if r {
            return Ok(true);
          }
        }
        false
      },
      (ExprData::Nat(v1, _, _), ExprData::Nat(v2, _, _)) => {
        return Ok(v1 == v2);
      },
      (ExprData::Str(v1, _, _), ExprData::Str(v2, _, _)) => {
        return Ok(v1 == v2);
      },
      _ => false,
    };

    if structural {
      return Ok(true);
    }

    // Nat literal ↔ constructor: 0 ≡ Nat.zero, succ(n) ≡ n+1
    if self.is_nat_like(a) && self.is_nat_like(b) {
      return self.is_def_eq_nat(a, b);
    }

    // Eta expansion: try both directions
    if matches!(a.data(), ExprData::Lam(..))
      || matches!(b.data(), ExprData::Lam(..))
    {
      if self.try_eta_expansion(a, b)? {
        return Ok(true);
      }
      if self.try_eta_expansion(b, a)? {
        return Ok(true);
      }
    }

    // String literal expansion
    if matches!(a.data(), ExprData::Str(..))
      || matches!(b.data(), ExprData::Str(..))
    {
      if self.try_string_lit_expansion(a, b)? {
        return Ok(true);
      }
      if self.try_string_lit_expansion(b, a)? {
        return Ok(true);
      }
    }

    // Struct eta + unit-like + proof irrelevance fallback
    if self.try_eta_struct(a, b)? {
      return Ok(true);
    }
    if self.try_eta_struct(b, a)? {
      return Ok(true);
    }
    if self.try_def_eq_unit(a, b)? {
      return Ok(true);
    }
    self.try_proof_irrel(a, b)
  }

  /// Proof irrelevance: if both are proofs of propositions (types in Prop),
  /// they're def-eq. We check type(type(a)) = Sort(0), meaning type(a) : Prop.
  fn try_proof_irrel(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let a_ty = match self.with_infer_only(|tc| tc.infer(a)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    // Check if a_ty lives in Prop: infer(a_ty) should be Sort(0)
    let a_ty_ty = match self.with_infer_only(|tc| tc.infer(&a_ty)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let a_ty_sort = match self.whnf(&a_ty_ty) {
      Ok(s) => s,
      Err(_) => return Ok(false),
    };
    match a_ty_sort.data() {
      ExprData::Sort(u, _) if u.is_zero() => {
        let b_ty = match self.with_infer_only(|tc| tc.infer(b)) {
          Ok(ty) => ty,
          Err(_) => return Ok(false),
        };
        self.is_def_eq(&a_ty, &b_ty)
      },
      _ => Ok(false),
    }
  }

  /// Unit-like type: non-recursive, 0 indices, 1 ctor with 0 fields.
  /// If both values inhabit the same unit-like type, they're def-eq.
  fn try_def_eq_unit(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let a_ty = match self.with_infer_only(|tc| tc.infer(a)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let a_ty_w = match self.whnf(&a_ty) {
      Ok(w) => w,
      Err(_) => return Ok(false),
    };
    let (a_head, _) = collect_app_spine(&a_ty_w);
    let a_ind = match a_head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => return Ok(false),
    };
    // Check unit-like: non-recursive, 0 indices, 1 ctor with 0 fields
    let is_unit = match self.env.get(&a_ind) {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        if is_rec || indices != 0 || ctors.len() != 1 {
          false
        } else {
          match self.env.get(&ctors[0]) {
            Some(KConst::Ctor { fields, .. }) => fields == 0,
            _ => false,
          }
        }
      },
      _ => return Ok(false),
    };
    if !is_unit {
      return Ok(false);
    }
    // Both must have the same type
    let b_ty = match self.with_infer_only(|tc| tc.infer(b)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    self.is_def_eq(&a_ty_w, &b_ty)
  }

  // -----------------------------------------------------------------------
  // Nat literal ↔ constructor comparison
  // -----------------------------------------------------------------------

  /// Check if an expression is a nat-like value (literal, Nat.zero, Nat.succ _).
  fn is_nat_like(&self, e: &KExpr<M>) -> bool {
    match e.data() {
      ExprData::Nat(..) => true,
      ExprData::Const(id, _, _) => id.addr == self.prims.nat_zero.addr,
      ExprData::App(f, _, _) => {
        matches!(f.data(), ExprData::Const(id, _, _) if id.addr == self.prims.nat_succ.addr)
      },
      _ => false,
    }
  }

  /// Check if expression is nat zero (literal 0 or Nat.zero constructor).
  fn is_nat_zero(&self, e: &KExpr<M>) -> bool {
    match e.data() {
      ExprData::Nat(v, _, _) => v.0 == num_bigint::BigUint::ZERO,
      ExprData::Const(id, _, _) => id.addr == self.prims.nat_zero.addr,
      _ => false,
    }
  }

  /// If expression is nat-succ, return the predecessor.
  /// Matches both `Nat(n+1)` → `Nat(n)` and `Nat.succ e` → `e`.
  fn nat_succ_of(&self, e: &KExpr<M>) -> Option<KExpr<M>> {
    match e.data() {
      ExprData::Nat(v, _, _) => {
        if v.0 == num_bigint::BigUint::ZERO {
          return None;
        }
        let pred = lean_ffi::nat::Nat(&v.0 - num_bigint::BigUint::from(1u64));
        let pred_addr = crate::ix::address::Address::hash(&pred.to_le_bytes());
        Some(self.env.intern.intern_expr(KExpr::nat(pred, pred_addr)))
      },
      ExprData::App(f, arg, _) => match f.data() {
        ExprData::Const(id, _, _) if id.addr == self.prims.nat_succ.addr => {
          Some(arg.clone())
        },
        _ => None,
      },
      _ => None,
    }
  }

  /// Def-eq for nat-like values: handles mixed literal/constructor comparison.
  /// Fast-path: two Nat literals are compared directly by value (O(1) instead of
  /// O(n) recursion depth that would blow the def_eq_depth limit).
  fn is_def_eq_nat(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    // Fast path: both literals — compare by value directly
    if let (ExprData::Nat(va, _, _), ExprData::Nat(vb, _, _)) =
      (a.data(), b.data())
    {
      return Ok(va == vb);
    }
    if self.is_nat_zero(a) && self.is_nat_zero(b) {
      return Ok(true);
    }
    match (self.nat_succ_of(a), self.nat_succ_of(b)) {
      (Some(a_pred), Some(b_pred)) => self.is_def_eq(&a_pred, &b_pred),
      _ => Ok(false),
    }
  }

  /// M2: Nat offset reduction for lazy delta loop (lean4lean isDefEqOffset).
  /// Returns Some(true/false) if both are nat-zero or nat-succ, None otherwise.
  fn try_def_eq_offset(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<Option<bool>, TcError<M>> {
    // Fast path: both literals — compare by value directly
    if let (ExprData::Nat(va, _, _), ExprData::Nat(vb, _, _)) =
      (a.data(), b.data())
    {
      return Ok(Some(va == vb));
    }
    if self.is_nat_zero(a) && self.is_nat_zero(b) {
      return Ok(Some(true));
    }
    match (self.nat_succ_of(a), self.nat_succ_of(b)) {
      (Some(a_pred), Some(b_pred)) => {
        Ok(Some(self.is_def_eq(&a_pred, &b_pred)?))
      },
      _ => Ok(None),
    }
  }

  // -----------------------------------------------------------------------
  // String literal expansion
  // -----------------------------------------------------------------------

  /// String literal expansion (C++ kernel: try_string_lit_expansion_core).
  ///
  /// When `t` is a string literal, expand it to constructor form via
  /// `str_lit_to_constructor` (String.ofList [Char.ofNat c₁, ...]), WHNF the
  /// result so String.ofList + Char.ofNat delta-unfold to the canonical
  /// `String.ofByteArray ...` form, then compare with `s`.
  fn try_string_lit_expansion(
    &mut self,
    t: &KExpr<M>,
    s: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let str_val = match t.data() {
      ExprData::Str(v, _, _) => v.clone(),
      _ => return Ok(false),
    };
    let expanded = self.str_lit_to_constructor(&str_val);
    self.is_def_eq(&expanded, s)
  }

  /// Convert a string literal to constructor form:
  /// `"abc"` → `String.ofList (List.cons (Char.ofNat 97) (List.cons (Char.ofNat 98) (... List.nil)))`
  ///
  /// Uses `Char.ofNat` (not `Char.mk`) matching lean4lean/C++ kernel.
  /// Uses `String.ofList` (= `String.mk` in our env) matching lean4lean/C++ kernel.
  pub(super) fn str_lit_to_constructor(&mut self, s: &str) -> KExpr<M> {
    let char_const =
      self.intern(KExpr::cnst(self.prims.char_type.clone(), Box::new([])));
    let char_of_nat =
      self.intern(KExpr::cnst(self.prims.char_of_nat.clone(), Box::new([])));
    let string_mk =
      self.intern(KExpr::cnst(self.prims.string_of_list.clone(), Box::new([])));

    // List.nil.{0} Char
    let list_nil_z = self.intern(KExpr::cnst(
      self.prims.list_nil.clone(),
      Box::new([KUniv::zero()]),
    ));
    let nil = self.intern(KExpr::app(list_nil_z, char_const.clone()));

    // List.cons.{0} Char
    let list_cons_z = self.intern(KExpr::cnst(
      self.prims.list_cons.clone(),
      Box::new([KUniv::zero()]),
    ));
    let cons = self.intern(KExpr::app(list_cons_z, char_const));

    // Build list right-to-left: foldr
    let mut list = nil;
    for c in s.chars().rev() {
      let nat_val = lean_ffi::nat::Nat::from(c as u64);
      let nat_addr = crate::ix::address::Address::hash(&nat_val.to_le_bytes());
      let nat_lit = self.intern(KExpr::nat(nat_val, nat_addr));
      let char_val = self.intern(KExpr::app(char_of_nat.clone(), nat_lit));
      let partial = self.intern(KExpr::app(cons.clone(), char_val));
      list = self.intern(KExpr::app(partial, list));
    }

    // String.mk list
    self.intern(KExpr::app(string_mk, list))
  }

  // -----------------------------------------------------------------------
  // Eta expansion
  // -----------------------------------------------------------------------

  /// Lambda eta expansion (lean4lean style): if `t` is a lambda and `s` is not,
  /// infer `s`'s type, WHNF to get a forall, wrap `s` as `λ(ty). s #0`, compare with `t`.
  fn try_eta_expansion(
    &mut self,
    t: &KExpr<M>,
    s: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if !matches!(t.data(), ExprData::Lam(..))
      || matches!(s.data(), ExprData::Lam(..))
    {
      return Ok(false);
    }
    // Infer s's type, WHNF to forall to get the binder type
    let s_ty = match self.with_infer_only(|tc| tc.infer(s)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let s_ty_whnf = match self.whnf(&s_ty) {
      Ok(w) => w,
      Err(_) => return Ok(false),
    };
    let (name, bi, ty) = match s_ty_whnf.data() {
      ExprData::All(name, bi, ty, _, _) => {
        (name.clone(), bi.clone(), ty.clone())
      },
      _ => return Ok(false),
    };
    // Wrap s as λ(ty). s #0
    let s_lifted = lift(&self.env.intern, s, 1, 0);
    let v0 =
      self.intern(KExpr::var(0, M::meta_field(crate::ix::env::Name::anon())));
    let body = self.intern(KExpr::app(s_lifted, v0));
    let s_lam = self.intern(KExpr::lam(name, bi, ty, body));
    self.is_def_eq(t, &s_lam)
  }

  /// Struct eta (lean4lean style): if `s` is a fully-applied constructor of a
  /// struct-like type, check `proj(i, t) ≡ s.args[params+i]` for each field.
  /// Tries `tryEtaStructCore(t, s)` — caller should try both directions.
  fn try_eta_struct(
    &mut self,
    t: &KExpr<M>,
    s: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    use super::tc::collect_app_spine;

    let t_norm = self.whnf_no_delta(t).unwrap_or_else(|_| t.clone());

    // s must be a constructor application
    let (s_head, s_args) = collect_app_spine(s);
    let ctor_id = match s_head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => {
        self.dump_eta_trace("rhs-not-ctor-head", None, 0, &t_norm, s);
        return Ok(false);
      },
    };

    // Head must be a constructor
    let (induct_id, num_params, num_fields) = match self.env.get(&ctor_id) {
      Some(KConst::Ctor { induct, params, fields, .. }) => {
        (induct.clone(), u64_to_usize::<M>(params)?, u64_to_usize::<M>(fields)?)
      },
      _ => {
        self.dump_eta_trace("rhs-head-not-ctor", Some(&ctor_id), 0, &t_norm, s);
        return Ok(false);
      },
    };

    // Must be fully applied
    if s_args.len() != num_params + num_fields {
      self.dump_eta_trace(
        "ctor-arity",
        Some(&ctor_id),
        s_args.len(),
        &t_norm,
        s,
      );
      return Ok(false);
    }

    // Inductive must be struct-like (non-recursive, 0 indices, 1 ctor)
    match self.env.get(&induct_id) {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        if is_rec || indices != 0 || ctors.len() != 1 {
          self.dump_eta_trace(
            "not-struct-like",
            Some(&induct_id),
            0,
            &t_norm,
            s,
          );
          return Ok(false);
        }
      },
      _ => {
        self.dump_eta_trace(
          "inductive-missing",
          Some(&induct_id),
          0,
          &t_norm,
          s,
        );
        return Ok(false);
      },
    }

    // Types must be def-eq (lean4lean tryEtaStructCore, line 515).
    // No Prop guard here — struct eta in def-eq is safe even for Prop types
    // because we're checking equality, not constructing terms. The Prop guard
    // is only needed in iota's toCtorWhenStruct (whnf.rs try_struct_eta_iota)
    // where eta-expanding creates projections that would be unsound for Prop.
    let s_ty = match self.with_infer_only(|tc| tc.infer(s)) {
      Ok(ty) => ty,
      Err(_) => {
        self.dump_eta_trace("infer-rhs-type", Some(&induct_id), 0, t, s);
        return Ok(false);
      },
    };
    let t_ty = match self.with_infer_only(|tc| tc.infer(&t_norm)) {
      Ok(ty) => ty,
      Err(_) => {
        self.dump_eta_trace("infer-lhs-type", Some(&induct_id), 0, &t_norm, s);
        return Ok(false);
      },
    };
    if !self.is_def_eq(&t_ty, &s_ty)? {
      self.dump_eta_trace("type-mismatch", Some(&induct_id), 0, &t_norm, s);
      return Ok(false);
    }

    if let Some(base) =
      self.eta_expansion_base(&induct_id, num_params, num_fields, &s_args)?
      && self.is_def_eq(&t_norm, &base)?
    {
      self.dump_eta_trace(
        "eta-base",
        Some(&induct_id),
        num_fields,
        &t_norm,
        &base,
      );
      return Ok(true);
    }

    // Compare each field: proj(induct, i, t) ≡ s_args[params + i]
    for i in 0..num_fields {
      let proj =
        self.intern(KExpr::prj(induct_id.clone(), i as u64, t_norm.clone()));
      if !self.is_def_eq(&proj, &s_args[num_params + i])? {
        self.dump_eta_trace(
          "field-mismatch",
          Some(&induct_id),
          i,
          &proj,
          &s_args[num_params + i],
        );
        return Ok(false);
      }
    }

    self.dump_eta_trace("ok", Some(&induct_id), num_fields, &t_norm, s);
    Ok(true)
  }

  fn eta_expansion_base(
    &mut self,
    induct_id: &KId<M>,
    num_params: usize,
    num_fields: usize,
    args: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let mut base: Option<KExpr<M>> = None;
    for i in 0..num_fields {
      let field = &args[num_params + i];
      let field = self.whnf_no_delta(field)?;
      let ExprData::Prj(id, idx, val, _) = field.data() else {
        return Ok(None);
      };
      if id.addr != induct_id.addr || *idx != i as u64 {
        return Ok(None);
      }
      let val = self.whnf_no_delta(val).unwrap_or_else(|_| val.clone());
      match &base {
        Some(base) if base.hash_key() != val.hash_key() => return Ok(None),
        Some(_) => {},
        None => base = Some(val),
      }
    }
    Ok(base)
  }

  /// App spine comparison (lean4lean isDefEqApp): decompose both sides into
  /// head + args and compare componentwise. Handles multi-arg apps.
  fn try_def_eq_app(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if !matches!(a.data(), ExprData::App(..))
      || !matches!(b.data(), ExprData::App(..))
    {
      return Ok(false);
    }
    let (a_head, a_args) = collect_app_spine(a);
    let (b_head, b_args) = collect_app_spine(b);
    if a_args.len() != b_args.len() {
      return Ok(false);
    }
    if !self.is_def_eq(&a_head, &b_head)? {
      return Ok(false);
    }
    for (ai, bi) in a_args.iter().zip(b_args.iter()) {
      if !self.is_def_eq(ai, bi)? {
        return Ok(false);
      }
    }
    Ok(true)
  }

  /// Check if expression is the Bool.true constant.
  fn is_bool_true(&self, e: &KExpr<M>) -> bool {
    match e.data() {
      ExprData::Const(id, us, _) => {
        us.is_empty() && id.addr == self.prims.bool_true.addr
      },
      _ => false,
    }
  }

  /// Check if a constant is delta-reducible.
  fn is_delta(&self, id: &KId<M>) -> bool {
    matches!(
      self.env.get(id),
      Some(KConst::Defn { kind, .. })
        if matches!(kind, DefKind::Definition | DefKind::Theorem)
    )
  }

  /// Check if a constant has Regular reducibility hints (not Abbrev or Opaque).
  /// Used to guard the same-head-spine optimization (lean4lean: dt.hints.isRegular).
  fn is_regular(&self, id: &KId<M>) -> bool {
    use crate::ix::env::ReducibilityHints;
    matches!(
      self.env.get(id),
      Some(KConst::Defn { hints: ReducibilityHints::Regular(_), .. })
    )
  }

  /// Reducibility rank by id. Higher rank = unfold first.
  ///
  /// Returns a `(class, height)` tuple compared lexicographically, so that
  /// `Abbrev` strictly dominates every `Regular(h)` regardless of `h`. The
  /// previous `u32` encoding mapped `Abbrev` to `u32::MAX - 1` and saturated
  /// `Regular(h)` to `h.saturating_add(1)`, which collapsed at `h ≥ u32::MAX-2`
  /// — flipping delta direction in the rare case of an `Abbrev` paired with
  /// a maximally heavy regular definition. The structured tuple matches
  /// Lean's `compare(d_t->get_hints(), d_s->get_hints())`
  /// (`type_checker.cpp:910`):
  ///
  /// - `Opaque` / `Theorem` / unknown → `(0, 0)`
  /// - `Regular(h)` → `(1, h)` (ordered by height within the class)
  /// - `Abbrev` → `(2, 0)` (strictly greater than every `Regular(h)`)
  fn def_rank_id(&self, id: &KId<M>) -> (u8, u32) {
    use crate::ix::env::ReducibilityHints;
    match self.env.get(id) {
      Some(KConst::Defn { kind, hints, .. }) => match kind {
        DefKind::Opaque | DefKind::Theorem => (0, 0),
        DefKind::Definition => match hints {
          ReducibilityHints::Opaque => (0, 0),
          ReducibilityHints::Regular(h) => (1, h),
          ReducibilityHints::Abbrev => (2, 0),
        },
      },
      _ => (0, 0),
    }
  }

  // -----------------------------------------------------------------------
  // Post-delta congruence and projection unfolding (C5, C6)
  // -----------------------------------------------------------------------

  /// Structural congruence after lazy delta exhaustion (lean4lean isDefEqConst/Proj).
  /// Checks Const-Const, Var-Var, Prj-Prj without further reduction.
  fn try_structural_congruence(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    match (a.data(), b.data()) {
      (ExprData::Const(id1, us1, _), ExprData::Const(id2, us2, _)) => Ok(
        id1.addr == id2.addr
          && us1.len() == us2.len()
          && us1.iter().zip(us2.iter()).all(|(u, v)| univ_eq(u, v)),
      ),
      (ExprData::Var(i, _, _), ExprData::Var(j, _, _)) => Ok(i == j),
      (ExprData::Prj(id1, f1, v1, _), ExprData::Prj(id2, f2, v2, _)) => {
        if id1.addr != id2.addr || f1 != f2 {
          return Ok(false);
        }
        let mut v1 = v1.clone();
        let mut v2 = v2.clone();
        self.lazy_delta_proj_reduction(id1, *f1, &mut v1, &mut v2)
      },
      _ => Ok(false),
    }
  }

  fn lazy_delta_proj_reduction(
    &mut self,
    struct_id: &KId<M>,
    field: u64,
    a: &mut KExpr<M>,
    b: &mut KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let mut fuel = MAX_WHNF_FUEL;
    loop {
      if fuel == 0 {
        self.dump_def_eq_max("proj-delta-fuel", a, b, None, None);
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;
      match self.lazy_delta_reduction_step(a, b)? {
        LazyDeltaStep::Equal => return Ok(true),
        LazyDeltaStep::Continue => {},
        LazyDeltaStep::Unknown => {
          self.dump_proj_delta_trace("stuck", struct_id, field, a, b);
          let pa = self.try_project_core(struct_id, field, a);
          let pb = self.try_project_core(struct_id, field, b);
          return match (pa, pb) {
            (Some(pa), Some(pb)) => {
              self.dump_proj_delta_trace(
                "projected",
                struct_id,
                field,
                &pa,
                &pb,
              );
              self.is_def_eq(&pa, &pb)
            },
            _ => {
              self.dump_proj_delta_trace("fallback", struct_id, field, a, b);
              self.is_def_eq(a, b)
            },
          };
        },
      }
    }
  }

  fn lazy_delta_reduction_step(
    &mut self,
    a: &mut KExpr<M>,
    b: &mut KExpr<M>,
  ) -> Result<LazyDeltaStep, TcError<M>> {
    let a_head = head_const_id(a);
    let b_head = head_const_id(b);
    let a_delta = a_head.as_ref().is_some_and(|h| self.is_delta(h));
    let b_delta = b_head.as_ref().is_some_and(|h| self.is_delta(h));

    if !a_delta && !b_delta {
      return Ok(LazyDeltaStep::Unknown);
    }

    if a_delta && !b_delta {
      if let Some(b2) = self.try_unfold_proj_app(b)? {
        *b = b2;
      } else if let Some(a2) = self.delta_unfold_one(a)? {
        *a = self.whnf_core(&a2)?;
      } else {
        return Ok(LazyDeltaStep::Unknown);
      }
    } else if !a_delta && b_delta {
      if let Some(a2) = self.try_unfold_proj_app(a)? {
        *a = a2;
      } else if let Some(b2) = self.delta_unfold_one(b)? {
        *b = self.whnf_core(&b2)?;
      } else {
        return Ok(LazyDeltaStep::Unknown);
      }
    } else {
      let a_id = a_head.as_ref().expect("a_delta implies head");
      let b_id = b_head.as_ref().expect("b_delta implies head");
      let cmp = self.def_rank_id(a_id).cmp(&self.def_rank_id(b_id));
      if cmp.is_gt() {
        if let Some(a2) = self.delta_unfold_one(a)? {
          *a = self.whnf_core(&a2)?;
        } else {
          return Ok(LazyDeltaStep::Unknown);
        }
      } else if cmp.is_lt() {
        if let Some(b2) = self.delta_unfold_one(b)? {
          *b = self.whnf_core(&b2)?;
        } else {
          return Ok(LazyDeltaStep::Unknown);
        }
      } else {
        if a_id.addr == b_id.addr
          && self.is_regular(a_id)
          && let Some(true) = self.try_same_head_spine(a, b)?
        {
          return Ok(LazyDeltaStep::Equal);
        }
        let a2 = self.delta_unfold_one(a)?;
        let b2 = self.delta_unfold_one(b)?;
        match (a2, b2) {
          (Some(a2), Some(b2)) => {
            *a = self.whnf_core(&a2)?;
            *b = self.whnf_core(&b2)?;
          },
          (Some(a2), None) => *a = self.whnf_core(&a2)?,
          (None, Some(b2)) => *b = self.whnf_core(&b2)?,
          (None, None) => return Ok(LazyDeltaStep::Unknown),
        }
      }
    }

    if a.ptr_eq(b) || self.quick_def_eq(a, b)? {
      Ok(LazyDeltaStep::Equal)
    } else {
      Ok(LazyDeltaStep::Continue)
    }
  }

  fn try_project_core(
    &mut self,
    struct_id: &KId<M>,
    field: u64,
    e: &KExpr<M>,
  ) -> Option<KExpr<M>> {
    self.try_proj_reduce(struct_id, field, e)
  }

  fn dump_proj_delta_trace(
    &self,
    phase: &str,
    id: &KId<M>,
    field: u64,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) {
    let Some(filter) = IX_PROJ_DELTA_TRACE.as_ref() else {
      return;
    };
    if !self.debug_label_matches_env() {
      return;
    }
    let id_s = id.to_string();
    if !filter.is_empty() && !id_s.contains(filter) {
      return;
    }
    eprintln!(
      "[proj-delta] const={} depth={} phase={} proj={}.{} a={} b={}",
      self.debug_label.as_deref().unwrap_or("<unknown>"),
      self.def_eq_depth,
      phase,
      id,
      field,
      compact_def_eq_expr(a),
      compact_def_eq_expr(b)
    );
  }

  /// If the head of `e` is a projection, try reducing it via whnf_no_delta.
  /// Returns the reduced form if it changed, None otherwise (lean4lean tryUnfoldProjApp).
  fn try_unfold_proj_app(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, _) = collect_app_spine(e);
    if !matches!(head.data(), ExprData::Prj(..)) {
      return Ok(None);
    }
    let reduced = self.whnf_no_delta(e)?;
    if reduced.ptr_eq(e) { Ok(None) } else { Ok(Some(reduced)) }
  }

  fn dump_eta_trace(
    &self,
    reason: &str,
    id: Option<&KId<M>>,
    idx: usize,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) {
    let Some(filter) = IX_ETA_TRACE.as_ref() else {
      return;
    };
    if !self.debug_label_matches_env() {
      return;
    }
    let id_s = id.map_or_else(|| "<none>".into(), |id| id.to_string());
    if !filter.is_empty() && !id_s.contains(filter) {
      return;
    }
    eprintln!(
      "[eta] const={} depth={} reason={} id={} idx={} a={} b={}",
      self.debug_label.as_deref().unwrap_or("<unknown>"),
      self.def_eq_depth,
      reason,
      id_s,
      idx,
      compact_def_eq_expr(a),
      compact_def_eq_expr(b)
    );
  }
}

enum LazyDeltaStep {
  Equal,
  Unknown,
  Continue,
}

fn compact_def_eq_expr<M: KernelMode>(e: &KExpr<M>) -> String {
  let (head, args) = collect_app_spine(e);
  let base = match head.data() {
    ExprData::Var(i, _, _) => format!("#{i}"),
    ExprData::Sort(u, _) => format!("Sort({u})"),
    ExprData::Const(id, us, _) => format!("{id}.{{{}}}", us.len()),
    ExprData::App(..) => "app".to_string(),
    ExprData::Lam(..) => "lam".to_string(),
    ExprData::All(..) => "forall".to_string(),
    ExprData::Let(..) => "let".to_string(),
    ExprData::Prj(id, field, val, _) => {
      format!("Prj({id}.{field}, {})", compact_def_eq_expr(val))
    },
    ExprData::Nat(v, _, _) => format!("Nat({})", v.0),
    ExprData::Str(v, _, _) => format!("Str(len={})", v.len()),
  };
  if args.is_empty() {
    format!("{base}@{}", short_def_eq_addr(e))
  } else {
    let shown = args
      .iter()
      .take(6)
      .map(compact_def_eq_head)
      .collect::<Vec<_>>()
      .join(", ");
    let more = if args.len() > 6 { ", ..." } else { "" };
    format!("{base}/{} [{shown}{more}]@{}", args.len(), short_def_eq_addr(e))
  }
}

fn compact_def_eq_head<M: KernelMode>(e: &KExpr<M>) -> String {
  let (head, args) = collect_app_spine(e);
  let base = match head.data() {
    ExprData::Var(i, _, _) => format!("#{i}"),
    ExprData::Sort(u, _) => format!("Sort({u})"),
    ExprData::Const(id, us, _) => format!("{id}.{{{}}}", us.len()),
    ExprData::App(..) => "app".to_string(),
    ExprData::Lam(..) => "lam".to_string(),
    ExprData::All(..) => "forall".to_string(),
    ExprData::Let(..) => "let".to_string(),
    ExprData::Prj(id, field, _, _) => format!("Prj({id}.{field})"),
    ExprData::Nat(v, _, _) => format!("Nat({})", v.0),
    ExprData::Str(v, _, _) => format!("Str(len={})", v.len()),
  };
  if args.is_empty() { base } else { format!("{base}/{}", args.len()) }
}

fn short_def_eq_addr<M: KernelMode>(e: &KExpr<M>) -> String {
  e.addr().to_hex().chars().take(12).collect()
}

/// Canonical ordering for cache keys: (min, max) by hash bytes.
fn canonical_pair(a: Addr, b: Addr) -> (Addr, Addr) {
  if a.as_bytes() <= b.as_bytes() { (a, b) } else { (b, a) }
}

/// Extract head constant KId from expression or app spine.
fn head_const_id<M: KernelMode>(e: &KExpr<M>) -> Option<KId<M>> {
  match e.data() {
    ExprData::Const(id, _, _) => Some(id.clone()),
    ExprData::App(..) => {
      let (head, _) = collect_app_spine(e);
      match head.data() {
        ExprData::Const(id, _, _) => Some(id.clone()),
        _ => None,
      }
    },
    _ => None,
  }
}

/// Extract head constant's display form as a string, for diagnostic
/// prefix matching. Uses `{kid}`'s Display impl (which is defined for
/// every `KernelMode`), not the inner `Name` which only has Display in
/// Meta mode. Returns `None` if the head isn't a `Const`.
fn head_const_name<M: KernelMode>(e: &KExpr<M>) -> Option<String> {
  let id = head_const_id(e)?;
  Some(format!("{id}"))
}

impl<M: KernelMode> TypeChecker<M> {
  fn dump_def_eq_max(
    &self,
    kind: &str,
    a: &KExpr<M>,
    b: &KExpr<M>,
    wa: Option<&KExpr<M>>,
    wb: Option<&KExpr<M>>,
  ) {
    let Some(filter) = IX_DEF_EQ_MAX_DUMP.as_ref() else {
      return;
    };
    if !self.debug_label_matches_env() {
      return;
    }
    let a_head = head_const_name(a).unwrap_or_else(|| "<none>".to_string());
    let b_head = head_const_name(b).unwrap_or_else(|| "<none>".to_string());
    let wa_head =
      wa.and_then(head_const_name).unwrap_or_else(|| "<none>".to_string());
    let wb_head =
      wb.and_then(head_const_name).unwrap_or_else(|| "<none>".to_string());
    if !filter.is_empty()
      && !a_head.contains(filter)
      && !b_head.contains(filter)
      && !wa_head.contains(filter)
      && !wb_head.contains(filter)
    {
      return;
    }
    eprintln!(
      "[deq max] {kind} depth={} a_head={} b_head={} wa_head={} wb_head={}",
      self.def_eq_depth, a_head, b_head, wa_head, wb_head
    );
    eprintln!("  a:  {a}");
    eprintln!("  b:  {b}");
    if let Some(wa) = wa {
      eprintln!("  wa: {wa}");
    }
    if let Some(wb) = wb {
      eprintln!("  wb: {wb}");
    }
  }
}

#[cfg(test)]
mod tests {
  use std::sync::Arc;

  use super::super::constant::KConst;
  use super::super::env::KEnv;
  use super::super::expr::KExpr;
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::{Anon, Meta};
  use super::super::tc::TypeChecker;
  use crate::ix::address::Address;
  use crate::ix::env::{DataValue, DefinitionSafety, Name, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;

  type AE = KExpr<Anon>;
  type ME = KExpr<Meta>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }
  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }
  fn mk_meta_name(s: &str) -> Name {
    let mut name = Name::anon();
    for part in s.split('.') {
      name = Name::str(name, part.to_string());
    }
    name
  }
  fn sort0() -> AE {
    AE::sort(AU::zero())
  }

  fn sort1() -> AE {
    AE::sort(AU::succ(AU::zero()))
  }

  fn env_with_id() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    let id_ty = AE::all((), (), sort0(), sort0());
    let id_val = AE::lam((), (), sort0(), AE::var(0, ()));
    env.insert(
      mk_id("id"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: id_ty,
        val: id_val,
        lean_all: (),
        block: mk_id("id"),
      },
    );
    env
  }

  /// Insert a `Defn` with the given reducibility hints under `name`, returning
  /// its `KId`. Used by `def_rank_id` ordering tests.
  fn insert_rank_def(
    env: &Arc<KEnv<Anon>>,
    name: &str,
    hints: ReducibilityHints,
  ) -> KId<Anon> {
    let id = mk_id(name);
    env.insert(
      id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints,
        lvls: 0,
        ty: sort1(),
        val: sort0(),
        lean_all: (),
        block: id.clone(),
      },
    );
    id
  }

  /// `Abbrev` must outrank a `Regular(u32::MAX)` — the saturation collision
  /// the `def_weight_id : u32` encoding admitted (audit Tier 1 #3).
  #[test]
  fn def_rank_abbrev_above_saturated_regular() {
    let env = Arc::new(KEnv::new());
    let abbrev = insert_rank_def(&env, "abbrev", ReducibilityHints::Abbrev);
    let regular =
      insert_rank_def(&env, "regular", ReducibilityHints::Regular(u32::MAX));
    let tc = TypeChecker::new(Arc::clone(&env));

    assert!(tc.def_rank_id(&abbrev) > tc.def_rank_id(&regular));
  }

  /// Within the `Regular` class, height orders rank monotonically.
  #[test]
  fn def_rank_regular_orders_by_height() {
    let env = Arc::new(KEnv::new());
    let low = insert_rank_def(&env, "low", ReducibilityHints::Regular(1));
    let high = insert_rank_def(&env, "high", ReducibilityHints::Regular(10));
    let tc = TypeChecker::new(Arc::clone(&env));

    assert!(tc.def_rank_id(&high) > tc.def_rank_id(&low));
  }

  #[test]
  fn def_eq_ptr_eq() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let e = sort0();
    assert!(tc.is_def_eq(&e, &e).unwrap());
  }

  #[test]
  fn def_eq_sort_same() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let s1 = AE::sort(AU::zero());
    let s2 = AE::sort(AU::zero());
    assert!(tc.is_def_eq(&s1, &s2).unwrap());
  }

  #[test]
  fn def_eq_sort_diff() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let s0 = AE::sort(AU::zero());
    let s1 = AE::sort(AU::succ(AU::zero()));
    assert!(!tc.is_def_eq(&s0, &s1).unwrap());
  }

  #[test]
  fn def_eq_const_same() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let c1 = AE::cnst(mk_id("id"), Box::new([]));
    let c2 = AE::cnst(mk_id("id"), Box::new([]));
    assert!(tc.is_def_eq(&c1, &c2).unwrap());
  }

  #[test]
  fn def_eq_ignores_meta_mdata() {
    let env = Arc::new(KEnv::<Meta>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let id = KId::new(mk_addr("C"), mk_meta_name("C"));
    let tagged = ME::cnst_mdata(
      id.clone(),
      Box::new([]),
      vec![vec![(
        mk_meta_name("tag"),
        DataValue::OfString("ignored".to_string()),
      )]],
    );
    let plain = ME::cnst(id, Box::new([]));

    assert_ne!(tagged.addr(), plain.addr());
    assert!(tc.is_def_eq(&tagged, &plain).unwrap());
  }

  #[test]
  fn def_eq_const_diff_addr() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let c1 = AE::cnst(mk_id("a"), Box::new([]));
    let c2 = AE::cnst(mk_id("b"), Box::new([]));
    assert!(!tc.is_def_eq(&c1, &c2).unwrap());
  }

  #[test]
  fn def_eq_lam_structural() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let l1 = AE::lam((), (), sort0(), AE::var(0, ()));
    let l2 = AE::lam((), (), sort0(), AE::var(0, ()));
    assert!(tc.is_def_eq(&l1, &l2).unwrap());
  }

  #[test]
  fn def_eq_all_structural() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let a1 = AE::all((), (), sort0(), sort0());
    let a2 = AE::all((), (), sort0(), sort0());
    assert!(tc.is_def_eq(&a1, &a2).unwrap());
  }

  #[test]
  fn def_eq_beta() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // (λ x. x)(Sort 0) ≡ Sort 0
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let app = AE::app(lam, sort0());
    assert!(tc.is_def_eq(&app, &sort0()).unwrap());
  }

  #[test]
  fn def_eq_delta_unfold() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // id(Sort 0) ≡ Sort 0 (via delta + beta)
    let id_app = AE::app(AE::cnst(mk_id("id"), Box::new([])), sort0());
    assert!(tc.is_def_eq(&id_app, &sort0()).unwrap());
  }

  #[test]
  fn def_eq_cache_hit() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let a = sort0();
    let b = AE::sort(AU::zero());
    assert!(tc.is_def_eq(&a, &b).unwrap());
    // Second call should hit cache
    assert!(tc.is_def_eq(&a, &b).unwrap());
  }

  #[test]
  fn def_eq_closed_cache_ignores_context_across_checkers() {
    let env = env_with_id();
    let a = AE::app(AE::cnst(mk_id("id"), Box::new([])), sort0());
    let b = sort0();

    let mut tc1 = TypeChecker::new(Arc::clone(&env));
    assert!(tc1.is_def_eq(&a, &b).unwrap());
    let cache_len = env.def_eq_cache.len();

    let mut tc2 = TypeChecker::new(Arc::clone(&env));
    tc2.push_local(sort1());
    assert!(tc2.is_def_eq(&a, &b).unwrap());
    assert_eq!(env.def_eq_cache.len(), cache_len);
  }

  // =========================================================================
  // Tier 3: proof irrelevance
  //
  // Two terms whose types live in Prop (Sort 0) are definitionally equal
  // regardless of their value structure. Terms whose types live in Type
  // (Sort ≥ 1) must match structurally.
  // =========================================================================

  /// Env with `P : Prop`, `p1 p2 : P`, `T : Type`, `a1 a2 : T`.
  fn env_with_prop_and_type_axioms() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());

    // P : Prop
    env.insert(
      mk_id("P"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort0(), // Sort 0 = Prop
      },
    );
    // T : Type
    env.insert(
      mk_id("T"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::sort(AU::succ(AU::zero())), // Sort 1 = Type
      },
    );
    // p1, p2 : P
    for name in ["p1", "p2"] {
      env.insert(
        mk_id(name),
        KConst::Axio {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: 0,
          ty: AE::cnst(mk_id("P"), Box::new([])),
        },
      );
    }
    // a1, a2 : T
    for name in ["a1", "a2"] {
      env.insert(
        mk_id(name),
        KConst::Axio {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: 0,
          ty: AE::cnst(mk_id("T"), Box::new([])),
        },
      );
    }
    env
  }

  #[test]
  fn def_eq_proof_irrelevance_prop() {
    // Two structurally distinct proofs of the same Prop type are def-eq.
    let env = env_with_prop_and_type_axioms();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let p1 = AE::cnst(mk_id("p1"), Box::new([]));
    let p2 = AE::cnst(mk_id("p2"), Box::new([]));
    assert!(tc.is_def_eq(&p1, &p2).unwrap());
  }

  #[test]
  fn def_eq_proof_irrelevance_symmetric() {
    let env = env_with_prop_and_type_axioms();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let p1 = AE::cnst(mk_id("p1"), Box::new([]));
    let p2 = AE::cnst(mk_id("p2"), Box::new([]));
    assert!(tc.is_def_eq(&p1, &p2).unwrap());
    assert!(tc.is_def_eq(&p2, &p1).unwrap());
  }

  #[test]
  fn def_eq_no_irrelevance_for_type_level() {
    // Proof irrelevance must NOT apply to Type-valued terms.
    let env = env_with_prop_and_type_axioms();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let a1 = AE::cnst(mk_id("a1"), Box::new([]));
    let a2 = AE::cnst(mk_id("a2"), Box::new([]));
    assert!(!tc.is_def_eq(&a1, &a2).unwrap());
  }

  // =========================================================================
  // Tier 5: unit-like types
  //
  // An inductive with 0 indices, 1 constructor with 0 fields, and `is_rec
  // = false` is a "unit-like" type. Any two values of such a type are
  // def-eq (both reduce to the unique constructor).
  // =========================================================================

  /// Env with `Unit : Sort 0` (0 indices, 1 ctor Unit.mk with 0 fields).
  fn env_with_unit_like() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());

    // Unit.mk : Unit
    env.insert(
      mk_id("Unit.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Unit"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: AE::cnst(mk_id("Unit"), Box::new([])),
      },
    );
    // Unit : Prop  (make it a Prop inductive so proof irrelevance is out of the
    // picture and we exercise try_def_eq_unit specifically)
    env.insert(
      mk_id("Unit"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("Unit"),
        member_idx: 0,
        ty: AE::sort(AU::succ(AU::zero())),
        ctors: vec![mk_id("Unit.mk")],
        lean_all: (),
      },
    );
    // Two different proof-style terms of Unit, both reducing to Unit.mk.
    for name in ["u1", "u2"] {
      env.insert(
        mk_id(name),
        KConst::Axio {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: 0,
          ty: AE::cnst(mk_id("Unit"), Box::new([])),
        },
      );
    }
    env
  }

  #[test]
  fn def_eq_unit_like_distinct_values() {
    // Two distinct inhabitants of a unit-like inductive are def-eq.
    let env = env_with_unit_like();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let u1 = AE::cnst(mk_id("u1"), Box::new([]));
    let u2 = AE::cnst(mk_id("u2"), Box::new([]));
    assert!(tc.is_def_eq(&u1, &u2).unwrap());
  }

  #[test]
  fn def_eq_unit_like_ctor_and_opaque() {
    // The explicit constructor and an opaque axiom of the same unit-like
    // type are def-eq.
    let env = env_with_unit_like();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let mk = AE::cnst(mk_id("Unit.mk"), Box::new([]));
    let u1 = AE::cnst(mk_id("u1"), Box::new([]));
    assert!(tc.is_def_eq(&mk, &u1).unwrap());
  }

  // =========================================================================
  // Tier 5: eta expansion for lambdas
  //
  // `f` def-eq `λ x, f x` when `f`'s type is a forall.
  // =========================================================================

  /// Env with `A : Type 0`, `B : Type 0`, `f : A → B`.
  fn env_with_fun() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
    env.insert(
      mk_id("A"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::sort(AU::succ(AU::zero())),
      },
    );
    env.insert(
      mk_id("B"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::sort(AU::succ(AU::zero())),
      },
    );
    let a_cnst = AE::cnst(mk_id("A"), Box::new([]));
    let b_cnst = AE::cnst(mk_id("B"), Box::new([]));
    // A → B = ∀ (_ : A), B (since the body doesn't mention the bound var,
    // using Var(1) in codomain would be wrong; Var-free B is correct).
    let arrow_ab = AE::all((), (), a_cnst, b_cnst);
    env.insert(
      mk_id("f"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: arrow_ab,
      },
    );
    env
  }

  #[test]
  fn def_eq_eta_lambda_wraps_function() {
    // f ≡ λ (x : A), f x
    let env = env_with_fun();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let f = AE::cnst(mk_id("f"), Box::new([]));
    // Lifting `f` by 1 is a no-op because it's closed.
    let eta = AE::lam(
      (),
      (),
      AE::cnst(mk_id("A"), Box::new([])),
      AE::app(f.clone(), AE::var(0, ())),
    );
    assert!(tc.is_def_eq(&f, &eta).unwrap());
  }

  #[test]
  fn def_eq_eta_lambda_symmetric() {
    // λ x, f x ≡ f (reverse direction)
    let env = env_with_fun();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let f = AE::cnst(mk_id("f"), Box::new([]));
    let eta = AE::lam(
      (),
      (),
      AE::cnst(mk_id("A"), Box::new([])),
      AE::app(f.clone(), AE::var(0, ())),
    );
    assert!(tc.is_def_eq(&eta, &f).unwrap());
  }

  #[test]
  fn def_eq_eta_lambda_fails_on_non_function() {
    // `a : A` is not a function — η-expanding makes no sense, must NOT fire.
    let env = env_with_fun();
    env.insert(
      mk_id("a"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::cnst(mk_id("A"), Box::new([])),
      },
    );
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let a = AE::cnst(mk_id("a"), Box::new([]));
    // A bogus "eta-like" wrapping of a non-function.
    let bogus = AE::lam(
      (),
      (),
      AE::cnst(mk_id("A"), Box::new([])),
      AE::app(a.clone(), AE::var(0, ())),
    );
    assert!(!tc.is_def_eq(&a, &bogus).unwrap());
  }

  // =========================================================================
  // Tier 5: struct eta
  //
  // For a struct-like inductive (non-recursive, 0 indices, single 0-field
  // constructor? — here use a 2-field struct), a term `t` is def-eq to
  // `Mk (t.1) (t.2)` via struct-eta.
  // =========================================================================

  /// Env with `Pair : Type 0` whose only ctor `Pair.mk : A → B → Pair`.
  fn env_with_pair_struct() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());

    env.insert(
      mk_id("A"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::sort(AU::succ(AU::zero())),
      },
    );
    env.insert(
      mk_id("B"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::sort(AU::succ(AU::zero())),
      },
    );
    // Pair : Type  (non-recursive, 0 indices, 1 ctor)
    env.insert(
      mk_id("Pair"),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: mk_id("Pair"),
        member_idx: 0,
        ty: AE::sort(AU::succ(AU::zero())),
        ctors: vec![mk_id("Pair.mk")],
        lean_all: (),
      },
    );
    let a_cnst = AE::cnst(mk_id("A"), Box::new([]));
    let b_cnst = AE::cnst(mk_id("B"), Box::new([]));
    let pair_cnst = AE::cnst(mk_id("Pair"), Box::new([]));
    // Pair.mk : A → B → Pair
    env.insert(
      mk_id("Pair.mk"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Pair"),
        cidx: 0,
        params: 0,
        fields: 2,
        ty: AE::all((), (), a_cnst, AE::all((), (), b_cnst, pair_cnst)),
      },
    );
    // a : A, b : B, p : Pair
    env.insert(
      mk_id("a"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::cnst(mk_id("A"), Box::new([])),
      },
    );
    env.insert(
      mk_id("b"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::cnst(mk_id("B"), Box::new([])),
      },
    );
    env.insert(
      mk_id("p"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: AE::cnst(mk_id("Pair"), Box::new([])),
      },
    );
    env
  }

  #[test]
  fn def_eq_struct_eta_via_projections() {
    // p ≡ Pair.mk p.1 p.2
    let env = env_with_pair_struct();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let p = AE::cnst(mk_id("p"), Box::new([]));
    let proj0 = AE::prj(mk_id("Pair"), 0, p.clone());
    let proj1 = AE::prj(mk_id("Pair"), 1, p.clone());
    let mk_app =
      AE::app(AE::app(AE::cnst(mk_id("Pair.mk"), Box::new([])), proj0), proj1);
    assert!(tc.is_def_eq(&p, &mk_app).unwrap());
  }
}
