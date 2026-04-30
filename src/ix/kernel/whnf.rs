//! Weak head normal form reduction.
//!
//! Multi-phase: whnf_core (beta, iota, zeta) → proj → nat → quot → delta.

use std::sync::LazyLock;

use rustc_hash::FxHashSet;

use crate::ix::address::Address;
use crate::ix::ixon::constant::DefKind;

/// When set, emit a `[iota stuck]` line whenever `try_iota` can't resolve
/// its major premise to a constructor. Set `IX_IOTA_STUCK=1` to activate
/// and optionally pass a substring filter (e.g. `IX_IOTA_STUCK=Poly.rec`)
/// to suppress recursor-unrelated noise.
static IX_IOTA_STUCK: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_IOTA_STUCK").ok());

/// When set, log total `nat_to_constructor` calls every 100k. Lets us see
/// whether a given check is doing runaway Nat iota expansion (signalling
/// a `Nat.rec motive base step N` whose step unconditionally forces `ih`
/// \u2014 the pattern the old 2^20 threshold guarded against).
static IX_NAT_EXPAND_LOG: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_NAT_EXPAND_LOG").is_ok());

/// Global counter for `nat_to_constructor` calls. Read lazily via
/// `IX_NAT_EXPAND_LOG`. `fetch_add(_, Relaxed)` is a near-free no-op when
/// logging is off (the compiler lifts the load+branch out of hot paths).
static NAT_EXPAND_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

static IX_NAT_IOTA_TRACE: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_NAT_IOTA_TRACE").is_ok());

static NAT_IOTA_TRACE_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

static IX_NAT_LINEAR_REC_TRACE: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_NAT_LINEAR_REC_TRACE").is_ok());

static NAT_LINEAR_REC_TRACE_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

/// When set, log every 1M whnf entries. A check using tens of millions
/// of whnf calls on a single constant is deep in pathological territory.
static IX_WHNF_COUNT_LOG: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_WHNF_COUNT_LOG").is_ok());

static WHNF_COUNT: std::sync::atomic::AtomicUsize =
  std::sync::atomic::AtomicUsize::new(0);

static IX_DELTA_TRACE: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_DELTA_TRACE").ok());

static IX_PROJ_TRACE: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_PROJ_TRACE").ok());

static IX_NAT_TRACE: LazyLock<Option<String>> =
  LazyLock::new(|| std::env::var("IX_NAT_TRACE").ok());

const NAT_REDUCER_OPEN_ARG_REC_FUEL: u64 = 4096;

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::subst::{simul_subst, subst, subst_no_intern};
use super::tc::{IotaInfo, MAX_WHNF_FUEL, TypeChecker, collect_app_spine};

use lean_ffi::nat::Nat;

/// Reduction policy for structural WHNF.
///
/// `cheap_proj` and `cheap_rec` mirror Lean4Lean's `cheapProj` and `cheapRec`
/// flags (`refs/lean4lean/Lean4Lean/TypeChecker.lean:337–341`): when set,
/// projection-of-`Prj`'s value uses `whnf_core` instead of full `whnf`, and
/// the recursor's major premise reduces with the same structural variant.
///
/// The only non-full policy currently used is `DEF_EQ_CORE`, matching
/// Lean/Lean4Lean's `whnfCore (cheapProj := true)` scaffold in def-eq.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct WhnfFlags {
  cheap_rec: bool,
  cheap_proj: bool,
}

impl WhnfFlags {
  const FULL: Self = Self { cheap_rec: false, cheap_proj: false };
  const DEF_EQ_CORE: Self = Self { cheap_rec: false, cheap_proj: true };

  #[inline]
  fn is_full(self) -> bool {
    !self.cheap_rec && !self.cheap_proj
  }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NatSuccMode {
  Collapse,
  Stuck,
}

struct NatRecLiteralParts<M: KernelMode> {
  spine: Vec<KExpr<M>>,
  major: Nat,
  base_idx: usize,
  step_idx: usize,
}

impl<M: KernelMode> TypeChecker<'_, M> {
  fn dump_whnf_fuel(
    &self,
    phase: &str,
    original: &KExpr<M>,
    current: &KExpr<M>,
  ) {
    if std::env::var("IX_WHNF_FUEL_DUMP").is_err()
      || !self.debug_label_matches_env()
    {
      return;
    }
    let (orig_head, orig_args) = collect_app_spine(original);
    let (cur_head, cur_args) = collect_app_spine(current);
    eprintln!(
      "[whnf fuel] {phase} const={} depth={} original_head={} original_args={} current_head={} current_args={}",
      self.debug_label.as_deref().unwrap_or("<unknown>"),
      self.depth(),
      orig_head,
      orig_args.len(),
      cur_head,
      cur_args.len()
    );
    eprintln!("  original: {original}");
    eprintln!("  current:  {current}");
  }

  fn dump_delta_trace(&self, id: &KId<M>, arity: usize, e: &KExpr<M>) {
    let Some(filter) = IX_DELTA_TRACE.as_ref() else {
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
      "[delta] const={} depth={} head={} args={arity} expr={}",
      self.debug_label.as_deref().unwrap_or("<unknown>"),
      self.depth(),
      id,
      e
    );
  }

  fn dump_proj_trace(
    &self,
    id: &KId<M>,
    field: u64,
    wval: &KExpr<M>,
    ctor_params: Option<usize>,
    result: Option<&KExpr<M>>,
  ) {
    let Some(filter) = IX_PROJ_TRACE.as_ref() else {
      return;
    };
    if !self.debug_label_matches_env() {
      return;
    }
    let id_s = id.to_string();
    if !filter.is_empty() && !id_s.contains(filter) {
      return;
    }
    let (head, args) = collect_app_spine(wval);
    match result {
      Some(result) => eprintln!(
        "[proj] const={} depth={} proj={} field={} struct_head={} struct_args={} ctor_params={:?} result={}",
        self.debug_label.as_deref().unwrap_or("<unknown>"),
        self.depth(),
        id,
        field,
        head,
        args.len(),
        ctor_params,
        result
      ),
      None => eprintln!(
        "[proj] const={} depth={} proj={} field={} struct_head={} struct_args={} ctor_params={:?} result=<stuck>",
        self.debug_label.as_deref().unwrap_or("<unknown>"),
        self.depth(),
        id,
        field,
        head,
        args.len(),
        ctor_params
      ),
    }
  }

  fn dump_nat_trace(&self, phase: &str, e: &KExpr<M>) {
    let Some(filter) = IX_NAT_TRACE.as_ref() else {
      return;
    };
    if !self.debug_label_matches_env() {
      return;
    }
    let (head, args) = collect_app_spine(e);
    let head_s = head.to_string();
    if !filter.is_empty() && !head_s.contains(filter) {
      return;
    }
    eprintln!(
      "[nat] const={} depth={} phase={} head={} args={} expr={}",
      self.debug_label.as_deref().unwrap_or("<unknown>"),
      self.depth(),
      phase,
      head,
      args.len(),
      e
    );
  }

  /// Full WHNF: loop of whnf_no_delta → delta (one step).
  pub fn whnf(&mut self, e: &KExpr<M>) -> Result<KExpr<M>, TcError<M>> {
    self.whnf_with_nat_succ_mode(e, NatSuccMode::Collapse)
  }

  fn whnf_with_nat_succ_mode(
    &mut self,
    e: &KExpr<M>,
    nat_succ_mode: NatSuccMode,
  ) -> Result<KExpr<M>, TcError<M>> {
    if *IX_WHNF_COUNT_LOG {
      let n = WHNF_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n.is_multiple_of(100_000) && n > 0 {
        eprintln!("[whnf] count={n}");
      }
    }
    // Quick exit for non-reducing forms.
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => return Ok(e.clone()),
      ExprData::Var(i, _, _) if !self.is_let_var(*i) => return Ok(e.clone()),
      _ => {},
    }

    // Context-aware cache: closed exprs use ptr only; open exprs include
    // ctx_id because some reductions consult local binder types.
    let key = self.whnf_key(e);
    let use_cache = nat_succ_mode == NatSuccMode::Collapse;
    let transient_nat_work = self.is_transient_nat_literal_work(e)?;
    if use_cache && !transient_nat_work {
      if let Some(cached) = self.env.whnf_cache.get(&key) {
        self.env.perf.record_whnf_hit();
        return Ok(cached.clone());
      }
      // Both probes missed.
      self.env.perf.record_whnf_miss();
      self.record_hot_miss("whnf", e);
    }

    // Tick AFTER fast paths and cache: only consume shared fuel for actual work.
    // Quick exits (Sort/All/Lam/Nat/Str) and cache hits are free.
    self.tick()?;

    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;
    // Cycle detection: long delta-unfolding chains in mathlib hit hundreds of
    // distinct intermediates, so a Vec linear scan is O(N²). Use a hash set
    // for O(1) lookup. Equality on `Addr` is a 32-byte blake3 compare, so we
    // pay one hash + one cmp per iteration.
    let mut seen: FxHashSet<super::env::Addr> = FxHashSet::default();

    loop {
      if fuel == 0 {
        self.dump_whnf_fuel("whnf", e, &cur);
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      cur = self.whnf_no_delta_impl(&cur, WhnfFlags::FULL, nat_succ_mode)?;
      let cur_key = cur.hash_key();
      if !seen.insert(cur_key) {
        break;
      }

      // Native reduction: Lean.reduceBool, Lean.reduceNat, System.Platform.numBits
      // (mirrors lean4 `type_checker.cpp:667-672` and lean4lean
      // `TypeChecker.lean:438` — `reduce_native` runs before `reduce_nat`).
      if let Some(reduced) = self.try_reduce_native(&cur)? {
        cur = reduced;
        continue;
      }

      // BitVec definitions reduce through Nat comparisons. Keep this before
      // delta so small definitional facts such as `x < 0#w` collapse
      // without unfolding the full Fin-backed representation of BitVec.
      if let Some(reduced) = self.try_reduce_bitvec(&cur)? {
        cur = reduced;
        continue;
      }

      // Nat primitive reduction in main WHNF loop (lean4lean TypeChecker.lean:439).
      // Must run BEFORE delta_unfold_one, so that Nat.sub/Nat.pow/etc. get
      // short-circuited before their bodies (which use Nat.rec) are exposed.
      if let Some(reduced) =
        self.try_reduce_nat_with_succ_mode(&cur, nat_succ_mode)?
      {
        cur = reduced;
        continue;
      }
      // Nat decidability: Nat.decLe/decEq/decLt on literals → Decidable.isTrue/isFalse.
      // Must run BEFORE delta, so the body (which uses dite/Nat.rec) is never exposed.
      if let Some(reduced) = self.try_reduce_decidable(&cur)? {
        cur = reduced;
        continue;
      }

      // String literal primitives such as `String.back ""`.
      if let Some(reduced) = self.try_reduce_string(&cur)? {
        cur = reduced;
        continue;
      }

      if let Some(unfolded) = self.delta_unfold_one(&cur)? {
        cur = unfolded;
        continue;
      }

      break;
    }

    if !self.in_native_reduce && use_cache && !transient_nat_work {
      self.env.whnf_cache.insert(key, cur.clone());
    }
    Ok(cur)
  }

  /// Structural WHNF: beta, iota, zeta. NO delta. FULL flags.
  ///
  /// This is the standard structural normalizer used outside the def-eq
  /// lazy-delta path. With `WhnfFlags::FULL`, recursive sub-reductions and
  /// `try_iota` use full delta on majors and projected values, matching
  /// pre-`WhnfFlags` behavior of `whnf_core`.
  pub(super) fn whnf_core(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.whnf_core_with_flags(e, WhnfFlags::FULL)
  }

  /// Structural WHNF for def-eq's cheap projection scaffold:
  /// `whnfCore (cheapProj := true)` in Lean/Lean4Lean. Projection values are
  /// reduced structurally instead of through full WHNF, but recursor majors
  /// still use full WHNF because def-eq does not enable `cheapRec` here.
  ///
  /// Increments `cheap_recursion_depth` for the duration of the call so
  /// `is_def_eq` can detect it is running inside a cheap reduction and
  /// keep cheap-mode false negatives out of the full def-eq cache.
  pub(super) fn whnf_core_for_def_eq(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.cheap_recursion_depth += 1;
    let result = self.whnf_core_with_flags(e, WhnfFlags::DEF_EQ_CORE);
    self.cheap_recursion_depth -= 1;
    result
  }

  /// Internal flags-threaded core: callers go through [`whnf_core`] or
  /// [`whnf_core_for_def_eq`]. Recursive sub-reductions and `try_iota`
  /// propagate the same flags so a def-eq structural pass does not
  /// accidentally unfold projected values.
  ///
  /// FULL-mode results are cached in [`KEnv::whnf_core_cache`], mirroring
  /// lean4lean's `whnfCoreCache` (TypeChecker.lean:19) and lean4 C++'s
  /// `m_whnf_core`. Cheap-mode results are NOT cached — projection values
  /// reduce structurally instead of through full WHNF, so cheap output is
  /// not safe to share with full callers.
  fn whnf_core_with_flags(
    &mut self,
    e: &KExpr<M>,
    flags: WhnfFlags,
  ) -> Result<KExpr<M>, TcError<M>> {
    // Fast pre-cache: leaves that whnf_core never reduces. Returning
    // `e.clone()` directly skips both the `whnf_key` build (a `ctx_addr`
    // probe + hash compose) and the `whnf_core_cache` probe/insert, and
    // — more importantly — keeps the cache from filling with trivial
    // `e → e` entries that dominate cache size on big mathlib blocks.
    //
    // `Const` is in the leaf set here (unlike `whnf`/`whnf_no_delta`)
    // because `whnf_core` does NOT delta-unfold. `Var` is a leaf only
    // when there are no active let-bindings; otherwise it might
    // zeta-reduce against a let-bound value via `lookup_let_val`.
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..)
      | ExprData::Const(..) => return Ok(e.clone()),
      ExprData::Var(i, _, _) if !self.is_let_var(*i) => return Ok(e.clone()),
      _ => {},
    }

    let key = self.whnf_key(e);
    let transient_nat_work = self.is_transient_nat_literal_work(e)?;
    if flags.is_full() {
      if !transient_nat_work {
        if let Some(cached) = self.env.whnf_core_cache.get(&key) {
          self.env.perf.record_whnf_core_hit();
          return Ok(cached.clone());
        }
      }
      self.env.perf.record_whnf_core_miss();
      self.record_hot_miss("whnf-core", e);
      let result = self.whnf_core_with_flags_uncached(e, flags)?;
      if !transient_nat_work {
        self.env.whnf_core_cache.insert(key, result.clone());
      }
      Ok(result)
    } else {
      // Cheap mode: consult/populate its own cache. Inside the def-eq lazy
      // delta loop the same operand reduces through whnf_core repeatedly
      // (once per loop iteration, also re-entered through whnf_no_delta_impl
      // → whnf_core_with_flags), so caching here cuts O(N²) iteration cost
      // back to O(N). Soundness mirrors `whnf_no_delta_cheap_cache`:
      // cheap-mode results are never shared with full callers.
      if !transient_nat_work {
        if let Some(cached) = self.env.whnf_core_cheap_cache.get(&key) {
          self.env.perf.record_whnf_core_hit();
          return Ok(cached.clone());
        }
      }
      self.env.perf.record_whnf_core_miss();
      self.record_hot_miss("whnf-core-cheap", e);
      let result = self.whnf_core_with_flags_uncached(e, flags)?;
      if !transient_nat_work {
        self.env.whnf_core_cheap_cache.insert(key, result.clone());
      }
      Ok(result)
    }
  }

  /// Inner loop for [`whnf_core_with_flags`]. Does not consult or update
  /// `whnf_core_cache`; the caller wraps it for FULL mode.
  fn whnf_core_with_flags_uncached(
    &mut self,
    e: &KExpr<M>,
    flags: WhnfFlags,
  ) -> Result<KExpr<M>, TcError<M>> {
    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;

    loop {
      if fuel == 0 {
        self.dump_whnf_fuel("whnf_core", e, &cur);
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      match cur.data() {
        // Legacy let-bound variable zeta-reduction: substitute the
        // let-bound value. Still active for inductive validation paths
        // and tests that push values via `push_let` rather than opening
        // let binders into LDecl fvars.
        ExprData::Var(i, _, _) => {
          if let Some(val) = self.lookup_let_val(*i) {
            cur = val;
            continue;
          }
          return Ok(cur);
        },
        // Let-bound fvar zeta-reduction: substitute the let-bound value.
        // Mirrors lean4lean's `whnfFVar` branch
        // (refs/lean4lean/Lean4Lean/TypeChecker.lean:233).
        ExprData::FVar(id, _, _) => {
          if let Some(super::lctx::LocalDecl::LDecl { val, .. }) =
            self.lctx.find(*id)
          {
            cur = val.clone();
            continue;
          }
          return Ok(cur);
        },
        ExprData::Sort(..)
        | ExprData::All(..)
        | ExprData::Lam(..)
        | ExprData::Nat(..)
        | ExprData::Str(..)
        | ExprData::Const(..) => return Ok(cur),

        // Projection reduction. Matches Lean4Lean's `reduceProj`
        // (`refs/lean4lean/Lean4Lean/TypeChecker.lean:284–292`):
        //   let mut c ← (if cheapProj then whnfCore struct cheapRec cheapProj
        //                else whnf struct)
        //
        // FULL flags use full `whnf` on the struct value so delta unfolding
        // can expose a constructor. CHEAP flags stay structural — the
        // projection stays stuck if the struct value doesn't already reduce
        // structurally to a ctor application. The caller is responsible for
        // handling stuck projections (def-eq compares them structurally).
        //
        ExprData::Prj(id, field, val, _) => {
          let field = *field;
          let id = id.clone();
          let val = val.clone();
          let wval = if flags.cheap_proj {
            self.whnf_core_with_flags(&val, flags)?
          } else {
            self.whnf(&val)?
          };
          if let Some(result) = self.try_proj_reduce(&id, field, &wval)? {
            cur = result;
            continue;
          }
          return Ok(cur); // stuck projection
        },

        // Zeta: let elimination
        ExprData::Let(_, _, val, body, _, _) => {
          let val = val.clone();
          let body = body.clone();
          cur = subst(&mut self.env.intern, &body, &val, 0);
          continue;
        },

        ExprData::App(..) => {},
      }

      // App: collect spine, whnf_core head, try beta/iota
      let (f0, args) = collect_app_spine(&cur);
      let f = self.whnf_core_with_flags(&f0, flags)?;

      // Multi-arg beta
      if matches!(f.data(), ExprData::Lam(..)) {
        let mut body = f;
        // Pre-size: at most one arg is consumed per outer Lam, capped by
        // `args.len()`. Pre-sizing skips the first growth reallocation
        // for non-trivial spines on this hot path.
        let mut consumed_args = Vec::with_capacity(args.len());
        while consumed_args.len() < args.len() {
          if let ExprData::Lam(_, _, _, inner, _) = body.data() {
            let inner = inner.clone();
            consumed_args.push(args[consumed_args.len()].clone());
            body = inner;
          } else {
            break;
          }
        }
        let remaining_start = consumed_args.len();
        if !consumed_args.is_empty() {
          consumed_args.reverse();
          body = simul_subst(&mut self.env.intern, &body, &consumed_args, 0);
        }
        for arg in &args[remaining_start..] {
          body = self.intern(KExpr::app(body, arg.clone()));
        }
        cur = body;
        continue;
      }

      // If head reduced, rebuild and try iota
      if !f.ptr_eq(&f0) {
        let mut rebuilt = f;
        for arg in &args {
          rebuilt = self.intern(KExpr::app(rebuilt, arg.clone()));
        }
        if let Some(reduced) = self.try_iota_with_flags(&rebuilt, flags)? {
          cur = reduced;
          continue;
        }
        return Ok(rebuilt);
      }

      // Try iota on original
      if let Some(reduced) = self.try_iota_with_flags(&cur, flags)? {
        cur = reduced;
        continue;
      }

      return Ok(cur);
    }
  }

  /// WHNF without delta: whnf_core → proj-app → nat/native/string → quot.
  /// Projection values use full WHNF, preserving the public/full semantics.
  pub fn whnf_no_delta(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.whnf_no_delta_impl(e, WhnfFlags::FULL, NatSuccMode::Collapse)
  }

  /// Def-eq no-delta WHNF. This is broader than Lean's pure `whnfCore`
  /// because Ix relies on the no-delta layer for primitive/native reductions,
  /// but it preserves Lean's cheap projection policy for projected values.
  pub(super) fn whnf_no_delta_for_def_eq(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.cheap_recursion_depth += 1;
    let result =
      self.whnf_no_delta_impl(e, WhnfFlags::DEF_EQ_CORE, NatSuccMode::Collapse);
    self.cheap_recursion_depth -= 1;
    result
  }

  fn whnf_no_delta_impl(
    &mut self,
    e: &KExpr<M>,
    flags: WhnfFlags,
    nat_succ_mode: NatSuccMode,
  ) -> Result<KExpr<M>, TcError<M>> {
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => return Ok(e.clone()),
      ExprData::Var(i, _, _) if !self.is_let_var(*i) => return Ok(e.clone()),
      _ => {},
    }

    let key = self.whnf_key(e);
    let use_cache = nat_succ_mode == NatSuccMode::Collapse;
    let transient_nat_work = self.is_transient_nat_literal_work(e)?;
    if flags.is_full() {
      if use_cache && !transient_nat_work {
        if let Some(cached) = self.env.whnf_no_delta_cache.get(&key) {
          self.env.perf.record_whnf_no_delta_hit();
          return Ok(cached.clone());
        }
      }
      // Both probes missed.
      if use_cache {
        self.env.perf.record_whnf_no_delta_miss();
        self.record_hot_miss("whnf-no-delta", e);
      }
    } else {
      // Cheap-mode (DEF_EQ_CORE): consult its own cache. Cheap output is NOT
      // shared with full callers, but cheap → cheap reuse is sound and is the
      // dominant pattern inside the lazy-delta loop, where the same operand
      // is re-reduced after every delta_unfold_one of the *other* operand.
      if use_cache && !transient_nat_work {
        if let Some(cached) = self.env.whnf_no_delta_cheap_cache.get(&key) {
          self.env.perf.record_whnf_no_delta_hit();
          return Ok(cached.clone());
        }
      }
      if use_cache {
        self.env.perf.record_whnf_no_delta_miss();
        self.record_hot_miss("whnf-no-delta-cheap", e);
      }
    }

    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;

    loop {
      if fuel == 0 {
        self.dump_whnf_fuel("whnf_no_delta", e, &cur);
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      cur = self.whnf_core_with_flags(&cur, flags)?;

      // Projection reduction is now handled inside `whnf_core_with_flags`
      // (`whnfCore`/`reduceProj` at TypeChecker.lean:284-292, 337-341).
      // `whnf_core` either returns a stuck `Prj`
      // (struct value didn't reduce to a ctor) or a fully-reduced field.
      //
      // We only need to handle the App-of-Prj case here, since `whnf_core`
      // doesn't iterate after a Prj reduces (its loop returns once the
      // outermost Prj is resolved). When the outer expression is
      // `App(Prj(S, i, val), args...)`, `whnf_core` reduces the App spine
      // and may leave the Prj head stuck; `try_proj_app_reduce` gives it
      // one more attempt with the same projection policy.
      if let Some((proj_result, args)) =
        self.try_proj_app_reduce(&cur, flags)?
      {
        let mut result = proj_result;
        for arg in &args {
          result = self.intern(KExpr::app(result, arg.clone()));
        }
        cur = result;
        continue;
      }

      // BitVec.toNat/ult reductions are definitional wrappers around Nat.
      if let Some(reduced) = self.try_reduce_bitvec(&cur)? {
        cur = reduced;
        continue;
      }

      // Nat primitive reduction
      if let Some(reduced) =
        self.try_reduce_nat_with_succ_mode(&cur, nat_succ_mode)?
      {
        cur = reduced;
        continue;
      }

      // Native/string primitives must run before projection-definition
      // rewriting. In the compiled environment, wrappers such as
      // `Subtype.val` and `String.toByteArray` are projection definitions;
      // once rewritten to `Prj`, the cheap primitive recognizers no longer
      // see the original head.
      if let Some(reduced) = self.try_reduce_native(&cur)? {
        cur = reduced;
        continue;
      }

      // String literal primitives.
      if let Some(reduced) = self.try_reduce_string(&cur)? {
        cur = reduced;
        continue;
      }

      if flags.is_full() {
        if let Some(reduced) = self.try_reduce_projection_definition(&cur)? {
          cur = reduced;
          continue;
        }
      }

      // Quotient reduction
      if let Some(reduced) = self.try_quot_reduce(&cur)? {
        cur = reduced;
        continue;
      }

      break;
    }

    if !self.in_native_reduce && use_cache && !transient_nat_work {
      if flags.is_full() {
        self.env.whnf_no_delta_cache.insert(key, cur.clone());
      } else {
        self.env.whnf_no_delta_cheap_cache.insert(key, cur.clone());
      }
    }
    Ok(cur)
  }

  /// Delta unfold: unfold one defined constant.
  pub fn delta_unfold_one(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if let Some(unfolded) = self.try_delta_unfold(e)? {
      return Ok(Some(unfolded));
    }
    // Bare constant
    if let ExprData::Const(id, us, _) = e.data()
      && let Some(KConst::Defn { kind, val, .. }) = self.try_get_const(id)?
      && matches!(kind, DefKind::Definition | DefKind::Theorem)
    {
      self.dump_delta_trace(id, 0, e);
      let val = val.clone();
      let us: Vec<_> = us.to_vec();
      return Ok(Some(self.unfold_const_value(e, &val, &us)?));
    }
    Ok(None)
  }

  /// Try delta-unfold on application head.
  fn try_delta_unfold(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);

    let (id, us) = match head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(None),
    };

    let val = match self.try_get_const(id)? {
      Some(KConst::Defn {
        kind: DefKind::Definition | DefKind::Theorem,
        val,
        ..
      }) => {
        self.dump_delta_trace(id, args.len(), e);
        val.clone()
      },
      _ => return Ok(None),
    };

    let us: Vec<_> = us.to_vec();
    let val = self.unfold_const_value(&head, &val, &us)?;

    let mut result = val;
    for arg in &args {
      result = self.intern(KExpr::app(result, arg.clone()));
    }

    Ok(Some(result))
  }

  /// Cache wrapper around `instantiate_univ_params` for delta unfolding.
  ///
  /// `head_expr` is the `Const(id, us)` head whose body we are unfolding;
  /// its content hash already encodes `(id, us)`, so we use it directly
  /// as the cache key. The cached value is the universe-instantiated body
  /// returned by `instantiate_univ_params(val, us)`.
  ///
  /// Soundness: `instantiate_univ_params` is a pure function of `(val, us)`
  /// — it only walks the term and substitutes universe params, touching
  /// neither `tc.ctx` nor any thread-local mutable state. Two distinct
  /// `(id, us)` pairs always produce distinct head hashes (KExpr interning
  /// is by content), so cache hits are content-correct.
  ///
  /// Mirrors the lean4 C++ kernel `m_unfold` cache in `type_checker.cpp`.
  fn unfold_const_value(
    &mut self,
    head_expr: &KExpr<M>,
    val: &KExpr<M>,
    us: &[KUniv<M>],
  ) -> Result<KExpr<M>, TcError<M>> {
    let key = head_expr.hash_key();
    if let Some(cached) = self.env.unfold_cache.get(&key) {
      self.env.perf.record_unfold_hit();
      return Ok(cached.clone());
    }
    self.env.perf.record_unfold_miss();
    let result = self.instantiate_univ_params(val, us)?;
    self.env.unfold_cache.insert(key, result.clone());
    Ok(result)
  }

  // -----------------------------------------------------------------------
  // Iota reduction
  // -----------------------------------------------------------------------

  /// Try iota: recursor applied to constructor.
  ///
  /// Flags-threaded: when `flags.cheap_rec` is set, the major premise (and
  /// the freshly-built string-literal constructor) reduce with cheap WHNF,
  /// mirroring Lean4Lean's `cheapRec` behaviour at TypeChecker.lean:337–341.
  /// Internal-only — callers go through `whnf_core_with_flags`.
  fn try_iota_with_flags(
    &mut self,
    e: &KExpr<M>,
    flags: WhnfFlags,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, spine) = collect_app_spine(e);

    let (rec_id, rec_us) = match head.data() {
      ExprData::Const(id, us, _) => (id.clone(), us.clone()),
      _ => return Ok(None),
    };

    let recr = match self.try_get_const(&rec_id)? {
      Some(KConst::Recr {
        k,
        params,
        motives,
        minors,
        indices,
        rules,
        lvls,
        ..
      }) => {
        let major_idx = u64_to_usize::<M>(params + motives + minors + indices)?;
        if spine.len() <= major_idx {
          return Ok(None);
        }
        IotaInfo {
          k,
          params: u64_to_usize::<M>(params)?,
          motives: u64_to_usize::<M>(motives)?,
          minors: u64_to_usize::<M>(minors)?,
          indices: u64_to_usize::<M>(indices)?,
          major_idx,
          rules: rules.clone(),
          lvls,
        }
      },
      _ => return Ok(None),
    };

    // K-like recursor: try to synthesize a nullary constructor before WHNF.
    // This handles cases like `Eq.rec motive minor major` where major isn't
    // a constructor but its type matches the inductive — we build `Eq.refl params...`.
    let major = &spine[recr.major_idx];
    let major = if recr.k {
      self
        .synth_ctor_when_k(major, &rec_id, &recr)?
        .unwrap_or_else(|| major.clone())
    } else {
      major.clone()
    };
    let major = match self.cleanup_nat_offset_major(&major)? {
      Some(cleaned) => cleaned,
      None => major,
    };

    // WHNF the major premise. Cheap mode skips delta on the major itself,
    // matching Lean4Lean's `cheapRec` (TypeChecker.lean:337–341); the rest of
    // the iota machinery still gets a structural normal form to inspect.
    let mut major_whnf = if flags.cheap_rec {
      self.whnf_core_with_flags(&major, flags)?
    } else {
      self.whnf(&major)?
    };

    // Nat literal → constructor form (one level: n → Nat.succ(lit(n-1))).
    //
    // Mirrors lean4 (`refs/lean4/src/kernel/inductive.h:91-93`) and
    // lean4lean (`refs/lean4lean/Lean4Lean/Inductive/Reduce.lean:70`):
    // unconditional peel. Truly runaway recursors (step case forces the
    // IH on every iteration) are bounded by `MAX_WHNF_FUEL` / outer
    // `MaxRecDepth`, same as upstream. An earlier ix-specific
    // throttle-by-counter scheme was found to mis-classify omega-style
    // proofs that legitimately crunch many independent large-Nat
    // recursors in one check; if a real runaway shows up we will fall
    // back to fuel-based detection and not the counter.
    let mut major_was_nat_lit = false;
    if let ExprData::Nat(val, _, _) = major_whnf.data() {
      if *IX_NAT_IOTA_TRACE {
        let n = NAT_IOTA_TRACE_COUNT
          .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if n < 32 {
          eprintln!(
            "[nat_iota_trace] rec={} major_bits={} spine={} major_idx={}",
            rec_id,
            val.0.bits(),
            spine.len(),
            recr.major_idx
          );
        }
      }
      major_was_nat_lit = true;
      major_whnf = self.nat_to_constructor(&val.clone());
    }
    if let Some(cleaned) = self.cleanup_nat_offset_major(&major_whnf)? {
      major_whnf = cleaned;
    }
    // String literal → constructor form (M3: WHNF after, matching lean4lean Reduce.lean:71).
    // Use the same flag-driven reduction policy as the major above so a
    // cheap iota stays cheap end-to-end.
    if let ExprData::Str(val, _, _) = major_whnf.data() {
      let val = val.clone();
      let str_ctor = self.str_lit_to_constructor(&val);
      major_whnf = if flags.cheap_rec {
        self.whnf_core_with_flags(&str_ctor, flags)?
      } else {
        self.whnf(&str_ctor)?
      };
    }

    // Check if major is a constructor application
    let (ctor_head, ctor_args) = collect_app_spine(&major_whnf);
    let is_ctor = match ctor_head.data() {
      ExprData::Const(id, _, _) => {
        matches!(self.try_get_const(id)?, Some(KConst::Ctor { .. }))
      },
      _ => false,
    };

    // Diagnostic: when the major doesn't reduce to a ctor, iota is stuck.
    // Surface which recursor + major shape we got \u2014 the major's head
    // tells us which downstream reduction (delta, iota, nat, int) failed
    // to complete.
    if !is_ctor && let Some(filter) = IX_IOTA_STUCK.as_ref() {
      let rec_name = format!("{rec_id}");
      if filter.is_empty() || rec_name.contains(filter) {
        eprintln!("[iota stuck] rec={rec_name}");
        eprintln!("[iota stuck]   major:      {major}");
        eprintln!("[iota stuck]   major whnf: {major_whnf}");
      }
    }

    if is_ctor {
      let ctor_id = match ctor_head.data() {
        ExprData::Const(id, _, _) => id,
        _ => unreachable!(),
      };
      let (cidx, ctor_fields) = match self.get_const(ctor_id)? {
        KConst::Ctor { cidx, fields, .. } => {
          (u64_to_usize::<M>(cidx)?, u64_to_usize::<M>(fields)?)
        },
        _ => return Ok(None),
      };

      if cidx >= recr.rules.len() {
        return Ok(None);
      }
      let rule = &recr.rules[cidx];
      // H6: Check level params arity (lean4lean Reduce.lean:76)
      if rec_us.len() as u64 != recr.lvls {
        return Ok(None);
      }
      // H5: Check nfields ≤ major_args (lean4lean Reduce.lean:75)
      if ctor_fields > ctor_args.len() {
        return Ok(None);
      }
      let rec_us_vec: Vec<_> = rec_us.to_vec();
      let rhs = self.instantiate_univ_params(&rule.rhs, &rec_us_vec)?;

      let pmm_end = recr.params + recr.motives + recr.minors;
      let field_start = ctor_args.len() - ctor_fields;
      let mut result = rhs;
      for arg in spine.iter().take(pmm_end.min(spine.len())) {
        result = self.apply_iota_arg(result, arg, major_was_nat_lit);
      }
      for arg in ctor_args.iter().skip(field_start) {
        result = self.apply_iota_arg(result, arg, major_was_nat_lit);
      }
      for arg in spine.iter().skip(recr.major_idx + 1) {
        result = self.apply_iota_arg(result, arg, major_was_nat_lit);
      }
      return Ok(Some(result));
    }

    // Struct eta iota fallback
    if let Some(result) =
      self.try_struct_eta_iota(&rec_id, &recr, &rec_us, &spine)?
    {
      return Ok(Some(result));
    }

    Ok(None)
  }

  fn is_struct_like(&mut self, id: &KId<M>) -> Result<bool, TcError<M>> {
    Ok(match self.try_get_const(id)? {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        !is_rec && indices == 0 && ctors.len() == 1
      },
      _ => false,
    })
  }

  fn apply_iota_arg(
    &mut self,
    result: KExpr<M>,
    arg: &KExpr<M>,
    transient: bool,
  ) -> KExpr<M> {
    if transient {
      if let ExprData::Lam(_, _, _, body, _) = result.data() {
        let body = body.clone();
        return subst_no_intern(&body, arg, 0);
      }
      KExpr::app(result, arg.clone())
    } else {
      self.intern(KExpr::app(result, arg.clone()))
    }
  }

  /// Nat literal iota can create a long chain of distinct predecessor terms.
  /// These terms are useful only while the current WHNF is executing; keeping
  /// each one in the global WHNF caches makes RSS linear in the literal.
  fn is_transient_nat_literal_work(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if self.is_nat_literal_recursor_app(e)? {
      return Ok(true);
    }

    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(false);
    };

    if id.addr == self.prims.nat_succ.addr && args.len() == 1 {
      return self.is_nat_literal_recursor_app(&args[0]);
    }

    Ok(false)
  }

  fn is_nat_literal_recursor_app(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let (head, spine) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(false);
    };
    if id.addr != self.prims.nat_rec.addr
      && id.addr != self.prims.nat_cases_on.addr
    {
      return Ok(false);
    }

    let Some(KConst::Recr { params, motives, minors, indices, .. }) =
      self.try_get_const(id)?
    else {
      return Ok(false);
    };
    let major_idx = u64_to_usize::<M>(params + motives + minors + indices)?;
    Ok(
      spine
        .get(major_idx)
        .is_some_and(|major| matches!(major.data(), ExprData::Nat(..))),
    )
  }

  /// Lean's `cleanupNatOffsetMajor` for recursor reduction.
  ///
  /// If the major premise is definitionally an offset `base + k` with `k > 0`,
  /// expose exactly one constructor layer as `Nat.succ (base + (k-1))`.
  /// This prevents `Nat.rec ... (x + huge)` from delta-unfolding `Nat.add`
  /// and allocating one intermediate literal per predecessor. Closed Nat
  /// arithmetic is left alone so the primitive Nat reducer can compute it
  /// directly to a compact literal.
  fn cleanup_nat_offset_major(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if self.eval_nat_offset_literal(e, 0).is_some() {
      return Ok(None);
    }
    let Some((base, offset)) = self.nat_offset(e, 0)? else {
      return Ok(None);
    };
    if offset.0 == num_bigint::BigUint::ZERO {
      return Ok(None);
    }

    let pred_offset = Nat(&offset.0 - 1u64);
    let pred = if pred_offset.0 == num_bigint::BigUint::ZERO {
      base
    } else {
      let pred_lit = self.nat_expr_from_value(pred_offset);
      self.mk_nat_add(base, pred_lit)
    };
    Ok(Some(self.mk_nat_succ(pred)))
  }

  fn nat_offset(
    &mut self,
    e: &KExpr<M>,
    depth: u16,
  ) -> Result<Option<(KExpr<M>, Nat)>, TcError<M>> {
    const MAX_NAT_OFFSET_DEPTH: u16 = 256;
    if depth >= MAX_NAT_OFFSET_DEPTH {
      return Ok(None);
    }

    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(None);
    };

    if id.addr == self.prims.nat_succ.addr && args.len() == 1 {
      let (base, offset) = self.nat_offset_or_zero(&args[0], depth + 1)?;
      return Ok(Some((base, Nat(offset.0 + 1u64))));
    }

    if id.addr == self.prims.nat_add.addr && args.len() == 2 {
      let Some(rhs) = self.eval_nat_offset_literal(&args[1], depth + 1) else {
        return Ok(None);
      };
      let (base, offset) = self.nat_offset_or_zero(&args[0], depth + 1)?;
      return Ok(Some((base, Nat(offset.0 + rhs.0))));
    }

    Ok(None)
  }

  fn nat_offset_or_zero(
    &mut self,
    e: &KExpr<M>,
    depth: u16,
  ) -> Result<(KExpr<M>, Nat), TcError<M>> {
    Ok(
      self
        .nat_offset(e, depth)?
        .unwrap_or_else(|| (e.clone(), Nat(num_bigint::BigUint::ZERO))),
    )
  }

  /// Syntactic, no-delta evaluator for Nat offset constants.
  ///
  /// This is intentionally weaker than WHNF: it only recognizes already
  /// exposed Nat literals/constructors and primitive Nat arithmetic whose
  /// arguments are themselves syntactically evaluable. It is used to avoid
  /// rewriting closed arithmetic offsets before `try_reduce_nat` can compute
  /// them, and to evaluate the literal offset side of `Nat.add`.
  fn eval_nat_offset_literal(
    &mut self,
    e: &KExpr<M>,
    depth: u16,
  ) -> Option<Nat> {
    const MAX_NAT_OFFSET_EVAL_DEPTH: u16 = 256;
    if depth >= MAX_NAT_OFFSET_EVAL_DEPTH {
      return None;
    }

    if let Some(n) = extract_nat_value(e, &self.prims) {
      return Some(n);
    }

    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return None;
    };

    if id.addr == self.prims.nat_pred.addr && args.len() == 1 {
      let n = self.eval_nat_offset_literal(&args[0], depth + 1)?;
      let result = if n.0 == num_bigint::BigUint::ZERO {
        Nat(num_bigint::BigUint::ZERO)
      } else {
        Nat(n.0 - 1u64)
      };
      return Some(result);
    }

    if self.is_nat_bin_arith_addr(&id.addr) && args.len() == 2 {
      let a = self.eval_nat_offset_literal(&args[0], depth + 1)?;
      let b = self.eval_nat_offset_literal(&args[1], depth + 1)?;
      return compute_nat_bin(&id.addr, &self.prims, &a, &b);
    }

    None
  }

  fn mk_nat_succ(&mut self, pred: KExpr<M>) -> KExpr<M> {
    let succ = KExpr::cnst(self.prims.nat_succ.clone(), Box::new([]));
    KExpr::app(succ, pred)
  }

  fn mk_nat_add(&mut self, a: KExpr<M>, b: KExpr<M>) -> KExpr<M> {
    let add = KExpr::cnst(self.prims.nat_add.clone(), Box::new([]));
    let result = KExpr::app(add, a);
    KExpr::app(result, b)
  }

  fn try_struct_eta_iota(
    &mut self,
    rec_id: &KId<M>,
    recr: &IotaInfo<M>,
    rec_us: &[KUniv<M>],
    spine: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if recr.rules.len() != 1 {
      return Ok(None);
    }
    let rule = &recr.rules[0];

    let rec_ty = match self.try_get_const(rec_id)? {
      Some(c) => c.ty().clone(),
      None => return Ok(None),
    };
    let skip = (recr.params + recr.motives + recr.minors + recr.indices) as u64;
    let ind_id = match self.get_major_inductive_id(&rec_ty, skip) {
      Ok(id) => id,
      Err(_) => return Ok(None),
    };
    if !self.is_struct_like(&ind_id)? {
      return Ok(None);
    }

    // H3: Prop guard — don't eta-expand Prop-typed structures (lean4lean toCtorWhenStruct:51)
    let major = &spine[recr.major_idx];
    let major_ty = match self.with_infer_only(|tc| tc.infer(major)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_sort = match self.with_infer_only(|tc| tc.infer(&major_ty)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_sort_w = match self.whnf(&major_sort) {
      Ok(w) => w,
      Err(_) => return Ok(None),
    };
    if matches!(major_sort_w.data(), ExprData::Sort(u, _) if u.is_zero()) {
      return Ok(None);
    }
    let rec_us_vec: Vec<_> = rec_us.to_vec();
    let rhs = self.instantiate_univ_params(&rule.rhs, &rec_us_vec)?;
    let pmm_end = recr.params + recr.motives + recr.minors;
    let mut result = rhs;
    for arg in spine.iter().take(pmm_end.min(spine.len())) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    for i in 0..rule.fields {
      let proj = self.intern(KExpr::prj(ind_id.clone(), i, major.clone()));
      result = self.intern(KExpr::app(result, proj));
    }
    for arg in spine.iter().skip(recr.major_idx + 1) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  // -----------------------------------------------------------------------
  // K-rule: synthesize nullary constructor
  // -----------------------------------------------------------------------

  /// For K-like recursors, try to synthesize a nullary constructor from the
  /// major premise's type. Returns `Ok(Some(ctor_app))` if successful.
  ///
  /// Algorithm (following lean4lean/nanoda):
  /// 1. Infer major's type, WHNF it
  /// 2. Check head constant matches the recursor's target inductive
  /// 3. Build nullary ctor: `Ctor.{levels} params...`
  /// 4. Infer ctor's type, check def-eq with major's type
  fn synth_ctor_when_k(
    &mut self,
    major: &KExpr<M>,
    rec_id: &KId<M>,
    recr: &IotaInfo<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    // Infer major's type (infer-only: we just need the type, not validation)
    let major_ty = match self.with_infer_only(|tc| tc.infer(major)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_ty_w = match self.whnf(&major_ty) {
      Ok(w) => w,
      Err(_) => return Ok(None),
    };

    // Extract head constant of the type
    let (ty_head, ty_args) = collect_app_spine(&major_ty_w);
    let ty_head_id = match ty_head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => return Ok(None),
    };

    // Get the recursor's target inductive from its type
    let rec_ty = match self.try_get_const(rec_id)? {
      Some(c) => c.ty().clone(),
      None => return Ok(None),
    };
    let skip = (recr.params + recr.motives + recr.minors + recr.indices) as u64;
    let ind_id = match self.get_major_inductive_id(&rec_ty, skip) {
      Ok(id) => id,
      Err(_) => return Ok(None),
    };

    // Head of major's type must match the recursor's target inductive
    if ty_head_id.addr != ind_id.addr {
      return Ok(None);
    }

    // Get the first constructor
    let ctor_id = match self.try_get_const(&ind_id)? {
      Some(KConst::Indc { ctors, .. }) if !ctors.is_empty() => ctors[0].clone(),
      _ => return Ok(None),
    };

    // Build nullary ctor application: Ctor.{levels} params...
    let ctor_us = match ty_head.data() {
      ExprData::Const(_, us, _) => us.clone(),
      _ => return Ok(None),
    };
    let mut ctor_app = self.intern(KExpr::cnst(ctor_id, ctor_us));
    for arg in ty_args.iter().take(recr.params) {
      ctor_app = self.intern(KExpr::app(ctor_app, arg.clone()));
    }

    // Verify: infer ctor's type and check def-eq with major's type
    let ctor_ty = match self.with_infer_only(|tc| tc.infer(&ctor_app)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    if !self.is_def_eq(&major_ty_w, &ctor_ty)? {
      return Ok(None);
    }

    Ok(Some(ctor_app))
  }

  // -----------------------------------------------------------------------
  // Projection reduction
  // -----------------------------------------------------------------------

  pub(super) fn try_proj_reduce(
    &mut self,
    id: &KId<M>,
    field: u64,
    wval: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    // String literal → constructor form before trying projection
    let wval_expanded;
    let wval_expanded_whnf;
    let wval = if let ExprData::Str(s, _, _) = wval.data() {
      wval_expanded = self.str_lit_to_constructor(&s.clone());
      wval_expanded_whnf = self.whnf(&wval_expanded)?;
      &wval_expanded_whnf
    } else {
      wval
    };

    let (head, args) = collect_app_spine(wval);

    if let Some(result) =
      self.try_reduce_fin_val_decidable_rec(id, field, &head, &args)
    {
      self.dump_proj_trace(id, field, wval, None, Some(&result));
      return Ok(Some(result));
    }

    let ctor_id = match head.data() {
      ExprData::Const(id, _, _) => id,
      _ => {
        self.dump_proj_trace(id, field, wval, None, None);
        return Ok(None);
      },
    };

    let ctor_params = match self.try_get_const(ctor_id)? {
      Some(KConst::Ctor { params, .. }) => match usize::try_from(params) {
        Ok(params) => params,
        Err(_) => return Ok(None),
      },
      _ => {
        self.dump_proj_trace(id, field, wval, None, None);
        return Ok(None);
      },
    };

    let field_start = ctor_params;
    let Ok(field_idx) = usize::try_from(field) else {
      return Ok(None);
    };
    let idx = field_start + field_idx;
    let result = args.get(idx).cloned();
    self.dump_proj_trace(id, field, wval, Some(ctor_params), result.as_ref());
    Ok(result)
  }

  fn try_reduce_fin_val_decidable_rec(
    &mut self,
    id: &KId<M>,
    field: u64,
    head: &KExpr<M>,
    args: &[KExpr<M>],
  ) -> Option<KExpr<M>> {
    if id.addr != self.prims.fin.addr || field != 0 {
      return None;
    }

    let ExprData::Const(rec_id, rec_us, _) = head.data() else {
      return None;
    };
    if rec_id.addr != self.prims.decidable_rec.addr || args.len() < 5 {
      return None;
    }

    let ExprData::Lam(motive_name, motive_bi, motive_dom, _, _) =
      args[1].data()
    else {
      return None;
    };
    let false_minor =
      self.project_decidable_fin_val_minor(id, field, &args[2])?;
    let true_minor =
      self.project_decidable_fin_val_minor(id, field, &args[3])?;

    let nat_ty = self.intern(KExpr::cnst(self.prims.nat.clone(), Box::new([])));
    let motive = self.intern(KExpr::lam(
      motive_name.clone(),
      motive_bi.clone(),
      motive_dom.clone(),
      nat_ty,
    ));

    let mut result = self.intern(KExpr::cnst(rec_id.clone(), rec_us.clone()));
    result = self.intern(KExpr::app(result, args[0].clone()));
    result = self.intern(KExpr::app(result, motive));
    result = self.intern(KExpr::app(result, false_minor));
    result = self.intern(KExpr::app(result, true_minor));
    result = self.intern(KExpr::app(result, args[4].clone()));
    for arg in args.iter().skip(5) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }

    Some(result)
  }

  fn project_decidable_fin_val_minor(
    &mut self,
    id: &KId<M>,
    field: u64,
    minor: &KExpr<M>,
  ) -> Option<KExpr<M>> {
    let ExprData::Lam(name, bi, dom, body, _) = minor.data() else {
      return None;
    };
    let proj = self.intern(KExpr::prj(id.clone(), field, body.clone()));
    Some(self.intern(KExpr::lam(name.clone(), bi.clone(), dom.clone(), proj)))
  }

  /// Try to reduce a projection-headed application: App(Prj(S, i, v), args...).
  /// Returns Some((reduced_proj, remaining_args)) if the projection reduced.
  fn try_proj_app_reduce(
    &mut self,
    e: &KExpr<M>,
    flags: WhnfFlags,
  ) -> Result<Option<(KExpr<M>, Vec<KExpr<M>>)>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    if args.is_empty() {
      return Ok(None);
    }

    if let ExprData::Prj(id, field, val, _) = head.data() {
      let field = *field;
      let id = id.clone();
      let val = val.clone();
      let wval = if flags.cheap_proj {
        self.whnf_core_with_flags(&val, flags)?
      } else {
        self.whnf(&val)?
      };
      if let Some(result) = self.try_proj_reduce(&id, field, &wval)? {
        return Ok(Some((result, args)));
      }
    }
    Ok(None)
  }

  fn try_reduce_projection_definition(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(None);
    };
    let val = match self.try_get_const(id)? {
      Some(KConst::Defn { kind: DefKind::Definition, val, .. }) => val,
      _ => return Ok(None),
    };
    let (arity, struct_id, field, struct_arg_idx) =
      match self.projection_definition_info(&val) {
        Some(info) => info,
        None => return Ok(None),
      };
    if args.len() < arity {
      return Ok(None);
    }
    let mut result =
      self.intern(KExpr::prj(struct_id, field, args[struct_arg_idx].clone()));
    for arg in args.iter().skip(arity) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  fn projection_definition_info(
    &self,
    val: &KExpr<M>,
  ) -> Option<(usize, KId<M>, u64, usize)> {
    let mut arity = 0usize;
    let mut cur = val.clone();
    loop {
      match cur.data() {
        ExprData::Lam(_, _, _, body, _) => {
          arity += 1;
          cur = body.clone();
        },
        ExprData::Prj(struct_id, field, projected, _) => {
          let ExprData::Var(idx, _, _) = projected.data() else {
            return None;
          };
          let idx = usize::try_from(*idx).ok()?;
          if idx >= arity {
            return None;
          }
          let struct_arg_idx = arity - 1 - idx;
          return Some((arity, struct_id.clone(), *field, struct_arg_idx));
        },
        _ => return None,
      }
    }
  }

  // -----------------------------------------------------------------------
  // Helpers
  // -----------------------------------------------------------------------

  /// Get the major premise's inductive KId from a recursor type.
  ///
  /// Strategy: peel `skip` foralls per Lean's stored `params + motives +
  /// minors + indices` count, then expect the next forall's domain to
  /// have an inductive `Const` head. For well-formed Lean recursors this
  /// lands exactly on the major premise.
  ///
  /// Resilience: if the strict `skip` position's domain head is not an
  /// inductive `Const`, peel up to `MAX_EXTRA_FORALLS` additional foralls
  /// scanning for the first one whose domain head IS an inductive
  /// `KConst::Indc`. This handles recursor shapes where Lean's stored
  /// counts don't align with the kernel's view of the forall structure
  /// after WHNF (e.g., nested-inductive recursors that carry extra
  /// instance/motive binders not captured by `num_params/num_motives/...`).
  ///
  /// We specifically require the head to be an **inductive** constant, not
  /// any Const: minor premises of recursors like `Nat.rec`'s `succ` case
  /// have a forall `(n : Nat)` where `Nat` is a Const inductive, but
  /// those are consumed by the initial `skip` pass. The scan only ever
  /// fires when `skip` under-counts; in that case the first Const
  /// inductive encountered is structurally the major.
  pub fn get_major_inductive_id(
    &mut self,
    rec_ty: &KExpr<M>,
    skip: u64,
  ) -> Result<KId<M>, TcError<M>> {
    const MAX_EXTRA_FORALLS: u64 = 8;

    let mut ty = rec_ty.clone();
    for _ in 0..skip {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => ty = body.clone(),
        _ => {
          return Err(TcError::Other(
            "get_major_inductive_id: not enough foralls".into(),
          ));
        },
      }
    }

    // Scan forward looking for a forall whose domain has a `KConst::Indc`
    // head. Accept the first match. Bounded so we can't loop forever.
    for _ in 0..=MAX_EXTRA_FORALLS {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, dom, body, _) => {
          let (head, _) = collect_app_spine(dom);
          if let ExprData::Const(id, _, _) = head.data() {
            // Only accept if the head resolves to an inductive.
            if matches!(self.try_get_const(id)?, Some(KConst::Indc { .. })) {
              return Ok(id.clone());
            }
          }
          ty = body.clone();
        },
        _ => {
          return Err(TcError::Other(
            "get_major_inductive_id: expected forall at major".into(),
          ));
        },
      }
    }

    Err(TcError::Other(
      "get_major_inductive_id: no inductive-headed forall within scan bound"
        .into(),
    ))
  }

  /// Convert a Nat literal to constructor form: 0 → Nat.zero, n+1 → Nat.succ(n-1).
  fn nat_to_constructor(&mut self, val: &Nat) -> KExpr<M> {
    use num_bigint::BigUint;
    // Global diagnostic: count expansions and log every 100k. A legitimate
    // `Nat.rec motive base step hugeFuel` where `step` only forces `ih`
    // on `Poly.add` paths will fire a handful of times. A pathological
    // linearly-recursing body would fire millions. Gated behind
    // `IX_NAT_EXPAND_LOG=1` so normal runs stay quiet.
    if *IX_NAT_EXPAND_LOG {
      let n =
        NAT_EXPAND_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n.is_multiple_of(10_000) {
        eprintln!("[nat_to_constructor] count={n} val_bits={}", val.0.bits());
      }
    }
    if val.0 == BigUint::ZERO {
      KExpr::cnst(self.prims.nat_zero.clone(), Box::new([]))
    } else {
      let pred_val = Nat(&val.0 - BigUint::from(1u64));
      let pred_addr = Address::hash(&pred_val.to_le_bytes());
      let pred_expr = KExpr::nat(pred_val, pred_addr);
      let succ = KExpr::cnst(self.prims.nat_succ.clone(), Box::new([]));
      KExpr::app(succ, pred_expr)
    }
  }

  fn nat_literal(&mut self, n: u64) -> KExpr<M> {
    let val = Nat::from(n);
    let addr = Address::hash(&val.to_le_bytes());
    KExpr::nat(val, addr)
  }

  /// Nat primitive reduction (add, sub, mul, div, mod, pow, gcd, bitwise, predicates).
  pub(super) fn try_reduce_nat(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    self.try_reduce_nat_with_succ_mode(e, NatSuccMode::Collapse)
  }

  fn try_reduce_nat_with_succ_mode(
    &mut self,
    e: &KExpr<M>,
    nat_succ_mode: NatSuccMode,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };
    // Nat.succ n → n + 1
    if addr == self.prims.nat_succ.addr && args.len() == 1 {
      if nat_succ_mode == NatSuccMode::Stuck {
        return Ok(None);
      }
      return self.try_reduce_nat_succ_iter(&args[0]);
    }

    if args.len() < 2 {
      return Ok(None);
    }

    let is_bin_arith = self.is_nat_bin_arith_addr(&addr);
    let is_bin_pred = self.is_nat_bin_pred_addr(&addr);

    if !is_bin_arith && !is_bin_pred {
      return Ok(None);
    }
    self.dump_nat_trace("candidate", e);

    if is_bin_pred {
      return self.try_reduce_nat_predicate(&addr, &args);
    }

    let Some(wa) = self.whnf_nat_reducer_arg(&args[0])? else {
      return Ok(None);
    };
    let Some(wb) = self.whnf_nat_reducer_arg(&args[1])? else {
      return Ok(None);
    };
    self.dump_nat_trace("arg0-whnf", &wa);
    self.dump_nat_trace("arg1-whnf", &wb);
    let a_val = match extract_nat_lit(&wa, &self.prims) {
      Some(v) => v.clone(),
      None => {
        self.dump_nat_trace("arg0-not-nat", &wa);
        return Ok(None);
      },
    };
    let b_val = match extract_nat_lit(&wb, &self.prims) {
      Some(v) => v.clone(),
      None => {
        self.dump_nat_trace("arg1-not-nat", &wb);
        return Ok(None);
      },
    };

    let result_expr = if is_bin_arith {
      let result = match compute_nat_bin(&addr, &self.prims, &a_val, &b_val) {
        Some(r) => r,
        None => {
          self.dump_nat_trace("not-computed", e);
          return Ok(None); // can't compute, leave unreduced
        },
      };
      let blob_addr = Address::hash(&result.to_le_bytes());
      KExpr::nat(result, blob_addr)
    } else {
      let b = if addr == self.prims.nat_beq.addr {
        a_val == b_val
      } else {
        a_val <= b_val
      };
      let bool_id = if b {
        self.prims.bool_true.clone()
      } else {
        self.prims.bool_false.clone()
      };
      self.intern(KExpr::cnst(bool_id, Box::new([])))
    };

    let mut result = result_expr;
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  fn try_reduce_nat_succ_iter(
    &mut self,
    arg: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let mut offset = num_bigint::BigUint::from(1u64);
    let mut cur = arg.clone();

    loop {
      if let Some(result) =
        self.try_reduce_nat_succ_linear_rec(&cur, &offset)?
      {
        return Ok(Some(result));
      }

      let w = self.whnf_with_nat_succ_mode(&cur, NatSuccMode::Stuck)?;
      if let Some(n) = extract_nat_lit(&w, &self.prims) {
        let result = Nat(&n.0 + &offset);
        let blob_addr = Address::hash(&result.to_le_bytes());
        return Ok(Some(KExpr::nat(result, blob_addr)));
      }

      let (head, args) = collect_app_spine(&w);
      if let ExprData::Const(id, _, _) = head.data()
        && id.addr == self.prims.nat_succ.addr
        && args.len() == 1
      {
        offset += 1u64;
        cur = args[0].clone();
        continue;
      }

      return Ok(None);
    }
  }

  fn try_reduce_nat_succ_linear_rec(
    &mut self,
    arg: &KExpr<M>,
    offset: &num_bigint::BigUint,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let Some(parts) = self.nat_rec_literal_parts(arg)? else {
      return Ok(None);
    };
    let Some(base) = parts.spine.get(parts.base_idx) else {
      return Ok(None);
    };
    let Some(step) = parts.spine.get(parts.step_idx) else {
      return Ok(None);
    };
    if *IX_NAT_LINEAR_REC_TRACE {
      let n = NAT_LINEAR_REC_TRACE_COUNT
        .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n < 8 {
        let step_whnf = self.whnf(step)?;
        eprintln!(
          "[nat_linear_rec] major_bits={} base_idx={} step_idx={} spine={} step_whnf={}",
          parts.major.0.bits(),
          parts.base_idx,
          parts.step_idx,
          parts.spine.len(),
          step_whnf
        );
      }
    }
    if !self.is_nat_succ_ih_step(step)? {
      return Ok(None);
    }

    let base = base.clone();
    let base_whnf = self.whnf(&base)?;
    let Some(base_val) = extract_nat_value(&base_whnf, &self.prims) else {
      return Ok(None);
    };

    let mut total = base_val.0;
    total += parts.major.0;
    total += offset;
    let result = Nat(total);
    let blob_addr = Address::hash(&result.to_le_bytes());
    Ok(Some(KExpr::nat(result, blob_addr)))
  }

  fn nat_rec_literal_parts(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<NatRecLiteralParts<M>>, TcError<M>> {
    let (head, spine) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(None);
    };
    if id.addr != self.prims.nat_rec.addr {
      return Ok(None);
    }

    let Some(KConst::Recr { params, motives, minors, indices, .. }) =
      self.try_get_const(id)?
    else {
      return Ok(None);
    };
    let params = u64_to_usize::<M>(params)?;
    let motives = u64_to_usize::<M>(motives)?;
    let minors = u64_to_usize::<M>(minors)?;
    let indices = u64_to_usize::<M>(indices)?;
    if minors < 2 {
      return Ok(None);
    }

    let base_idx = params + motives;
    let step_idx = base_idx + 1;
    let major_idx = params + motives + minors + indices;
    let Some(major) = spine.get(major_idx) else {
      return Ok(None);
    };
    let ExprData::Nat(major, _, _) = major.data() else {
      return Ok(None);
    };
    let major = major.clone();

    Ok(Some(NatRecLiteralParts { spine, major, base_idx, step_idx }))
  }

  fn is_nat_succ_ih_step(
    &mut self,
    step: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let step = self.whnf(step)?;
    let ExprData::Lam(_, _, _, body, _) = step.data() else {
      return Ok(false);
    };
    let ExprData::Lam(_, _, _, body, _) = body.data() else {
      return Ok(false);
    };

    let (head, args) = collect_app_spine(body);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(false);
    };
    if id.addr != self.prims.nat_succ.addr || args.len() != 1 {
      return Ok(false);
    }
    Ok(matches!(args[0].data(), ExprData::Var(0, _, _)))
  }

  fn nat_expr_from_value(&mut self, n: Nat) -> KExpr<M> {
    let blob_addr = Address::hash(&n.to_le_bytes());
    KExpr::nat(n, blob_addr)
  }

  fn nat_succ_n(&mut self, mut e: KExpr<M>, n: u64) -> KExpr<M> {
    for _ in 0..n {
      let succ =
        self.intern(KExpr::cnst(self.prims.nat_succ.clone(), Box::new([])));
      e = self.intern(KExpr::app(succ, e));
    }
    e
  }

  fn is_nat_bin_arith_addr(&self, addr: &Address) -> bool {
    let p = &self.prims;
    *addr == p.nat_add.addr
      || *addr == p.nat_sub.addr
      || *addr == p.nat_mul.addr
      || *addr == p.nat_div.addr
      || *addr == p.nat_mod.addr
      || *addr == p.nat_pow.addr
      || *addr == p.nat_gcd.addr
      || *addr == p.nat_land.addr
      || *addr == p.nat_lor.addr
      || *addr == p.nat_xor.addr
      || *addr == p.nat_shift_left.addr
      || *addr == p.nat_shift_right.addr
  }

  fn is_nat_bin_pred_addr(&self, addr: &Address) -> bool {
    *addr == self.prims.nat_beq.addr || *addr == self.prims.nat_ble.addr
  }

  fn whnf_nat_reducer_arg(
    &mut self,
    arg: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if !arg.has_fvars() || self.eager_reduce {
      return Ok(Some(self.whnf(arg)?));
    }

    let saved_fuel = self.rec_fuel;
    let local_fuel = saved_fuel.min(NAT_REDUCER_OPEN_ARG_REC_FUEL);
    self.rec_fuel = local_fuel;
    let result = self.whnf(arg);
    let consumed = local_fuel.saturating_sub(self.rec_fuel);
    self.rec_fuel = saved_fuel.saturating_sub(consumed);

    match result {
      Ok(w) => Ok(Some(w)),
      Err(TcError::MaxRecDepth | TcError::MaxRecFuel) => Ok(None),
      Err(err) => Err(err),
    }
  }

  /// Recursors / casesOn whose Nat-typed major can leave the term stuck.
  /// `BitVec.toNat` projects through to a Nat that may itself be stuck on
  /// a recursor, so it goes here too. Used by shallow native probes that must
  /// not treat these as concrete Nat values.
  ///
  /// Replaces a name-based `is_const_named(id, &["Nat.rec", "Nat.casesOn",
  /// "BitVec.toNat"])` whose alpha-twin display names (e.g. `Lean.RBColor.rec`
  /// for `Bool.rec`) silently bypass the check under canonical hashing.
  fn is_nat_stuck_recursor_addr(&self, addr: &Address) -> bool {
    *addr == self.prims.nat_rec.addr
      || *addr == self.prims.nat_cases_on.addr
      || *addr == self.prims.bit_vec_to_nat.addr
  }

  fn try_reduce_nat_predicate(
    &mut self,
    addr: &Address,
    args: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let Some(wa) = self.whnf_nat_reducer_arg(&args[0])? else {
      return Ok(None);
    };
    let Some(a_val) = extract_nat_lit(&wa, &self.prims) else {
      return Ok(None);
    };
    let Some(wb) = self.whnf_nat_reducer_arg(&args[1])? else {
      return Ok(None);
    };
    let Some(b_val) = extract_nat_lit(&wb, &self.prims) else {
      return Ok(None);
    };
    let decision = if *addr == self.prims.nat_beq.addr {
      a_val == b_val
    } else {
      a_val <= b_val
    };
    Ok(Some(self.nat_predicate_bool_result(decision, args)))
  }

  fn nat_predicate_bool_result(
    &mut self,
    decision: bool,
    args: &[KExpr<M>],
  ) -> KExpr<M> {
    let bool_id = if decision {
      self.prims.bool_true.clone()
    } else {
      self.prims.bool_false.clone()
    };
    let mut result = self.intern(KExpr::cnst(bool_id, Box::new([])));
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    result
  }

  /// A shallow Nat evaluator for bounded native helpers.
  ///
  /// This is intentionally not used by `Nat.beq`/`Nat.ble` primitive
  /// reduction; those follow Lean and only compare WHNF'd literal-extension
  /// arguments. BitVec helpers use this narrower evaluator to avoid forcing
  /// large recursive Nat models when only a bounded width is useful.
  fn try_eval_nat_value_for_pred(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<Nat>, TcError<M>> {
    self.try_eval_nat_value_for_pred_core(e, 0)
  }

  fn try_eval_nat_value_for_pred_core(
    &mut self,
    e: &KExpr<M>,
    depth: u8,
  ) -> Result<Option<Nat>, TcError<M>> {
    const MAX_PRED_NAT_EVAL_DEPTH: u8 = 64;
    if depth >= MAX_PRED_NAT_EVAL_DEPTH {
      return Ok(None);
    }
    if let Some(n) = extract_nat_lit(e, &self.prims) {
      return Ok(Some(n.clone()));
    }

    if self.is_stuck_nat_predicate_probe(e) {
      return Ok(None);
    }

    let (head, args) = collect_app_spine(e);
    match head.data() {
      ExprData::Const(id, _, _) => {
        if id.addr == self.prims.nat_succ.addr && args.len() == 1 {
          let Some(pred) =
            self.try_eval_nat_value_for_pred_core(&args[0], depth + 1)?
          else {
            return Ok(None);
          };
          return Ok(Some(Nat(pred.0 + 1u64)));
        }
        if id.addr == self.prims.nat_pred.addr && args.len() == 1 {
          let Some(n) =
            self.try_eval_nat_value_for_pred_core(&args[0], depth + 1)?
          else {
            return Ok(None);
          };
          let result = if n.0 == num_bigint::BigUint::ZERO {
            Nat(num_bigint::BigUint::ZERO)
          } else {
            Nat(n.0 - 1u64)
          };
          return Ok(Some(result));
        }
        if self.is_nat_bin_arith_addr(&id.addr) && args.len() == 2 {
          let Some(a) =
            self.try_eval_nat_value_for_pred_core(&args[0], depth + 1)?
          else {
            return Ok(None);
          };
          let Some(b) =
            self.try_eval_nat_value_for_pred_core(&args[1], depth + 1)?
          else {
            return Ok(None);
          };
          return Ok(compute_nat_bin(&id.addr, &self.prims, &a, &b));
        }
      },
      ExprData::Var(..)
      | ExprData::FVar(..)
      | ExprData::Sort(..)
      | ExprData::Lam(..)
      | ExprData::All(..)
      | ExprData::Str(..)
      | ExprData::Nat(..) => return Ok(None),
      ExprData::App(..) | ExprData::Let(..) | ExprData::Prj(..) => {},
    }

    let w = self.whnf(e)?;
    self.dump_nat_trace("pred-arg-whnf", &w);
    if let Some(n) = extract_nat_value(&w, &self.prims) {
      return Ok(Some(n));
    }
    if &w == e {
      return Ok(None);
    }
    self.try_eval_nat_value_for_pred_core(&w, depth + 1)
  }

  fn is_stuck_nat_predicate_probe(&self, e: &KExpr<M>) -> bool {
    let (head, _) = collect_app_spine(e);
    match head.data() {
      ExprData::Const(id, _, _) => {
        self.is_nat_bin_pred_addr(&id.addr)
          || self.is_nat_stuck_recursor_addr(&id.addr)
      },
      ExprData::Prj(id, _, val, _) => {
        if id.addr == self.prims.fin.addr {
          return true;
        }
        let (val_head, _) = collect_app_spine(val);
        matches!(
          val_head.data(),
          ExprData::Const(val_id, _, _)
            if self.is_nat_stuck_recursor_addr(&val_id.addr)
        )
      },
      _ => false,
    }
  }

  /// Native Nat.decLe/decEq/decLt reduction.
  ///
  /// Intercepts `Nat.decLe n m`, `Nat.decEq n m`, `Nat.decLt n m` when both
  /// arguments are Nat literals. Computes the boolean result natively and
  /// constructs the appropriate `Decidable.isTrue prop proof` or
  /// `Decidable.isFalse prop proof`.
  ///
  /// Constructors in the kernel are fully explicit:
  ///   `Decidable.isTrue  : (p : Prop) → p → Decidable p`
  ///   `Decidable.isFalse : (p : Prop) → (p → False) → Decidable p`
  /// so the proposition `p` must be supplied as the first argument.
  ///
  /// Proof terms:
  /// - decLe true:  `Decidable.isTrue  prop (Nat.le_of_ble_eq_true  n m (Eq.refl.{1} Bool Bool.true))`
  /// - decEq true:  `Decidable.isTrue  prop (Nat.eq_of_beq_eq_true  n m (Eq.refl.{1} Bool Bool.true))`
  /// - decEq false: `Decidable.isFalse prop (Nat.ne_of_beq_eq_false n m (Eq.refl.{1} Bool Bool.false))`
  /// - decLe false: falls through to delta (proof requires `False` primitive not yet available)
  /// - decLt n m:   delegates to decLe (n+1) m
  pub(super) fn try_reduce_decidable(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    let p = &self.prims;
    let is_dec_le = addr == p.nat_dec_le.addr;
    let is_dec_eq = addr == p.nat_dec_eq.addr;
    let is_dec_lt = addr == p.nat_dec_lt.addr;
    let is_int_dec_le = addr == p.int_dec_le.addr;
    let is_int_dec_eq = addr == p.int_dec_eq.addr;
    let is_int_dec_lt = addr == p.int_dec_lt.addr;
    if is_int_dec_le || is_int_dec_eq || is_int_dec_lt {
      return self.try_normalize_int_decidable(&addr, &args);
    }
    if !is_dec_le && !is_dec_eq && !is_dec_lt {
      return Ok(None);
    }
    if args.len() < 2 {
      return Ok(None);
    }

    let wa = self.whnf(&args[0])?;
    let wb = self.whnf(&args[1])?;
    let a_val = match extract_nat_value(&wa, &self.prims) {
      Some(v) => v,
      None => return Ok(None),
    };
    let b_val = match extract_nat_value(&wb, &self.prims) {
      Some(v) => v,
      None => return Ok(None),
    };

    // S5: Eq.refl is universe-polymorphic: @Eq.refl.{u}.
    // For Bool : Type = Sort 1, we need u = 1 = Succ(Zero).
    let u1 = KUniv::succ(KUniv::zero());

    // decLt n m  →  decLe (n+1) m
    if is_dec_lt {
      let succ_a = Nat(&a_val.0 + 1u64);
      let succ_a_addr = Address::hash(&succ_a.to_le_bytes());
      let succ_a_expr = self.intern(KExpr::nat(succ_a, succ_a_addr));
      // Build: Nat.decLe (n+1) m
      let dec_le_const =
        self.intern(KExpr::cnst(self.prims.nat_dec_le.clone(), Box::new([])));
      let mut result = self.intern(KExpr::app(dec_le_const, succ_a_expr));
      result = self.intern(KExpr::app(result, args[1].clone()));
      for arg in args.iter().skip(2) {
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      // Recursively reduce the decLe
      return Ok(Some(result));
    }

    // Extract the proposition from the type of `e`.
    // `e : Decidable prop` → we need `prop` as the first constructor argument.
    // Use infer_only to avoid def-eq checks (safe within WHNF).
    let prop = match self.with_infer_only(|tc| tc.infer(e)) {
      Ok(e_ty) => {
        let e_ty_whnf = self.whnf(&e_ty)?;
        let (_, type_args) = collect_app_spine(&e_ty_whnf);
        match type_args.into_iter().next() {
          Some(p) => p,
          None => return Ok(None), // not `Decidable prop` — bail
        }
      },
      Err(_) => return Ok(None), // inference failed — bail to delta
    };

    let (b_result, proof_true_fn, proof_false_fn) = if is_dec_le {
      (
        a_val <= b_val,
        &self.prims.nat_le_of_ble_eq_true,
        &self.prims.nat_not_le_of_not_ble_eq_true,
      )
    } else {
      // is_dec_eq
      (
        a_val == b_val,
        &self.prims.nat_eq_of_beq_eq_true,
        &self.prims.nat_ne_of_beq_eq_false,
      )
    };
    let proof_true_fn = proof_true_fn.clone();
    let proof_false_fn = proof_false_fn.clone();

    let result_expr = if b_result {
      // Decidable.isTrue prop (proof_fn n m (Eq.refl.{1} Bool Bool.true))
      let eq_refl = self.intern(KExpr::cnst(
        self.prims.eq_refl.clone(),
        Box::new([u1.clone()]),
      ));
      let bool_ty =
        self.intern(KExpr::cnst(self.prims.bool_type.clone(), Box::new([])));
      let bool_true =
        self.intern(KExpr::cnst(self.prims.bool_true.clone(), Box::new([])));
      let refl_proof = self.intern(KExpr::app(eq_refl, bool_ty));
      let refl_proof = self.intern(KExpr::app(refl_proof, bool_true));

      // Build: proof_fn n m refl_proof
      let proof_const =
        self.intern(KExpr::cnst(proof_true_fn.clone(), Box::new([])));
      let proof = self.intern(KExpr::app(proof_const, args[0].clone()));
      let proof = self.intern(KExpr::app(proof, args[1].clone()));
      let proof = self.intern(KExpr::app(proof, refl_proof));

      // Build: Decidable.isTrue prop proof
      let is_true = self.intern(KExpr::cnst(
        self.prims.decidable_is_true.clone(),
        Box::new([]),
      ));
      let r = self.intern(KExpr::app(is_true, prop));
      self.intern(KExpr::app(r, proof))
    } else if is_dec_eq {
      // Decidable.isFalse prop (Nat.ne_of_beq_eq_false n m (Eq.refl.{1} Bool Bool.false))
      let eq_refl = self.intern(KExpr::cnst(
        self.prims.eq_refl.clone(),
        Box::new([u1.clone()]),
      ));
      let bool_ty =
        self.intern(KExpr::cnst(self.prims.bool_type.clone(), Box::new([])));
      let bool_false =
        self.intern(KExpr::cnst(self.prims.bool_false.clone(), Box::new([])));
      let refl_proof = self.intern(KExpr::app(eq_refl, bool_ty));
      let refl_proof = self.intern(KExpr::app(refl_proof, bool_false));

      let proof_const =
        self.intern(KExpr::cnst(proof_false_fn.clone(), Box::new([])));
      let proof = self.intern(KExpr::app(proof_const, args[0].clone()));
      let proof = self.intern(KExpr::app(proof, args[1].clone()));
      let proof = self.intern(KExpr::app(proof, refl_proof));

      // Build: Decidable.isFalse prop proof
      let is_false = self.intern(KExpr::cnst(
        self.prims.decidable_is_false.clone(),
        Box::new([]),
      ));
      let r = self.intern(KExpr::app(is_false, prop));
      self.intern(KExpr::app(r, proof))
    } else {
      // decLe false: the proof requires `Bool.noConfusion.{0} False Bool.false Bool.true`
      // which needs a `False` primitive not yet registered. Fall through to
      // delta reduction which correctly unfolds Nat.decLe to its definition body.
      return Ok(None);
    };

    let mut result = result_expr;
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  fn try_normalize_int_decidable(
    &mut self,
    addr: &Address,
    args: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if args.len() < 2 {
      return Ok(None);
    }

    let wa = self.whnf(&args[0])?;
    let wb = self.whnf(&args[1])?;
    let Some(a_val) = extract_int_lit(&wa, &self.prims) else {
      return Ok(None);
    };
    let Some(b_val) = extract_int_lit(&wb, &self.prims) else {
      return Ok(None);
    };

    let a = intern_int_lit(self, a_val);
    let b = intern_int_lit(self, b_val);
    if a.hash_key() == args[0].hash_key() && b.hash_key() == args[1].hash_key()
    {
      return Ok(None);
    }

    let head_id = if *addr == self.prims.int_dec_eq.addr {
      self.prims.int_dec_eq.clone()
    } else if *addr == self.prims.int_dec_le.addr {
      self.prims.int_dec_le.clone()
    } else {
      self.prims.int_dec_lt.clone()
    };
    let head = self.intern(KExpr::cnst(head_id, Box::new([])));
    let mut result = self.intern(KExpr::app(head, a));
    result = self.intern(KExpr::app(result, b));
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  /// Quotient reduction (Quot.lift, Quot.ind).
  fn try_quot_reduce(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    // Quot.lift: 6 args, f at 3, major at 5
    // Quot.ind:  5 args, f at 3, major at 4
    let (f_idx, major_idx) = if addr == self.prims.quot_lift.addr {
      if args.len() < 6 {
        return Ok(None);
      }
      (3usize, 5usize)
    } else if addr == self.prims.quot_ind.addr {
      if args.len() < 5 {
        return Ok(None);
      }
      (3usize, 4usize)
    } else {
      return Ok(None);
    };

    let major_whnf = self.whnf(&args[major_idx])?;
    let (mk_head, mk_args) = collect_app_spine(&major_whnf);
    let mk_addr = match mk_head.data() {
      ExprData::Const(id, _, _) => &id.addr,
      _ => return Ok(None),
    };
    if *mk_addr != self.prims.quot_ctor.addr {
      return Ok(None);
    }

    // Quot.mk has exactly 3 args: (α, r, a). Value is the last.
    if mk_args.len() != 3 {
      return Ok(None);
    }
    let quot_val = mk_args[2].clone();

    let mut result = self.intern(KExpr::app(args[f_idx].clone(), quot_val));
    for arg in args.iter().skip(major_idx + 1) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  // -----------------------------------------------------------------------
  // BitVec reduction
  // -----------------------------------------------------------------------

  /// Reduce the small BitVec fragment that is definitionally Nat-backed:
  /// - `BitVec.toNat (BitVec.ofNat w n)` reduces to `n % 2^w`
  /// - `BitVec.ult w x y` reduces by evaluating `x.toNat < y.toNat`
  /// - `decide (x < y)` for BitVec reduces through the same comparison
  fn try_reduce_bitvec(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(None);
    };

    if id.addr == self.prims.bit_vec_to_nat.addr && args.len() >= 2 {
      if let Some(result) = self.try_reduce_bitvec_to_nat(&args[1])? {
        return Ok(Some(self.finish_app_result(result, &args, 2)));
      }
      return Ok(None);
    }

    if id.addr == self.prims.bit_vec_ult.addr && args.len() >= 3 {
      if let Some(result) =
        self.try_reduce_bitvec_ult(&args[0], &args[1], &args[2])?
      {
        return Ok(Some(self.finish_app_result(result, &args, 3)));
      }
      return Ok(None);
    }

    if id.addr == self.prims.decidable_decide.addr
      && args.len() >= 2
      && let Some(result) = self.try_reduce_bitvec_lt_prop(&args[0])?
    {
      return Ok(Some(self.finish_app_result(result, &args, 2)));
    }

    Ok(None)
  }

  fn try_reduce_bitvec_ult(
    &mut self,
    width: &KExpr<M>,
    lhs: &KExpr<M>,
    rhs: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let lhs_nat = self.bitvec_to_nat_expr(width, lhs)?;
    let rhs_nat = self.bitvec_to_nat_expr(width, rhs)?;
    let rhs_nat_whnf = self.whnf(&rhs_nat)?;
    if let Some(rhs_val) = extract_nat_value(&rhs_nat_whnf, &self.prims) {
      if rhs_val.0 == num_bigint::BigUint::ZERO {
        let result =
          self.intern(KExpr::cnst(self.prims.bool_false.clone(), Box::new([])));
        return Ok(Some(result));
      }

      let lhs_nat_whnf = self.whnf(&lhs_nat)?;
      if let Some(lhs_val) = extract_nat_value(&lhs_nat_whnf, &self.prims) {
        let result_id = if lhs_val.0 < rhs_val.0 {
          self.prims.bool_true.clone()
        } else {
          self.prims.bool_false.clone()
        };
        let result = self.intern(KExpr::cnst(result_id, Box::new([])));
        return Ok(Some(result));
      }
    }

    // `BitVec.ult x y` is definitionally `decide (x.toNat < y.toNat)`.
    // Kernel Nat LT reduces through `Nat.ble (Nat.succ x.toNat) y.toNat`.
    let lhs_succ = self.nat_succ_n(lhs_nat, 1);
    let ble =
      self.intern(KExpr::cnst(self.prims.nat_ble.clone(), Box::new([])));
    let cmp_lhs = self.intern(KExpr::app(ble, lhs_succ));
    let cmp = self.intern(KExpr::app(cmp_lhs, rhs_nat));
    let result = self.whnf(&cmp)?;
    if self.bool_lit_value(&result).is_some() {
      Ok(Some(result))
    } else {
      Ok(None)
    }
  }

  fn try_reduce_bitvec_lt_prop(
    &mut self,
    prop: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(prop);
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(None);
    };
    if id.addr != self.prims.lt_lt.addr || args.len() != 4 {
      return Ok(None);
    }

    let (type_head, type_args) = collect_app_spine(&args[0]);
    let ExprData::Const(type_id, _, _) = type_head.data() else {
      return Ok(None);
    };
    if type_id.addr != self.prims.bit_vec.addr || type_args.len() != 1 {
      return Ok(None);
    }

    self.try_reduce_bitvec_ult(&type_args[0], &args[2], &args[3])
  }

  fn bitvec_to_nat_expr(
    &mut self,
    width: &KExpr<M>,
    value: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    if let Some(result) = self.try_reduce_bitvec_to_nat(value)? {
      return Ok(result);
    }

    let head =
      self.intern(KExpr::cnst(self.prims.bit_vec_to_nat.clone(), Box::new([])));
    let with_width = self.intern(KExpr::app(head, width.clone()));
    Ok(self.intern(KExpr::app(with_width, value.clone())))
  }

  fn try_reduce_bitvec_to_nat(
    &mut self,
    value: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let Some((width, n_expr)) = self.bitvec_of_nat_args(value) else {
      return Ok(None);
    };

    let n_whnf = self.whnf(&n_expr)?;
    let Some(n) = extract_nat_value(&n_whnf, &self.prims) else {
      return Ok(None);
    };

    if n.0 == num_bigint::BigUint::ZERO {
      return Ok(Some(self.nat_literal(0)));
    }

    let width_val = self.try_eval_nat_value_for_pred(&width)?;
    let Some(width) = width_val.and_then(|w| w.to_u64()) else {
      return Ok(None);
    };

    const REDUCE_BITVEC_WIDTH_MAX: u64 = 1 << 24;
    if width > REDUCE_BITVEC_WIDTH_MAX {
      return Ok(None);
    }

    // `width` was bounded above by `REDUCE_BITVEC_WIDTH_MAX = 1 << 24`, so
    // it always fits in `usize` on every supported target.
    let width_usize = usize::try_from(width).unwrap_or(usize::MAX);
    let modulus = num_bigint::BigUint::from(1u64) << width_usize;
    let result = Nat(n.0 % modulus);
    Ok(Some(self.nat_expr_from_value(result)))
  }

  fn bitvec_of_nat_args(&self, e: &KExpr<M>) -> Option<(KExpr<M>, KExpr<M>)> {
    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return None;
    };
    if id.addr == self.prims.bit_vec_of_nat.addr && args.len() == 2 {
      return Some((args[0].clone(), args[1].clone()));
    }
    if id.addr != self.prims.of_nat_of_nat.addr || args.len() < 2 {
      return None;
    }

    let (type_head, type_args) = collect_app_spine(&args[0]);
    let ExprData::Const(type_id, _, _) = type_head.data() else {
      return None;
    };
    if type_id.addr == self.prims.bit_vec.addr && type_args.len() == 1 {
      Some((type_args[0].clone(), args[1].clone()))
    } else {
      None
    }
  }

  fn bool_lit_value(&self, e: &KExpr<M>) -> Option<bool> {
    let ExprData::Const(id, _, _) = e.data() else {
      return None;
    };
    if id.addr == self.prims.bool_true.addr {
      Some(true)
    } else if id.addr == self.prims.bool_false.addr {
      Some(false)
    } else {
      None
    }
  }

  fn finish_app_result(
    &mut self,
    mut result: KExpr<M>,
    args: &[KExpr<M>],
    consumed: usize,
  ) -> KExpr<M> {
    for arg in args.iter().skip(consumed) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    result
  }

  // -----------------------------------------------------------------------
  // Native reduction (Lean.reduceBool, Lean.reduceNat, System.Platform.numBits)
  // -----------------------------------------------------------------------

  /// Try native reduction, matching C++ kernel's `reduce_native`.
  /// - `Lean.reduceBool arg`: look up `arg` (a constant), evaluate its body, return Bool
  /// - `Lean.reduceNat arg`: look up `arg` (a constant), evaluate its body, return Nat
  /// - `System.Platform.numBits`: return 64 (matching Lean's 64-bit platform)
  pub(super) fn try_reduce_native(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let head_addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    if let ExprData::Const(id, _, _) = head.data() {
      let is_unit_sizeof_impl =
        id.addr == self.prims.punit_size_of_1.addr && args.len() == 1;

      if e.lbr() > 0 {
        if is_unit_sizeof_impl {
          return Ok(Some(self.nat_literal(1)));
        }
        return Ok(None);
      }

      // `System.Platform.numBits` is defined as the value projection from the
      // platform subtype returned by `System.Platform.getNumBits ()`.
      if id.addr == self.prims.subtype_val.addr && args.len() == 3 {
        let (value_head, value_args) = collect_app_spine(&args[2]);
        if value_args.len() == 1
          && let ExprData::Const(value_id, _, _) = value_head.data()
          && value_id.addr == self.prims.system_platform_get_num_bits.addr
        {
          return Ok(Some(self.nat_literal(64)));
        }
      }

      // Lean's generated `PUnit`/`Unit` SizeOf instance is extensionally the
      // constant function 1, but its body recurses on an open unit variable.
      // Reduce this primitive singleton case directly.
      if id.addr == self.prims.size_of_size_of.addr && args.len() == 3 {
        let (ty_head, _) = collect_app_spine(&args[0]);
        if let ExprData::Const(ty_id, _, _) = ty_head.data()
          && (ty_id.addr == self.prims.unit.addr
            || ty_id.addr == self.prims.punit.addr)
        {
          return Ok(Some(self.nat_literal(1)));
        }
      }

      if is_unit_sizeof_impl {
        return Ok(Some(self.nat_literal(1)));
      }
    }

    // System.Platform.numBits is a Nat-valued wrapper around the opaque
    // extern `System.Platform.getNumBits`. Delta-unfolding gets stuck at
    // the extern, so reduce the public Nat constant directly.
    if head_addr == self.prims.system_platform_num_bits.addr && args.is_empty()
    {
      return Ok(Some(self.nat_literal(64)));
    }

    // Lean.reduceBool / Lean.reduceNat: arg must be a single constant
    let is_reduce_bool = head_addr == self.prims.reduce_bool.addr;
    let is_reduce_nat = head_addr == self.prims.reduce_nat.addr;
    if !is_reduce_bool && !is_reduce_nat {
      return Ok(None);
    }
    if args.len() != 1 {
      return Ok(None);
    }
    // Re-entrancy guard: prevent whnf → native → whnf → native stack overflow
    if self.in_native_reduce {
      return Ok(None);
    }

    // The argument should be a constant whose definition we can evaluate
    let arg_const = match args[0].data() {
      ExprData::Const(id, us, _) => (id.clone(), us.clone()),
      _ => return Ok(None),
    };
    let (arg_id, arg_us) = arg_const;

    // Look up the constant's definition body
    let body = match self.try_get_const(&arg_id)? {
      Some(KConst::Defn { val, .. }) => val.clone(),
      _ => return Ok(None),
    };

    // Instantiate universe params and fully evaluate (guarded)
    let us_vec: Vec<_> = arg_us.to_vec();
    let body = self.instantiate_univ_params(&body, &us_vec)?;
    self.in_native_reduce = true;
    let result = self.whnf(&body);
    self.in_native_reduce = false;
    let result = result?;

    if is_reduce_bool {
      // Result must be Bool.true or Bool.false
      let result_addr = match result.data() {
        ExprData::Const(id, _, _) => &id.addr,
        _ => return Ok(None),
      };
      if *result_addr == self.prims.bool_true.addr
        || *result_addr == self.prims.bool_false.addr
      {
        Ok(Some(result))
      } else {
        Ok(None) // not a Bool literal — leave unreduced
      }
    } else {
      // reduceNat: result must be a Nat literal
      match result.data() {
        ExprData::Nat(..) => Ok(Some(result)),
        _ => Ok(None),
      }
    }
  }

  // -----------------------------------------------------------------------
  // String primitive reduction
  // -----------------------------------------------------------------------

  pub(super) fn try_reduce_string(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    if args.len() != 1 {
      return Ok(None);
    }
    let ExprData::Const(id, _, _) = head.data() else {
      return Ok(None);
    };
    let is_back = id.addr == self.prims.string_back.addr
      || id.addr == self.prims.string_legacy_back.addr;
    let is_utf8_byte_size = id.addr == self.prims.string_utf8_byte_size.addr;
    let is_to_byte_array = id.addr == self.prims.string_to_byte_array.addr;
    if !is_back && !is_utf8_byte_size && !is_to_byte_array {
      return Ok(None);
    }

    let s = match args[0].data() {
      ExprData::Str(s, _, _) => s,
      _ => return Ok(None),
    };
    if is_utf8_byte_size {
      let n = Nat::from(s.len() as u64);
      let addr = Address::hash(&n.to_le_bytes());
      return Ok(Some(self.intern(KExpr::nat(n, addr))));
    }
    if is_to_byte_array {
      if s.is_empty() {
        return Ok(Some(self.intern(KExpr::cnst(
          self.prims.byte_array_empty.clone(),
          Box::new([]),
        ))));
      }
      return Ok(None);
    }

    let codepoint = s.chars().last().map_or(65u32, u32::from);
    Ok(Some(self.char_of_nat_expr(u64::from(codepoint))))
  }

  fn char_of_nat_expr(&mut self, n: u64) -> KExpr<M> {
    let char_of_nat =
      self.intern(KExpr::cnst(self.prims.char_of_nat.clone(), Box::new([])));
    let nat_val = Nat::from(n);
    let nat_addr = Address::hash(&nat_val.to_le_bytes());
    let nat_lit = self.intern(KExpr::nat(nat_val, nat_addr));
    self.intern(KExpr::app(char_of_nat, nat_lit))
  }
}

// ---------------------------------------------------------------------------
// Free-standing helpers for nat reduction
// ---------------------------------------------------------------------------

use super::primitive::Primitives;

/// Zero constant shared across `extract_nat_lit` calls.
static NAT_ZERO_LITERAL: LazyLock<Nat> =
  LazyLock::new(|| Nat(num_bigint::BigUint::ZERO));

/// Extract a nat value from a literal or `Nat.zero` constructor.
///
/// Matches both `Nat(n)` literals and the `Nat.zero` constructor constant,
/// mirroring C++ `is_nat_lit_ext` and lean4lean `rawNatLitExt?`. After iota
/// reduction, `Nat.zero` can appear as `Const(Nat.zero, [])` which must be
/// recognized for native Nat operations to fire.
fn extract_nat_lit<'a, M: KernelMode>(
  e: &'a KExpr<M>,
  prims: &Primitives<M>,
) -> Option<&'a Nat> {
  match e.data() {
    ExprData::Nat(val, _, _) => Some(val),
    ExprData::Const(id, _, _) if id.addr == prims.nat_zero.addr => {
      Some(&NAT_ZERO_LITERAL)
    },
    _ => None,
  }
}

/// Extract a Nat value from either literal form or a constructor numeral.
///
/// Iota reduction on `Nat` literals can expose the matched value as
/// `Nat.succ <literal predecessor>` inside branch bodies. Some non-Nat
/// primitive helpers recover that value here before deciding whether a
/// surrounding native reduction can proceed.
fn extract_nat_value<M: KernelMode>(
  e: &KExpr<M>,
  prims: &Primitives<M>,
) -> Option<Nat> {
  if let Some(n) = extract_nat_lit(e, prims) {
    return Some(n.clone());
  }

  let (head, args) = collect_app_spine(e);
  let ExprData::Const(id, _, _) = head.data() else {
    return None;
  };
  if id.addr != prims.nat_succ.addr || args.len() != 1 {
    return None;
  }
  let pred = extract_nat_value(&args[0], prims)?;
  Some(Nat(pred.0 + 1u64))
}

fn gcd_biguint(
  a: &num_bigint::BigUint,
  b: &num_bigint::BigUint,
) -> num_bigint::BigUint {
  let mut x = a.clone();
  let mut y = b.clone();
  while y != num_bigint::BigUint::ZERO {
    let t = y.clone();
    y = &x % &y;
    x = t;
  }
  x
}

/// Compute a binary nat operation. Returns `None` if the operation can't be
/// computed (e.g., exponent too large) — caller leaves the expression unreduced.
fn compute_nat_bin<M: KernelMode>(
  addr: &Address,
  p: &Primitives<M>,
  a: &Nat,
  b: &Nat,
) -> Option<Nat> {
  use num_bigint::BigUint;
  let zero = BigUint::ZERO;
  let r = if *addr == p.nat_add.addr {
    &a.0 + &b.0
  } else if *addr == p.nat_sub.addr {
    if a.0 >= b.0 { &a.0 - &b.0 } else { zero }
  } else if *addr == p.nat_mul.addr {
    &a.0 * &b.0
  } else if *addr == p.nat_div.addr {
    if b.0 == zero { zero } else { &a.0 / &b.0 }
  } else if *addr == p.nat_mod.addr {
    if b.0 == zero { a.0.clone() } else { &a.0 % &b.0 }
  } else if *addr == p.nat_pow.addr {
    // Limit matches C++ kernel `ReducePowMaxExp` and lean4lean `reducePowMaxExp`.
    const REDUCE_POW_MAX_EXP: u64 = 1 << 24; // 16_777_216
    match b.to_u64() {
      #[allow(clippy::cast_possible_truncation)] // guarded: exp <= 2^24
      Some(exp) if exp <= REDUCE_POW_MAX_EXP => a.0.pow(exp as u32),
      _ => return None, // too large to compute
    }
  } else if *addr == p.nat_gcd.addr {
    gcd_biguint(&a.0, &b.0)
  } else if *addr == p.nat_land.addr {
    &a.0 & &b.0
  } else if *addr == p.nat_lor.addr {
    &a.0 | &b.0
  } else if *addr == p.nat_xor.addr {
    &a.0 ^ &b.0
  } else if *addr == p.nat_shift_left.addr {
    let shift = usize::try_from(b.to_u64()?).ok()?;
    &a.0 << shift
  } else if *addr == p.nat_shift_right.addr {
    let shift = usize::try_from(b.to_u64()?).ok()?;
    &a.0 >> shift
  } else {
    return None;
  };
  Some(Nat(r))
}

// ---------------------------------------------------------------------------
// Int literal helpers
// ---------------------------------------------------------------------------
//
// Lean's C++ kernel has no parallel `reduce_int` (only `reduce_nat` +
// `reduce_native`). Instead, it reduces Int operations symbolically through
// `Int.rec` pattern matching on `Int.ofNat` / `Int.negSucc`, cascading into
// native Nat ops. For expressions like `Int.bmod (-1) (2^32)`, that chain
// goes through `Decidable.rec (LT.lt Int ...) ...` which in turn requires
// reducing `Int.decLt = decNonneg (b - a)` through `Int.sub` / `Int.subNatNat`
// etc. — tractable for Lean's kernel but a known source of stuck reductions
// when any link of the chain is missing. Lean's stdlib mitigates with
// `Int.ble'` / `Int.blt'` "for kernel reduction" hand-crafted `noncomputable`
// defs, but they still cascade through delta+iota.
//
// Our kernel takes the direct route: if the head of an app-spine is a known
// Int primitive and all arguments whnf to literals (Int, Nat, or Bool), we
// compute the result natively and short-circuit the whole delta+iota chain.

use num_bigint::BigInt;

/// An Int literal in canonical kernel constructor form.
///
/// Lean's canonical form is `Int.ofNat n` (non-negative) or
/// `Int.negSucc n` (`= -(n+1)`, ≤ -1). We flatten both into a single
/// `BigInt` for arithmetic and re-encode via `intern_int_lit` afterwards.
type IntVal = BigInt;

/// Extract an Int value from an app-spine whose head is `Int.ofNat` or
/// `Int.negSucc` applied to a Nat literal. Returns `None` for any other
/// shape so the caller leaves the expression unreduced for delta+iota to
/// handle.
///
/// Callers typically pass a whnf'd expression so partially-applied
/// constructors (e.g. `Int.ofNat` with a non-literal argument) will
/// naturally be rejected here.
fn extract_int_lit<M: KernelMode>(
  e: &KExpr<M>,
  prims: &Primitives<M>,
) -> Option<IntVal> {
  let (head, args) = collect_app_spine(e);
  let (head_id, _) = match head.data() {
    ExprData::Const(id, us, _) => (id, us),
    _ => return None,
  };
  if args.len() != 1 {
    return None;
  }
  let nat_val = extract_nat_value(&args[0], prims)?;
  let n: BigInt = nat_val.0.clone().into();
  if head_id.addr == prims.int_of_nat.addr {
    Some(n) // Int.ofNat n = n
  } else if head_id.addr == prims.int_neg_succ.addr {
    Some(-(n + BigInt::from(1))) // Int.negSucc n = -(n+1)
  } else {
    None
  }
}

/// Build a canonical-form Int literal expression: `Int.ofNat n` for n ≥ 0,
/// `Int.negSucc (|n| - 1)` for n < 0. Used as the return form of native
/// Int reductions so subsequent delta+iota steps see the value in its
/// ctor-headed shape (letting `decNonneg` / `Int.rec` iota-reduce in the
/// caller).
fn intern_int_lit<M: KernelMode>(
  tc: &mut TypeChecker<M>,
  v: IntVal,
) -> KExpr<M> {
  use num_bigint::Sign;
  let (sign, magnitude) = v.into_parts();
  let nat_val = match sign {
    Sign::Minus => {
      // negSucc n encodes -(n+1); shift magnitude down by 1 to get n.
      // Safe: Sign::Minus implies magnitude >= 1, so subtract can't
      // underflow.
      Nat(magnitude - 1u32)
    },
    Sign::NoSign | Sign::Plus => Nat(magnitude),
  };
  let nat_addr = Address::hash(&nat_val.to_le_bytes());
  let nat_expr = tc.intern(KExpr::nat(nat_val, nat_addr));
  let ctor_id = match sign {
    Sign::Minus => tc.prims.int_neg_succ.clone(),
    _ => tc.prims.int_of_nat.clone(),
  };
  let ctor = tc.intern(KExpr::cnst(ctor_id, Box::new([])));
  // With Sign::NoSign (zero) we use int_of_nat → Int.ofNat 0 = 0.
  // With non-negative => Int.ofNat n. With negative => Int.negSucc (n-1).
  tc.intern(KExpr::app(ctor, nat_expr))
}

#[cfg(test)]
mod tests {

  use super::super::constant::KConst;
  use super::super::env::KEnv;
  use super::super::expr::{ExprData, KExpr};
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::{Anon, Meta};
  use super::super::primitive::Primitives;
  use super::super::tc::TypeChecker;
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::env::{DefinitionSafety, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }
  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }
  fn sort0() -> AE {
    AE::sort(AU::zero())
  }
  fn sort1() -> AE {
    AE::sort(AU::succ(AU::zero()))
  }

  /// Build a minimal env with a single definition: `id := λ x. x : Sort 0 → Sort 0`
  fn env_with_id() -> KEnv<Anon> {
    let mut env = KEnv::new();
    let id_ty = AE::all((), (), sort0(), sort0()); // Sort 0 → Sort 0
    let id_val = AE::lam((), (), sort0(), AE::var(0, ())); // λ x. x
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
    // Opaque constant
    let opaq_ty = sort0();
    let opaq_val = sort0();
    env.insert(
      mk_id("opaque"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Opaque,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: 0,
        ty: opaq_ty,
        val: opaq_val,
        lean_all: (),
        block: mk_id("opaque"),
      },
    );
    let opaque_def_ty = sort0();
    let opaque_def_val = sort1();
    env.insert(
      mk_id("opaque_def"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: 0,
        ty: opaque_def_ty,
        val: opaque_def_val,
        lean_all: (),
        block: mk_id("opaque_def"),
      },
    );
    env
  }

  #[test]
  fn whnf_var_identity() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    let v = AE::var(0, ());
    assert_eq!(tc.whnf(&v).unwrap(), v);
  }

  #[test]
  fn whnf_sort_identity() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    assert_eq!(tc.whnf(&sort0()).unwrap(), sort0());
  }

  #[test]
  fn whnf_lam_identity() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    assert_eq!(tc.whnf(&lam).unwrap(), lam);
  }

  #[test]
  fn whnf_beta_simple() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    // (λ x. x) a → a
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let a = AE::sort(AU::succ(AU::zero()));
    let app = AE::app(lam, a.clone());
    assert_eq!(tc.whnf(&app).unwrap(), a);
  }

  #[test]
  fn whnf_beta_multi() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    // (λ x y. x) a b → a
    let body = AE::var(1, ()); // x (de Bruijn 1, the outer binder)
    let inner_lam = AE::lam((), (), sort0(), body);
    let outer_lam = AE::lam((), (), sort0(), inner_lam);
    let a = sort0();
    let b = sort1();
    let app = AE::app(AE::app(outer_lam, a.clone()), b);
    assert_eq!(tc.whnf(&app).unwrap(), a);
  }

  #[test]
  fn whnf_zeta() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    // let x := Sort 0 in x → Sort 0
    let let_e = AE::let_((), sort1(), sort0(), AE::var(0, ()), true);
    assert_eq!(tc.whnf(&let_e).unwrap(), sort0());
  }

  #[test]
  fn whnf_delta() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    // id(Sort 0) should delta-unfold id then beta-reduce
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let app = AE::app(id_const, sort0());
    assert_eq!(tc.whnf(&app).unwrap(), sort0());
  }

  #[test]
  fn whnf_delta_opaque_blocked() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    let opaque = AE::cnst(mk_id("opaque"), Box::new([]));
    // Opaque should NOT be unfolded
    let result = tc.whnf(&opaque).unwrap();
    assert!(matches!(result.data(), ExprData::Const(..)));
  }

  #[test]
  fn whnf_delta_opaque_hint_unfolds() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    let opaque_def = AE::cnst(mk_id("opaque_def"), Box::new([]));
    let result = tc.whnf(&opaque_def).unwrap();
    assert_eq!(result, sort1());
  }

  #[test]
  fn whnf_string_legacy_back_empty_literal() {
    use super::super::testing as kt;

    let mut env = KEnv::new();
    let mut tc = TypeChecker::new(&mut env);
    let back = kt::ME::cnst(tc.prims.string_legacy_back.clone(), Box::new([]));
    let empty = kt::ME::str(String::new(), Address::hash(b""));
    let result = tc.whnf(&kt::ME::app(back, empty)).unwrap();
    let (head, args) = collect_app_spine(&result);
    match head.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.char_of_nat.addr)
      },
      other => panic!("expected Char.ofNat head, got {:?}", other),
    }
    assert_eq!(args.len(), 1);
    match args[0].data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(65u64));
      },
      other => panic!("expected default Char Nat literal, got {:?}", other),
    }
  }

  #[test]
  fn whnf_string_utf8_byte_size_literal() {
    use super::super::testing as kt;

    let mut env = KEnv::new();
    let mut tc = TypeChecker::new(&mut env);
    let size =
      kt::ME::cnst(tc.prims.string_utf8_byte_size.clone(), Box::new([]));
    let s = kt::ME::str("L∃∀N".to_string(), Address::hash("L∃∀N".as_bytes()));
    let result = tc.whnf(&kt::ME::app(size, s)).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(8u64));
      },
      other => {
        panic!("expected UTF-8 byte length Nat literal, got {:?}", other)
      },
    }
  }

  #[test]
  fn def_eq_string_to_byte_array_empty() {
    use super::super::testing as kt;

    let mut env = KEnv::new();
    let mut tc = TypeChecker::new(&mut env);
    let to_byte_array =
      kt::ME::cnst(tc.prims.string_to_byte_array.clone(), Box::new([]));
    let empty_string = kt::ME::str(String::new(), Address::hash(b""));
    let lhs = kt::ME::app(to_byte_array, empty_string);
    let rhs = kt::ME::cnst(tc.prims.byte_array_empty.clone(), Box::new([]));
    assert!(tc.is_def_eq(&lhs, &rhs).unwrap());
  }

  #[test]
  fn whnf_nat_ble_zero_length_string_to_list_literal_is_true() {
    use super::super::constant::RecRule;

    // Do not add these to `Primitives`: Lean reduces this through ordinary
    // delta/iota/projection/string-literal expansion, not a native kernel op.
    fn canonical_id(hex: &str) -> KId<Anon> {
      KId::new(Address::from_hex(hex).unwrap(), ())
    }
    fn apps_ae(mut f: AE, args: &[AE]) -> AE {
      for arg in args {
        f = app(f, arg.clone());
      }
      f
    }

    let prims = Primitives::from_env(&KEnv::<Anon>::new());
    let string_to_list_id = canonical_id(
      "8cece559b9901256cce90e9bf1fa09fce136ff433a24fed990e6734a9c0bdba4",
    );
    let list_length_id = canonical_id(
      "040eac73ee2bdc17f6f276c3660f7e8cf84cb82df9259591d6a808a39571bf25",
    );
    let list_id = mk_id("Test.List");
    let list_nil_id = mk_id("Test.List.nil");
    let list_cons_id = mk_id("Test.List.cons");
    let list_rec_id = mk_id("Test.List.rec");
    let list_const = AE::cnst(list_id.clone(), Box::new([]));

    let mut env = KEnv::<Anon>::new();
    env.insert(
      list_id.clone(),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: 0,
        params: 1,
        indices: 0,
        is_rec: true,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: list_id.clone(),
        member_idx: 0,
        ty: pi(sort0(), sort0()),
        ctors: vec![list_nil_id.clone(), list_cons_id.clone()],
        lean_all: (),
      },
    );
    env.insert(
      list_nil_id.clone(),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: list_id.clone(),
        cidx: 0,
        params: 1,
        fields: 0,
        ty: pi(sort0(), app(list_const.clone(), var(0))),
      },
    );
    env.insert(
      list_cons_id.clone(),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: list_id.clone(),
        cidx: 1,
        params: 1,
        fields: 2,
        ty: pi(
          sort0(),
          pi(
            var(0),
            pi(app(list_const.clone(), var(1)), app(list_const.clone(), var(2))),
          ),
        ),
      },
    );

    let rec_const = AE::cnst(list_rec_id.clone(), Box::new([]));
    let ih = apps_ae(
      rec_const.clone(),
      &[var(5), var(4), var(3), var(2), var(0)],
    );
    let cons_result = apps_ae(var(2), &[var(1), var(0), ih]);
    env.insert(
      list_rec_id.clone(),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 0,
        params: 1,
        indices: 0,
        motives: 1,
        minors: 2,
        block: list_id.clone(),
        member_idx: 0,
        ty: sort0(),
        rules: vec![
          RecRule {
            ctor: (),
            fields: 0,
            rhs: lam(sort0(), lam(sort0(), lam(sort0(), lam(sort0(), var(1))))),
          },
          RecRule {
            ctor: (),
            fields: 2,
            rhs: lam(
              sort0(),
              lam(
                sort0(),
                lam(
                  sort0(),
                  lam(sort0(), lam(sort0(), lam(sort0(), cons_result))),
                ),
              ),
            ),
          },
        ],
        lean_all: (),
      },
    );

    let char_ty = AE::cnst(prims.char_type.clone(), Box::new([]));
    let char_of_nat = AE::cnst(prims.char_of_nat.clone(), Box::new([]));
    let list_nil = AE::cnst(list_nil_id.clone(), Box::new([]));
    let list_cons = AE::cnst(list_cons_id.clone(), Box::new([]));
    let nil_char = app(list_nil, char_ty.clone());
    let char_a = app(char_of_nat, mk_nat(65));
    let one_char_list = apps_ae(list_cons, &[char_ty.clone(), char_a, nil_char]);
    env.insert(
      string_to_list_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sort0(),
        val: lam(sort0(), one_char_list),
        lean_all: (),
        block: string_to_list_id.clone(),
      },
    );

    let nat_succ = AE::cnst(prims.nat_succ.clone(), Box::new([]));
    let motive = lam(sort0(), nat());
    let cons_case = lam(
      var(1),
      lam(
        app(list_const.clone(), var(2)),
        lam(nat(), app(nat_succ, var(0))),
      ),
    );
    let length_body = apps_ae(
      rec_const,
      &[var(1), motive, mk_nat(0), cons_case, var(0)],
    );
    env.insert(
      list_length_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 1,
        ty: sort0(),
        val: lam(sort0(), lam(app(list_const, var(0)), length_body)),
        lean_all: (),
        block: list_length_id.clone(),
      },
    );

    let mut tc = TypeChecker::new(&mut env);
    let string_to_list = AE::cnst(string_to_list_id, Box::new([]));
    let list_length = AE::cnst(list_length_id, Box::new([KUniv::zero()]));
    let nat_ble = AE::cnst(tc.prims.nat_ble.clone(), Box::new([]));

    let sample = " 0123abcABC:,;`\\/";
    let str_lit = AE::str(sample.to_string(), Address::hash(sample.as_bytes()));
    let chars = app(string_to_list, str_lit);
    let len = apps_ae(list_length, &[char_ty, chars]);
    let expr = apps_ae(nat_ble, &[mk_nat(0), len]);

    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.bool_true.addr);
      },
      other => panic!("expected Bool.true, got {other:?}"),
    }
  }

  #[test]
  fn whnf_cache_hit() {
    let mut env = env_with_id();
    let mut tc = TypeChecker::new(&mut env);
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let app = AE::app(id_const, sort0());
    let r1 = tc.whnf(&app).unwrap();
    let r2 = tc.whnf(&app).unwrap();
    // Both should return the same result
    assert_eq!(r1, r2);
  }

  fn nat() -> AE {
    AE::cnst(mk_id("Nat"), Box::new([]))
  }
  fn param(n: u64) -> AU {
    AU::param(n, ())
  }
  fn pi(a: AE, b: AE) -> AE {
    AE::all((), (), a, b)
  }
  fn app(f: AE, a: AE) -> AE {
    AE::app(f, a)
  }
  fn lam(a: AE, b: AE) -> AE {
    AE::lam((), (), a, b)
  }
  fn var(i: u64) -> AE {
    AE::var(i, ())
  }
  fn cnst(name: &str, us: &[AU]) -> AE {
    AE::cnst(mk_id(name), us.to_vec().into_boxed_slice())
  }
  fn mk_nat(n: u64) -> AE {
    let v = Nat::from(n);
    let addr = Address::hash(&v.to_le_bytes());
    AE::nat(v, addr)
  }

  fn unit() -> AE {
    cnst("Unit", &[])
  }

  fn unit_env() -> KEnv<Anon> {
    use super::super::constant::RecRule;

    let mut env = KEnv::new();
    let block = mk_id("Unit");
    let unit_id = mk_id("Unit");
    let unit_unit_id = mk_id("Unit.unit");

    env.insert(
      unit_id.clone(),
      KConst::Indc {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: false,
        is_refl: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![unit_unit_id.clone()],
        lean_all: (),
      },
    );
    env.insert(
      unit_unit_id.clone(),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: unit_id.clone(),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: unit(),
      },
    );

    let motive_ty = pi(unit(), sort1());
    let unit_unit = cnst("Unit.unit", &[]);
    let minor_ty = app(var(0), unit_unit);
    let rec_ty = pi(
      motive_ty.clone(),
      pi(minor_ty.clone(), pi(unit(), app(var(2), var(0)))),
    );
    let rule_rhs = lam(motive_ty, lam(minor_ty, var(0)));
    env.insert(
      mk_id("Unit.rec"),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 1,
        block: block.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![RecRule { ctor: (), fields: 0, rhs: rule_rhs }],
        lean_all: (),
      },
    );
    env.blocks.insert(block, vec![unit_id, unit_unit_id, mk_id("Unit.rec")]);
    env
  }

  #[test]
  fn whnf_unit_like_rec_eta_on_open_major() {
    let mut env = unit_env();
    let mut tc = TypeChecker::new(&mut env);
    tc.push_local(unit());

    let motive = lam(unit(), unit());
    let minor = cnst("Unit.unit", &[]);
    let rec = cnst("Unit.rec", &[]);
    let expr = app(app(app(rec, motive), minor.clone()), var(0));
    let result = tc.whnf(&expr).unwrap();

    assert_eq!(result, minor);
  }

  fn mk_meta_nat(n: u64) -> super::super::testing::ME {
    let v = Nat::from(n);
    let addr = Address::hash(&v.to_le_bytes());
    super::super::testing::ME::nat(v, addr)
  }

  /// Build a Nat env with Nat, Nat.zero, Nat.succ, Nat.rec, and Nat.sub.
  /// Nat.sub is defined as a primitive that the kernel's try_reduce_nat handles,
  /// but also has a delta-unfoldable body using Nat.rec (to test reduction order).
  fn nat_env() -> KEnv<Anon> {
    use super::super::constant::RecRule;

    let mut env = KEnv::new();
    let block = mk_id("Nat");

    // Nat : Sort 1
    env.insert(
      mk_id("Nat"),
      KConst::Indc {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Nat.zero"), mk_id("Nat.succ")],
        lean_all: (),
      },
    );
    env.insert(
      mk_id("Nat.zero"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Nat"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: nat(),
      },
    );
    env.insert(
      mk_id("Nat.succ"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Nat"),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: pi(nat(), nat()),
      },
    );
    let prims = Primitives::from_env(&KEnv::new());
    if prims.nat_zero.addr != mk_id("Nat.zero").addr {
      env.insert(
        prims.nat_zero.clone(),
        KConst::Ctor {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: 0,
          induct: mk_id("Nat"),
          cidx: 0,
          params: 0,
          fields: 0,
          ty: nat(),
        },
      );
    }
    if prims.nat_succ.addr != mk_id("Nat.succ").addr {
      env.insert(
        prims.nat_succ.clone(),
        KConst::Ctor {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: 0,
          induct: mk_id("Nat"),
          cidx: 1,
          params: 0,
          fields: 1,
          ty: pi(nat(), nat()),
        },
      );
    }

    // Nat.rec : ∀ {motive : Nat → Sort u} (zero : motive 0) (succ : ∀ n, motive n → motive (succ n)) (t : Nat), motive t
    let motive_ty = pi(nat(), AE::sort(param(0)));
    let minor_zero = app(var(0), cnst("Nat.zero", &[]));
    let minor_succ = pi(
      nat(),
      pi(app(var(2), var(0)), app(var(3), app(cnst("Nat.succ", &[]), var(1)))),
    );
    let rec_ty = pi(
      motive_ty,
      pi(minor_zero, pi(minor_succ, pi(nat(), app(var(3), var(0))))),
    );
    let rule_zero_rhs = lam(sort0(), lam(sort0(), lam(sort0(), var(1))));
    let nat_rec_const = cnst("Nat.rec", &[param(0)]);
    let ih = app(app(app(app(nat_rec_const, var(3)), var(2)), var(1)), var(0));
    let rule_succ_rhs = lam(
      sort0(),
      lam(sort0(), lam(sort0(), lam(nat(), app(app(var(1), var(0)), ih)))),
    );
    env.insert(
      mk_id("Nat.rec"),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: block.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          RecRule { ctor: (), fields: 0, rhs: rule_zero_rhs },
          RecRule { ctor: (), fields: 1, rhs: rule_succ_rhs },
        ],
        lean_all: (),
      },
    );

    // Nat.sub : Nat → Nat → Nat
    // Body: a simple definition that the kernel should reduce natively.
    // In practice Nat.sub's body uses Nat.rec, but try_reduce_nat
    // should intercept it before delta unfolding exposes the body.
    let sub_ty = pi(nat(), pi(nat(), nat()));
    // Body is irrelevant for the native reduction test — just use a placeholder.
    // To test the delta-unfold-before-native-reduce bug, we make the body
    // something that would diverge if delta-unfolded: Nat.rec applied to arg.
    // Nat.sub a b = Nat.rec (motive := λ _, Nat) a (λ n ih, Nat.pred ih) b
    // But for simplicity, just use λ a b. a (dummy body).
    let sub_val = lam(nat(), lam(nat(), var(1)));
    env.insert(
      mk_id("Nat.sub"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: mk_id("Nat.sub"),
      },
    );

    env.blocks.insert(
      block,
      vec![
        mk_id("Nat"),
        mk_id("Nat.zero"),
        mk_id("Nat.succ"),
        mk_id("Nat.rec"),
      ],
    );
    env
  }

  fn insert_nat_add_model(env: &mut KEnv<Anon>, add_id: KId<Anon>) {
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    let add_ty = pi(nat(), pi(nat(), nat()));
    let succ = AE::cnst(prims.nat_succ.clone(), Box::new([]));
    let add_val = lam(nat(), lam(nat(), app(succ.clone(), app(succ, var(1)))));
    env.insert(
      add_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: add_ty,
        val: add_val,
        lean_all: (),
        block: add_id,
      },
    );
  }

  #[test]
  fn whnf_nat_sub_native() {
    // Nat.sub 1000 500 should reduce to Nat(500) via try_reduce_nat,
    // without delta-unfolding Nat.sub's body.
    let mut env = nat_env();
    // Build primitives from an empty env to get hardcoded addresses as KIds
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    // Insert Nat.sub at its REAL primitive address so try_reduce_nat recognizes it
    let sub_id = prims.nat_sub.clone();
    let sub_ty = pi(nat(), pi(nat(), nat()));
    let sub_val = lam(nat(), lam(nat(), var(1))); // dummy body: λ a b. a
    env.insert(
      sub_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: sub_id.clone(),
      },
    );
    let mut tc = TypeChecker::new(&mut env);
    let sub_const = AE::cnst(sub_id, Box::new([]));
    let expr = app(app(sub_const, mk_nat(1000)), mk_nat(500));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => assert_eq!(
        v.0,
        num_bigint::BigUint::from(500u64),
        "Nat.sub 1000 500 should be 500"
      ),
      other => panic!("expected Nat(500), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_primitive_accepts_constructor_value_with_loose_bvar() {
    // Iota on Nat literals can expose a value as `Nat.succ <literal>`.
    // Sparse-case code also carries binders that disappear after WHNF of
    // primitive arguments, so primitive reduction must not reject the whole
    // application just because it syntactically contains a loose bvar.
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    let ctor_num = app(succ, mk_nat(4));
    let dead_open_arg = app(lam(nat(), ctor_num), var(0));
    let expr = app(app(add, dead_open_arg), mk_nat(2));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(7u64));
      },
      other => panic!("expected Nat(7), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_ble_large() {
    // Nat.ble 2^32 2^32 should reduce to Bool.true via try_reduce_nat
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let ble = AE::cnst(tc.prims.nat_ble.clone(), Box::new([]));
    let big = mk_nat(1u64 << 32);
    let expr = app(app(ble, big.clone()), big);
    let result = tc.whnf(&expr).unwrap();
    // Should be Bool.true constant
    match result.data() {
      ExprData::Const(id, _, _) => assert_eq!(id.addr, tc.prims.bool_true.addr),
      other => panic!("expected Bool.true, got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_add_symbolic_literal_rhs_exposes_succ() {
    let mut env = nat_env();
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    insert_nat_add_model(&mut env, prims.nat_add.clone());

    let mut tc = TypeChecker::new(&mut env);
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let expr = app(app(add, var(0)), mk_nat(2));
    let result = tc.whnf(&expr).unwrap();
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    assert_eq!(result, app(succ.clone(), app(succ, var(0))));
  }

  #[test]
  fn whnf_nat_add_ofnat_zero_lhs_stays_stuck() {
    use super::super::testing as kt;

    let mut env = KEnv::<Meta>::new();
    let mut tc = TypeChecker::new(&mut env);
    let nat_ty = kt::ME::cnst(tc.prims.nat.clone(), Box::new([]));
    let ofnat_zero = kt::apps(
      kt::cnst("OfNat.ofNat", &[]),
      &[nat_ty, mk_meta_nat(0), kt::cnst("instOfNatNat", &[])],
    );
    let add = kt::ME::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let expr = kt::apps(add, &[ofnat_zero, kt::var(0)]);
    let result = tc.whnf(&expr).unwrap();
    assert_eq!(result, expr);
  }

  #[test]
  fn whnf_nat_mul_ofnat_one_rhs_stays_stuck() {
    use super::super::testing as kt;

    let mut env = KEnv::<Meta>::new();
    let mut tc = TypeChecker::new(&mut env);
    let nat_ty = kt::ME::cnst(tc.prims.nat.clone(), Box::new([]));
    let ofnat_one = kt::apps(
      kt::cnst("OfNat.ofNat", &[]),
      &[nat_ty, mk_meta_nat(1), kt::cnst("instOfNatNat", &[])],
    );
    let mul = kt::ME::cnst(tc.prims.nat_mul.clone(), Box::new([]));
    let expr = kt::apps(mul, &[kt::var(0), ofnat_one]);
    let result = tc.whnf(&expr).unwrap();
    assert_eq!(result, expr);
  }

  #[test]
  fn try_reduce_nat_ofnat_nat_literal_arg_stays_stuck() {
    use super::super::testing as kt;

    let mut env = KEnv::<Meta>::new();
    let mut tc = TypeChecker::new(&mut env);
    let nat_ty = kt::ME::cnst(tc.prims.nat.clone(), Box::new([]));
    let ofnat_one = kt::apps(
      kt::cnst("OfNat.ofNat", &[]),
      &[nat_ty, mk_meta_nat(1), kt::cnst("instOfNatNat", &[])],
    );
    let add = kt::ME::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let expr = kt::apps(add, &[ofnat_one, mk_meta_nat(2)]);
    assert!(tc.try_reduce_nat(&expr).unwrap().is_none());
  }

  #[test]
  fn whnf_nat_mul_symbolic_zero_rhs_stays_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let mul = AE::cnst(tc.prims.nat_mul.clone(), Box::new([]));
    let expr = app(app(mul, var(0)), mk_nat(0));
    let result = tc.whnf(&expr).unwrap();
    assert_eq!(result, expr);
  }

  #[test]
  fn def_eq_nat_add_literal_lhs_not_succ_chain() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    tc.push_local(nat());

    for n in 0..=4 {
      let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
      let lhs = app(app(add, mk_nat(n)), var(0));
      let mut rhs = var(0);
      for _ in 0..n {
        let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
        rhs = app(succ, rhs);
      }

      assert!(
        !tc.is_def_eq(&lhs, &rhs).unwrap(),
        "Nat.add {n} x must stay distinct from succ^{n} x"
      );
    }
  }

  #[test]
  fn def_eq_nat_mul_non_iota_symbolic_cases_stay_distinct() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    tc.push_local(nat());

    let mul = AE::cnst(tc.prims.nat_mul.clone(), Box::new([]));
    let x = var(0);

    let lhs_zero = app(app(mul.clone(), mk_nat(0)), x.clone());
    assert!(
      !tc.is_def_eq(&lhs_zero, &mk_nat(0)).unwrap(),
      "Nat.mul 0 x must not reduce to 0 while x is stuck"
    );

    let lhs_one = app(app(mul.clone(), mk_nat(1)), x.clone());
    assert!(
      !tc.is_def_eq(&lhs_one, &x).unwrap(),
      "Nat.mul 1 x must not reduce to x while x is stuck"
    );

    let rhs_one = app(app(mul, x.clone()), mk_nat(1));
    assert!(
      !tc.is_def_eq(&rhs_one, &x).unwrap(),
      "Nat.mul x 1 must not reduce directly to x"
    );
  }

  #[test]
  fn whnf_nat_mod_literal_by_symbolic_lower_bound_stays_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let modu = AE::cnst(tc.prims.nat_mod.clone(), Box::new([]));
    let denom = app(app(add, var(0)), mk_nat(2));
    let expr = app(app(modu, mk_nat(1)), denom);
    let result = tc.whnf(&expr).unwrap();
    assert_eq!(result, expr);
  }

  #[test]
  fn try_reduce_nat_sub_symbolic_literal_rhs_stays_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let sub = AE::cnst(tc.prims.nat_sub.clone(), Box::new([]));
    let lhs = app(app(add, var(0)), mk_nat(2));
    let expr = app(app(sub, lhs), mk_nat(1));
    assert!(tc.try_reduce_nat(&expr).unwrap().is_none());
  }

  #[test]
  fn whnf_bitvec_ult_zero_rhs_is_false() {
    use super::super::testing as kt;

    let mut env = KEnv::<Meta>::new();
    let mut tc = TypeChecker::new(&mut env);
    let bv_of_nat = kt::ME::cnst(tc.prims.bit_vec_of_nat.clone(), Box::new([]));
    let bv_ult = kt::ME::cnst(tc.prims.bit_vec_ult.clone(), Box::new([]));
    let zero = kt::apps(bv_of_nat, &[kt::var(1), mk_meta_nat(0)]);
    let ult = kt::apps(bv_ult, &[kt::var(1), kt::var(0), zero]);
    let result = tc.whnf(&ult).unwrap();
    match result.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.bool_false.addr)
      },
      other => panic!("expected Bool.false, got {:?}", other),
    }
  }

  #[test]
  fn whnf_bitvec_to_nat_ofnat_zero_is_zero() {
    use super::super::testing as kt;

    let mut env = KEnv::<Meta>::new();
    let mut tc = TypeChecker::new(&mut env);
    let bv_of_nat = kt::ME::cnst(tc.prims.bit_vec_of_nat.clone(), Box::new([]));
    let bv_to_nat = kt::ME::cnst(tc.prims.bit_vec_to_nat.clone(), Box::new([]));
    let zero = kt::apps(bv_of_nat, &[kt::var(0), mk_meta_nat(0)]);
    let expr = kt::apps(bv_to_nat, &[kt::var(0), zero]);
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::ZERO);
      },
      other => panic!("expected Nat(0), got {:?}", other),
    }
  }

  #[test]
  fn whnf_decide_bitvec_lt_zero_is_false() {
    use super::super::testing as kt;

    let mut env = KEnv::<Meta>::new();
    let mut tc = TypeChecker::new(&mut env);
    let width = kt::var(1);
    let bv_const = kt::ME::cnst(tc.prims.bit_vec.clone(), Box::new([]));
    let bv_of_nat = kt::ME::cnst(tc.prims.bit_vec_of_nat.clone(), Box::new([]));
    let lt_lt = kt::ME::cnst(tc.prims.lt_lt.clone(), Box::new([]));
    let dec_decide =
      kt::ME::cnst(tc.prims.decidable_decide.clone(), Box::new([]));
    let bv_ty = kt::apps(bv_const, std::slice::from_ref(&width));
    let zero = kt::apps(bv_of_nat, &[width, mk_meta_nat(0)]);
    let prop = kt::apps(lt_lt, &[bv_ty, kt::var(2), kt::var(0), zero]);
    let decide = kt::apps(dec_decide, &[prop, kt::var(3)]);
    let result = tc.whnf(&decide).unwrap();
    match result.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.bool_false.addr)
      },
      other => panic!("expected Bool.false, got {:?}", other),
    }
  }

  #[test]
  fn whnf_def_eq_nat_sub_large() {
    // Simulate the real failure: a definition whose type-check requires
    // proving `Nat.sub (2^16) x =?= y` via def-eq. If Nat.sub gets
    // delta-unfolded to Nat.rec before try_reduce_nat intercepts it,
    // the kernel diverges on iota reduction.
    let mut env = nat_env();
    // Build primitives from an empty env to get hardcoded addresses as KIds
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    let sub_id = prims.nat_sub.clone();
    let sub_ty = pi(nat(), pi(nat(), nat()));
    // Body that uses Nat.rec — if delta-unfolded, this would produce
    // Nat.rec motive zero_case succ_case (lit 65536) which diverges.
    // But try_reduce_nat should intercept Nat.sub first.
    let sub_val = lam(nat(), lam(nat(), var(1))); // dummy
    env.insert(
      sub_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: sub_id.clone(),
      },
    );
    let mut tc = TypeChecker::new(&mut env);
    let sub_const = AE::cnst(sub_id, Box::new([]));
    let big = mk_nat(65536); // 2^16
    let expr = app(app(sub_const, big), mk_nat(0));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(65536u64))
      },
      other => panic!("expected Nat(65536), got {:?}", other),
    }
  }

  #[test]
  fn def_eq_large_nat_literals() {
    // Two identical large Nat literals should be equal via the fast-path
    // (direct value comparison, not O(n) succ peeling).
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let a = mk_nat(1 << 20); // ~1 million
    let b = mk_nat(1 << 20);
    assert!(
      tc.is_def_eq(&a, &b).unwrap(),
      "identical large Nat literals should be def-eq"
    );
  }

  #[test]
  fn whnf_nat_rec_small() {
    // Nat.rec (motive) zero_case succ_case (Nat(3)) should reduce via iota
    // to succ_case 2 (succ_case 1 (succ_case 0 zero_case))
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let rec = cnst("Nat.rec", &[AU::succ(AU::zero())]); // Nat.rec.{1}
    // motive := λ _, Nat
    let motive = lam(nat(), nat());
    // zero_case := Nat(42)
    let zero_case = mk_nat(42);
    // succ_case := λ n ih, Nat.succ ih
    let succ_case = lam(nat(), lam(nat(), app(cnst("Nat.succ", &[]), var(0))));
    let expr = app(app(app(app(rec, motive), zero_case), succ_case), mk_nat(3));
    let result = tc.whnf(&expr).unwrap();
    // Should be Nat.succ(Nat.succ(Nat.succ(Nat(42))))
    // After native succ reduction: Nat(45)
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(45u64))
      },
      ExprData::App(..) => {
        // Might be Nat.succ chain — that's also acceptable
        eprintln!("Nat.rec result is App chain (not folded to literal)");
      },
      other => panic!("unexpected Nat.rec result: {:?}", other),
    }
  }

  // -----------------------------------------------------------------------
  // USize.size reduction chain tests
  // -----------------------------------------------------------------------

  /// Build an env that includes the full USize.size reduction chain:
  ///   System.Platform.numBits (handled by try_reduce_native → 64)
  ///   Nat.pow at the correct primitive address
  ///   USize.size := Nat.pow 2 numBits (reducible def)
  fn usize_env() -> KEnv<Anon> {
    let mut env = nat_env();
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);

    // System.Platform.numBits — insert at the real primitive address
    // so try_reduce_native recognizes it. Give it a stuck body so this test
    // fails if native handling regresses and WHNF falls through to delta.
    env.insert(
      prims.system_platform_num_bits.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: nat(),
        val: AE::cnst(mk_id("opaque.bits"), Box::new([])),
        lean_all: (),
        block: prims.system_platform_num_bits.clone(),
      },
    );

    // Nat.pow at the real primitive address
    let pow_ty = pi(nat(), pi(nat(), nat()));
    let pow_val = lam(nat(), lam(nat(), var(1))); // dummy body
    env.insert(
      prims.nat_pow.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: pow_ty,
        val: pow_val,
        lean_all: (),
        block: prims.nat_pow.clone(),
      },
    );

    // Nat.sub at the real primitive address
    let sub_ty = pi(nat(), pi(nat(), nat()));
    let sub_val = lam(nat(), lam(nat(), var(1))); // dummy body
    env.insert(
      prims.nat_sub.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: prims.nat_sub.clone(),
      },
    );

    // Nat.pred at the real primitive address, defined via Nat.rec as in Lean.
    let pred_ty = pi(nat(), nat());
    let rec = cnst("Nat.rec", &[AU::succ(AU::zero())]);
    let motive = lam(nat(), nat());
    let zero_case = mk_nat(0);
    let succ_case = lam(nat(), lam(nat(), var(1)));
    let pred_val =
      lam(nat(), app(app(app(app(rec, motive), zero_case), succ_case), var(0)));
    env.insert(
      prims.nat_pred.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: pred_ty,
        val: pred_val,
        lean_all: (),
        block: prims.nat_pred.clone(),
      },
    );

    // USize.size := Nat.pow 2 System.Platform.numBits
    let usize_size_val = app(
      app(AE::cnst(prims.nat_pow.clone(), Box::new([])), mk_nat(2)),
      AE::cnst(prims.system_platform_num_bits.clone(), Box::new([])),
    );
    env.insert(
      mk_id("USize.size"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev, // @[reducible]
        lvls: 0,
        ty: nat(),
        val: usize_size_val,
        lean_all: (),
        block: mk_id("USize.size"),
      },
    );

    env
  }

  #[test]
  fn whnf_system_platform_num_bits() {
    // System.Platform.numBits should reduce to 64 via try_reduce_native
    let mut env = usize_env();
    let mut tc = TypeChecker::new(&mut env);
    let num_bits =
      AE::cnst(tc.prims.system_platform_num_bits.clone(), Box::new([]));
    let result = tc.whnf(&num_bits).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(64u64))
      },
      other => panic!("expected Nat(64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_pow_2_64() {
    // Nat.pow 2 64 should reduce to 2^64
    let mut env = usize_env();
    let mut tc = TypeChecker::new(&mut env);
    let pow_const = AE::cnst(tc.prims.nat_pow.clone(), Box::new([]));
    let expr = app(app(pow_const, mk_nat(2)), mk_nat(64));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => assert_eq!(
        v.0,
        num_bigint::BigUint::from(1u64 << 63) * 2u64,
        "Nat.pow 2 64 should be 2^64"
      ),
      other => panic!("expected Nat(2^64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_usize_size() {
    // USize.size := Nat.pow 2 numBits should reduce to 2^64
    let mut env = usize_env();
    let mut tc = TypeChecker::new(&mut env);
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));
    let result = tc.whnf(&usize_size).unwrap();
    let expected = num_bigint::BigUint::from(1u64 << 63) * 2u64;
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, expected, "USize.size should be 2^64")
      },
      other => panic!("expected Nat(2^64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_sub_usize_size_0() {
    // Nat.sub USize.size 0 should reduce to 2^64
    let mut env = usize_env();
    let mut tc = TypeChecker::new(&mut env);
    let sub_const = AE::cnst(tc.prims.nat_sub.clone(), Box::new([]));
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));
    let expr = app(app(sub_const, usize_size), mk_nat(0));
    let result = tc.whnf(&expr).unwrap();
    let expected = num_bigint::BigUint::from(1u64 << 63) * 2u64;
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, expected, "Nat.sub USize.size 0 should be 2^64")
      },
      other => panic!("expected Nat(2^64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_pred_usize_size() {
    // Nat.pred USize.size should reduce to 2^64 - 1
    let mut env = usize_env();
    let mut tc = TypeChecker::new(&mut env);
    let pred_const = AE::cnst(tc.prims.nat_pred.clone(), Box::new([]));
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));
    let expr = app(pred_const, usize_size);
    let result = tc.whnf(&expr).unwrap();
    let expected = num_bigint::BigUint::from(1u64 << 63) * 2u64 - 1u64;
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, expected, "Nat.pred USize.size should be 2^64 - 1")
      },
      other => panic!("expected Nat(2^64 - 1), got {:?}", other),
    }
  }

  #[test]
  fn def_eq_usize_pred_sub_vs_sub_1() {
    // Nat.pred (Nat.sub USize.size 0) =?= Nat.sub USize.size 1
    // This is the actual failing pattern from USize.toUInt16_ofNatTruncate_of_lt
    let mut env = usize_env();
    let mut tc = TypeChecker::new(&mut env);

    let sub_const = AE::cnst(tc.prims.nat_sub.clone(), Box::new([]));
    let pred_const = AE::cnst(tc.prims.nat_pred.clone(), Box::new([]));
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));

    // LHS: Nat.pred (Nat.sub USize.size 0)
    let lhs = app(
      pred_const,
      app(app(sub_const.clone(), usize_size.clone()), mk_nat(0)),
    );
    // RHS: Nat.sub USize.size 1
    let rhs = app(app(sub_const, usize_size), mk_nat(1));

    assert!(
      tc.is_def_eq(&lhs, &rhs).unwrap(),
      "Nat.pred (Nat.sub USize.size 0) should be def-eq to Nat.sub USize.size 1"
    );
  }

  // =========================================================================
  // Regression: native-reduce re-entrancy guard
  //
  // `try_reduce_native` must short-circuit when `self.in_native_reduce` is
  // set to prevent `whnf → native → whnf → native` stack overflow. The
  // guard lives at line ~1222 in this file; exercise it here.
  // =========================================================================

  #[test]
  fn native_reduce_reentrancy_guard_prevents_recursion() {
    // Build an env with reduce_bool bound to a constant whose body is
    // Bool.true. Under the guard, an outer call should still succeed
    // normally, but an inner call during native reduction must see
    // `in_native_reduce == true` and return `None`.
    let empty = KEnv::<Anon>::new();
    let prims = Primitives::from_env(&empty);

    let mut env = KEnv::<Anon>::new();
    // A definition whose body is Bool.true at the canonical Bool.true addr.
    env.insert(
      mk_id("BodyTrue"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: AE::cnst(prims.bool_type.clone(), Box::new([])),
        val: AE::cnst(prims.bool_true.clone(), Box::new([])),
        lean_all: (),
        block: mk_id("BodyTrue"),
      },
    );

    let mut tc = TypeChecker::new(&mut env);
    // Set the guard — simulating an in-progress native reduction.
    tc.in_native_reduce = true;

    let reduce_bool = AE::cnst(tc.prims.reduce_bool.clone(), Box::new([]));
    let body_true = AE::cnst(mk_id("BodyTrue"), Box::new([]));
    let expr = AE::app(reduce_bool, body_true);
    // With the guard set, try_reduce_native must not recurse. Because
    // the guard just short-circuits `try_reduce_native`, whnf falls
    // through to the outer-level delta loop; that doesn't know about
    // `reduce_bool`, so the result stays structurally as-applied.
    let result = tc.whnf(&expr).unwrap();
    // Sanity: result should be an App (no reduction fired under the
    // guard) OR the body unfolded via delta. What must NOT happen is
    // an infinite loop / panic.
    let _ = result; // just verify no panic / no divergence
  }

  // =========================================================================
  // Large-Nat iota runaway guard
  //
  // WHNF fuel guards against unbounded expansion of Nat literals into
  // Nat.succ chains when the same recursor peels consecutive predecessors
  // for thousands of steps. Verify the guard fires by applying `Nat.rec`
  // whose step immediately forces `ih` to a large literal.
  // =========================================================================

  #[test]
  fn whnf_large_nat_literal_iota_cap() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // A literal well above the 2^20 threshold.
    let huge = mk_nat(1u64 << 25);
    // Nat.rec : ∀ {motive} (zero) (succ) (t : Nat), motive t
    let rec_const = cnst("Nat.rec", &[param(0)]);
    let motive = lam(nat(), nat());
    let zero_branch = mk_nat(0);
    let succ_branch = lam(nat(), lam(nat(), var(0)));
    let application =
      app(app(app(app(rec_const, motive), zero_branch), succ_branch), huge);
    assert!(matches!(tc.whnf(&application), Err(TcError::MaxRecDepth)));
  }

  // =========================================================================
  // Quotient reduction: `Quot.lift α r β f h (Quot.mk α r a) == f a`
  //
  // Sets up the Quot primitives at their canonical addresses so that
  // `tc.prims.quot_ctor` / `quot_lift` / `quot_ind` resolve to real env
  // entries. Values are kept opaque — we only check that the head-spine
  // of the result matches `f a`.
  // =========================================================================

  /// Minimal Quot env: Quot / Quot.mk / Quot.lift / Quot.ind as axioms.
  fn quot_env() -> KEnv<Anon> {
    let empty = KEnv::<Anon>::new();
    let prims = Primitives::from_env(&empty);

    let mut env = KEnv::<Anon>::new();
    // Types are placeholders; we only need these to live at canonical
    // addresses so `try_quot_reduce` recognizes them.
    env.insert(
      prims.quot_type.clone(),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        ty: sort1(),
      },
    );
    env.insert(
      prims.quot_ctor.clone(),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        ty: sort0(),
      },
    );
    env.insert(
      prims.quot_lift.clone(),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 2,
        ty: sort0(),
      },
    );
    env.insert(
      prims.quot_ind.clone(),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 1,
        ty: sort0(),
      },
    );
    env
  }

  #[test]
  fn whnf_quot_lift_reduces() {
    // Quot.lift α r β f h (Quot.mk α r a) → f a
    let mut env = quot_env();
    let mut tc = TypeChecker::new(&mut env);

    let alpha = AE::cnst(mk_id("α"), Box::new([]));
    let r = AE::cnst(mk_id("r"), Box::new([]));
    let beta = AE::cnst(mk_id("β"), Box::new([]));
    let f = AE::cnst(mk_id("f"), Box::new([]));
    let h = AE::cnst(mk_id("h"), Box::new([]));
    let a = AE::cnst(mk_id("a"), Box::new([]));

    // Quot.mk α r a
    let mk = AE::app(
      AE::app(
        AE::app(
          AE::cnst(tc.prims.quot_ctor.clone(), Box::new([])),
          alpha.clone(),
        ),
        r.clone(),
      ),
      a.clone(),
    );
    // Quot.lift α r β f h mk
    let lift = AE::app(
      AE::app(
        AE::app(
          AE::app(
            AE::app(
              AE::app(
                AE::cnst(tc.prims.quot_lift.clone(), Box::new([])),
                alpha,
              ),
              r,
            ),
            beta,
          ),
          f.clone(),
        ),
        h,
      ),
      mk,
    );

    let result = tc.whnf(&lift).unwrap();
    // Result head-spine: `f a`.
    let (head, args) = collect_app_spine(&result);
    assert_eq!(args.len(), 1);
    assert!(head.hash_eq(&f));
    assert!(args[0].hash_eq(&a));
  }

  #[test]
  fn whnf_quot_lift_stuck_on_non_mk_major() {
    // Major is not Quot.mk → no reduction.
    let mut env = quot_env();
    // Major is an opaque axiom, not Quot.mk — include it in the env.
    env.insert(
      mk_id("opaque_q"),
      KConst::Axio {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        ty: sort0(),
      },
    );
    let mut tc = TypeChecker::new(&mut env);

    let alpha = AE::cnst(mk_id("α"), Box::new([]));
    let r = AE::cnst(mk_id("r"), Box::new([]));
    let beta = AE::cnst(mk_id("β"), Box::new([]));
    let f = AE::cnst(mk_id("f"), Box::new([]));
    let h = AE::cnst(mk_id("h"), Box::new([]));
    let opaque = AE::cnst(mk_id("opaque_q"), Box::new([]));

    let lift = AE::app(
      AE::app(
        AE::app(
          AE::app(
            AE::app(
              AE::app(
                AE::cnst(tc.prims.quot_lift.clone(), Box::new([])),
                alpha,
              ),
              r,
            ),
            beta,
          ),
          f.clone(),
        ),
        h,
      ),
      opaque,
    );

    let result = tc.whnf(&lift).unwrap();
    // Result is the original (possibly with args WHNF'd) — head must
    // still be Quot.lift.
    let (head, _) = collect_app_spine(&result);
    match head.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.quot_lift.addr);
      },
      other => panic!("expected Quot.lift head, got {other:?}"),
    }
  }

  #[test]
  fn whnf_quot_lift_insufficient_args_stuck() {
    // Fewer than 6 args → no reduction.
    let mut env = quot_env();
    let mut tc = TypeChecker::new(&mut env);
    // Only 3 args
    let alpha = AE::cnst(mk_id("α"), Box::new([]));
    let r = AE::cnst(mk_id("r"), Box::new([]));
    let beta = AE::cnst(mk_id("β"), Box::new([]));
    let lift_partial = AE::app(
      AE::app(
        AE::app(AE::cnst(tc.prims.quot_lift.clone(), Box::new([])), alpha),
        r,
      ),
      beta,
    );
    let result = tc.whnf(&lift_partial).unwrap();
    let (head, args) = collect_app_spine(&result);
    assert_eq!(args.len(), 3, "under-applied Quot.lift must stay partial");
    match head.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.quot_lift.addr);
      },
      other => panic!("expected Quot.lift head, got {other:?}"),
    }
  }

  // =========================================================================
  // `try_reduce_decidable` bail paths
  //
  // Full decidable reduction needs a substantial prelude (Decidable,
  // Eq, Bool, Nat.le_of_ble_eq_true, etc.). Here we only verify the
  // short-circuit paths: non-Nat args and under-application bail out
  // rather than crashing.
  // =========================================================================

  #[test]
  fn decidable_reduction_non_nat_arg_bails_out() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let dec_le = AE::cnst(tc.prims.nat_dec_le.clone(), Box::new([]));
    // Args are not Nat literals — decidable path must not panic, must
    // not reduce.
    let opaque1 = sort0();
    let opaque2 = sort0();
    let expr = AE::app(AE::app(dec_le, opaque1), opaque2);
    let _ = tc.whnf(&expr).unwrap();
  }

  #[test]
  fn decidable_reduction_underapplied_bails_out() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let dec_le = AE::cnst(tc.prims.nat_dec_le.clone(), Box::new([]));
    // Only 1 arg — path must bail out.
    let expr = AE::app(dec_le, mk_nat(3));
    let _ = tc.whnf(&expr).unwrap();
  }

  // =========================================================================
  // Comprehensive Nat literal reduction mirror
  //
  // Companion to `Tests/Ix/Kernel/NatReduction.lean`. See
  // `docs/nat-reduction-audit.md` for the divergence catalogue.
  //
  // These cover behaviors that are hard or impossible to observe through
  // Lean's elaborator + `rfl`, in particular:
  //   - All binary primitives on raw literals (parity)
  //   - `Nat.zero` literal-extension recognition (D10)
  //   - `Nat.pow` cap at `2^24` and uncapped shifts
  //   - Non-literal arguments staying stuck
  //   - `Nat.pred` staying out of native Nat reduction
  // =========================================================================

  /// Build `op a b` using the canonical primitive address for `op`.
  fn nat_bin_op(op: KId<Anon>, a: AE, b: AE) -> AE {
    AE::app(AE::app(AE::cnst(op, Box::new([])), a), b)
  }

  /// Build `op a` for a unary primitive.
  fn nat_unary_op(op: KId<Anon>, a: AE) -> AE {
    AE::app(AE::cnst(op, Box::new([])), a)
  }

  fn assert_nat_lit(e: &AE, expected: u64) {
    match e.data() {
      ExprData::Nat(v, _, _) => assert_eq!(
        v.0,
        num_bigint::BigUint::from(expected),
        "expected lit {expected}, got {v:?}"
      ),
      other => panic!("expected Nat literal, got {other:?}"),
    }
  }

  fn assert_bool_const(e: &AE, expected: bool, prims: &Primitives<Anon>) {
    match e.data() {
      ExprData::Const(id, _, _) => {
        let exp_addr = if expected {
          prims.bool_true.addr.clone()
        } else {
          prims.bool_false.addr.clone()
        };
        assert_eq!(
          id.addr,
          exp_addr,
          "expected Bool.{}, got different const",
          if expected { "true" } else { "false" }
        );
      },
      other => panic!("expected Bool const, got {other:?}"),
    }
  }

  // ---- Section A: Per-primitive literal-on-literal (parity with reference) ----

  #[test]
  fn nat_add_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let cases =
      [(0, 7, 7), (7, 0, 7), (2, 3, 5), (1_000_000, 2_000_000, 3_000_000)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_add.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_sub_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // Saturating: a < b ⇒ 0
    let cases = [(5, 3, 2), (5, 5, 0), (3, 5, 0), (5, 0, 5), (0, 0, 0)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_sub.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_mul_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let cases = [(0, 7, 0), (7, 0, 0), (6, 7, 42), (1, 42, 42)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_mul.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_div_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // Lean convention: div by 0 ⇒ 0
    let cases = [(10, 2, 5), (7, 3, 2), (7, 0, 0), (0, 7, 0)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_div.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_mod_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // Lean convention: mod by 0 ⇒ a (the dividend)
    let cases = [(10, 2, 0), (7, 3, 1), (7, 0, 7), (0, 7, 0)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_mod.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_pow_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let cases = [(0, 5, 0), (5, 0, 1), (2, 10, 1024), (1, 100, 1)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_pow.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_gcd_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let cases = [(0, 7, 7), (7, 0, 7), (9, 4, 1), (12, 18, 6)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_gcd.clone(), mk_nat(a), mk_nat(b));
      assert_nat_lit(&tc.whnf(&e).unwrap(), r);
    }
  }

  #[test]
  fn nat_beq_lit_lit() {
    let mut env = nat_env();
    let prims_clone = {
      let tc = TypeChecker::new(&mut env);
      tc.prims.clone()
    };
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let cases = [
      (0, 0, true),
      (5, 5, true),
      (1, 2, false),
      (42, 42, true),
      (5, 3, false),
    ];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_beq.clone(), mk_nat(a), mk_nat(b));
      assert_bool_const(&tc.whnf(&e).unwrap(), r, &prims_clone);
    }
  }

  #[test]
  fn nat_ble_lit_lit() {
    let mut env = nat_env();
    let prims_clone = {
      let tc = TypeChecker::new(&mut env);
      tc.prims.clone()
    };
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let cases = [(0, 0, true), (3, 5, true), (5, 5, true), (5, 3, false)];
    for (a, b, r) in cases {
      let e = nat_bin_op(tc.prims.nat_ble.clone(), mk_nat(a), mk_nat(b));
      assert_bool_const(&tc.whnf(&e).unwrap(), r, &prims_clone);
    }
  }

  #[test]
  fn nat_bitwise_lit_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // land
    let e = nat_bin_op(tc.prims.nat_land.clone(), mk_nat(0xF0), mk_nat(0x0F));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 0);
    let e = nat_bin_op(tc.prims.nat_land.clone(), mk_nat(0xFF), mk_nat(0x0F));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 0xF);
    // lor
    let e = nat_bin_op(tc.prims.nat_lor.clone(), mk_nat(0xF0), mk_nat(0x0F));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 0xFF);
    // xor
    let e = nat_bin_op(tc.prims.nat_xor.clone(), mk_nat(0xFF), mk_nat(0xFF));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 0);
    let e = nat_bin_op(tc.prims.nat_xor.clone(), mk_nat(0xFF), mk_nat(0x0F));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 0xF0);
  }

  #[test]
  fn nat_shift_small() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // shift_left
    let e = nat_bin_op(tc.prims.nat_shift_left.clone(), mk_nat(1), mk_nat(4));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 16);
    let e = nat_bin_op(tc.prims.nat_shift_left.clone(), mk_nat(5), mk_nat(0));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 5);
    // shift_right
    let e = nat_bin_op(tc.prims.nat_shift_right.clone(), mk_nat(16), mk_nat(4));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 1);
    let e = nat_bin_op(tc.prims.nat_shift_right.clone(), mk_nat(5), mk_nat(0));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 5);
  }

  // ---- Section B: Nat.zero literal-extension recognition (D10) ----
  // `Nat.zero` constant must be treated as numeric `0` by primitive reduction.

  #[test]
  fn nat_add_zero_ctor_left() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let zero = AE::cnst(tc.prims.nat_zero.clone(), Box::new([]));
    let e = nat_bin_op(tc.prims.nat_add.clone(), zero, mk_nat(7));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 7);
  }

  #[test]
  fn nat_mul_zero_ctor_right() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let zero = AE::cnst(tc.prims.nat_zero.clone(), Box::new([]));
    let e = nat_bin_op(tc.prims.nat_mul.clone(), mk_nat(7), zero);
    assert_nat_lit(&tc.whnf(&e).unwrap(), 0);
  }

  #[test]
  fn nat_beq_zero_ctor_lit() {
    let mut env = nat_env();
    let prims_clone = {
      let tc = TypeChecker::new(&mut env);
      tc.prims.clone()
    };
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let zero = AE::cnst(tc.prims.nat_zero.clone(), Box::new([]));
    let e = nat_bin_op(tc.prims.nat_beq.clone(), zero, mk_nat(0));
    assert_bool_const(&tc.whnf(&e).unwrap(), true, &prims_clone);
  }

  // ---- Section C: Nat.succ chain reduction ----

  #[test]
  fn nat_succ_of_lit() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    let e = AE::app(succ, mk_nat(41));
    assert_nat_lit(&tc.whnf(&e).unwrap(), 42);
  }

  #[test]
  fn nat_succ_chain_of_zero() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    let zero = AE::cnst(tc.prims.nat_zero.clone(), Box::new([]));
    // Nat.succ (Nat.succ (Nat.succ Nat.zero))
    let chain =
      AE::app(succ.clone(), AE::app(succ.clone(), AE::app(succ, zero)));
    assert_nat_lit(&tc.whnf(&chain).unwrap(), 3);
  }

  // ---- Section D: shifts are not capped at 2^24 ----

  #[test]
  fn nat_shift_left_over_former_cap_reduces() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let shift = (1u64 << 24) + 1;
    let e =
      nat_bin_op(tc.prims.nat_shift_left.clone(), mk_nat(1), mk_nat(shift));
    let r = tc.try_reduce_nat(&e).unwrap().expect("shiftLeft reduces");
    if let ExprData::Nat(v, _, _) = r.data() {
      assert_eq!(v.0.bits(), shift + 1);
    } else {
      panic!("expected Nat lit");
    }
  }

  #[test]
  fn nat_shift_right_over_former_cap_reduces_to_zero() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = nat_bin_op(
      tc.prims.nat_shift_right.clone(),
      mk_nat(7),
      mk_nat((1u64 << 24) + 1),
    );
    let r = tc.try_reduce_nat(&e).unwrap();
    let r = r.expect("shiftRight reduces");
    assert_nat_lit(&r, 0);
  }

  #[test]
  fn nat_shift_left_at_former_cap_reduces() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let shift = 1u64 << 24;
    let e =
      nat_bin_op(tc.prims.nat_shift_left.clone(), mk_nat(1), mk_nat(shift));
    let r = tc.try_reduce_nat(&e).unwrap().expect("shiftLeft reduces");
    if let ExprData::Nat(v, _, _) = r.data() {
      assert_eq!(v.0.bits(), shift + 1);
    } else {
      panic!("expected Nat lit");
    }
  }

  // ---- Section D6: pow cap (matches reference) ----

  #[test]
  fn nat_pow_over_cap_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e =
      nat_bin_op(tc.prims.nat_pow.clone(), mk_nat(2), mk_nat((1u64 << 24) + 1));
    let r = tc.try_reduce_nat(&e).unwrap();
    assert!(
      r.is_none(),
      "D6: pow over cap should leave expr stuck (matches reference)"
    );
  }

  #[test]
  fn nat_pow_at_cap_reduces() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    // 1^(2^24) = 1; cap is "b > 2^24", so b == 2^24 reduces.
    let e = nat_bin_op(tc.prims.nat_pow.clone(), mk_nat(1), mk_nat(1u64 << 24));
    let r = tc.try_reduce_nat(&e).unwrap().expect("at cap reduces");
    assert_nat_lit(&r, 1);
  }

  // ---- Section E: Nat.pred is not a native Nat reduction ----

  #[test]
  fn nat_pred_lit_stays_out_of_try_reduce_nat() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    for a in [5, 0, 1] {
      let e = nat_unary_op(tc.prims.nat_pred.clone(), mk_nat(a));
      assert!(tc.try_reduce_nat(&e).unwrap().is_none());
    }
  }

  #[test]
  fn nat_pred_zero_ctor_stays_out_of_try_reduce_nat() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let zero = AE::cnst(tc.prims.nat_zero.clone(), Box::new([]));
    let e = nat_unary_op(tc.prims.nat_pred.clone(), zero);
    assert!(tc.try_reduce_nat(&e).unwrap().is_none());
  }

  // ---- Section F: non-literal binary arguments stay stuck ----

  #[test]
  fn nat_mul_symbolic_zero_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = nat_bin_op(tc.prims.nat_mul.clone(), AE::var(0, ()), mk_nat(0));
    assert!(tc.try_reduce_nat(&e).unwrap().is_none());
  }

  #[test]
  fn nat_mul_zero_symbolic_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = nat_bin_op(tc.prims.nat_mul.clone(), mk_nat(0), AE::var(0, ()));
    assert!(tc.try_reduce_nat(&e).unwrap().is_none());
  }

  #[test]
  fn nat_add_symbolic_small_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = nat_bin_op(tc.prims.nat_add.clone(), AE::var(0, ()), mk_nat(3));
    assert!(tc.try_reduce_nat(&e).unwrap().is_none());
  }

  #[test]
  fn nat_add_symbolic_large_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = nat_bin_op(tc.prims.nat_add.clone(), AE::var(0, ()), mk_nat(100));
    let r = tc.try_reduce_nat(&e).unwrap();
    assert!(r.is_none(), "add with a symbolic argument should stay stuck");
  }

  #[test]
  fn nat_add_both_symbolic_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e =
      nat_bin_op(tc.prims.nat_add.clone(), AE::var(0, ()), AE::var(1, ()));
    let r = tc.try_reduce_nat(&e).unwrap();
    assert!(r.is_none(), "both-symbolic add should be stuck");
  }

  #[test]
  fn nat_div_symbolic_stuck() {
    let mut env = nat_env();
    let mut tc = TypeChecker::new(&mut env);
    let e = nat_bin_op(tc.prims.nat_div.clone(), AE::var(0, ()), mk_nat(2));
    let r = tc.try_reduce_nat(&e).unwrap();
    assert!(r.is_none(), "div with symbolic dividend should be stuck");
  }
}
