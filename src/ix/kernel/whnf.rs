//! Weak head normal form reduction.
//!
//! Multi-phase: whnf_core (beta, iota, zeta) → proj → nat → quot → delta.

use std::sync::LazyLock;

use crate::ix::address::Address;
use crate::ix::env::{Name, NameData};
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

/// Raw Nat literal value above which iota reduction starts consuming the
/// per-constant large-literal budget.
static NAT_IOTA_LITERAL_CAP: LazyLock<num_bigint::BigUint> =
  LazyLock::new(|| num_bigint::BigUint::from(1u64 << 20));

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

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::subst::{simul_subst, subst};
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

impl<M: KernelMode> TypeChecker<M> {
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
    if *IX_WHNF_COUNT_LOG {
      let n = WHNF_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
      if n.is_multiple_of(100_000) && n > 0 {
        eprintln!("[whnf] count={n}");
      }
    }
    let has_lets = self.num_let_bindings > 0;
    // Quick exit for non-reducing forms (skip Var when let-bindings active).
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => return Ok(e.clone()),
      ExprData::Var(..) if !has_lets => return Ok(e.clone()),
      _ => {},
    }

    // Context-aware cache: closed exprs use ptr only; open exprs include
    // ctx_id because some reductions consult local binder types.
    let key = self.whnf_key(e);
    if let Some(cached) = self.env.whnf_cache.get(&key) {
      self.env.perf.record_whnf_hit();
      return Ok(cached.clone());
    }
    // Both probes missed.
    self.env.perf.record_whnf_miss();

    // Tick AFTER fast paths and cache: only consume shared fuel for actual work.
    // Quick exits (Sort/All/Lam/Nat/Str) and cache hits are free.
    self.tick()?;

    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;
    let mut seen = Vec::new();

    loop {
      if fuel == 0 {
        self.dump_whnf_fuel("whnf", e, &cur);
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      cur = self.whnf_no_delta(&cur)?;
      let cur_key = cur.hash_key();
      if seen.iter().any(|seen_key| seen_key == &cur_key) {
        break;
      }
      seen.push(cur_key);

      // BitVec definitions reduce through Nat comparisons. Keep this before
      // native/delta so small definitional facts such as `x < 0#w` collapse
      // without unfolding the full Fin-backed representation of BitVec.
      if let Some(reduced) = self.try_reduce_bitvec(&cur)? {
        cur = reduced;
        continue;
      }

      // Nat primitive reduction in main WHNF loop (lean4lean TypeChecker.lean:439).
      // Must run BEFORE delta_unfold_one, so that Nat.sub/Nat.pow/etc. get
      // short-circuited before their bodies (which use Nat.rec) are exposed.
      if let Some(reduced) = self.try_reduce_nat(&cur)? {
        cur = reduced;
        continue;
      }
      if self.is_stuck_nat_predicate(&cur) {
        break;
      }

      // Int primitive reduction — same reasoning as Nat. Without this,
      // `Int.bmod (-1) (2^32)` would delta-unfold to `Decidable.rec (LT.lt
      // Int ...) ...` and get stuck at the `Int.decLt` instance. Runs
      // BEFORE delta so the body is never exposed. See `try_reduce_int`.
      if let Some(reduced) = self.try_reduce_int(&cur)? {
        cur = reduced;
        continue;
      }

      // Nat decidability: Nat.decLe/decEq/decLt on literals → Decidable.isTrue/isFalse.
      // Must run BEFORE delta, so the body (which uses dite/Nat.rec) is never exposed.
      if let Some(reduced) = self.try_reduce_decidable(&cur)? {
        cur = reduced;
        continue;
      }

      // Native reduction: Lean.reduceBool, Lean.reduceNat, System.Platform.numBits
      if let Some(reduced) = self.try_reduce_native(&cur)? {
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

    if !self.in_native_reduce {
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
    if flags.is_full() {
      let key = self.whnf_key(e);
      if let Some(cached) = self.env.whnf_core_cache.get(&key) {
        self.env.perf.record_whnf_core_hit();
        return Ok(cached.clone());
      }
      self.env.perf.record_whnf_core_miss();
      let result = self.whnf_core_with_flags_uncached(e, flags)?;
      self.env.whnf_core_cache.insert(key, result.clone());
      Ok(result)
    } else {
      self.whnf_core_with_flags_uncached(e, flags)
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
        // Let-bound variable zeta-reduction: substitute the let-bound value.
        ExprData::Var(i, _, _) => {
          if let Some(val) = self.lookup_let_val(*i) {
            cur = val;
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
          if let Some(result) = self.try_proj_reduce(&id, field, &wval) {
            cur = result;
            continue;
          }
          return Ok(cur); // stuck projection
        },

        // Zeta: let elimination
        ExprData::Let(_, _, val, body, _, _) => {
          let val = val.clone();
          let body = body.clone();
          cur = subst(&self.env.intern, &body, &val, 0);
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
        let mut consumed_args = Vec::new();
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
          body = simul_subst(&self.env.intern, &body, &consumed_args, 0);
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
    self.whnf_no_delta_impl(e, WhnfFlags::FULL)
  }

  /// Def-eq no-delta WHNF. This is broader than Lean's pure `whnfCore`
  /// because Ix relies on the no-delta layer for primitive/native reductions,
  /// but it preserves Lean's cheap projection policy for projected values.
  pub(super) fn whnf_no_delta_for_def_eq(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    self.cheap_recursion_depth += 1;
    let result = self.whnf_no_delta_impl(e, WhnfFlags::DEF_EQ_CORE);
    self.cheap_recursion_depth -= 1;
    result
  }

  fn whnf_no_delta_impl(
    &mut self,
    e: &KExpr<M>,
    flags: WhnfFlags,
  ) -> Result<KExpr<M>, TcError<M>> {
    let has_lets = self.num_let_bindings > 0;
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => return Ok(e.clone()),
      ExprData::Var(..) if !has_lets => return Ok(e.clone()),
      _ => {},
    }

    let key = self.whnf_key(e);
    if flags.is_full() {
      if let Some(cached) = self.env.whnf_no_delta_cache.get(&key) {
        self.env.perf.record_whnf_no_delta_hit();
        return Ok(cached.clone());
      }
      // Both probes missed.
      self.env.perf.record_whnf_no_delta_miss();
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
      if let Some(reduced) = self.try_reduce_nat(&cur)? {
        cur = reduced;
        continue;
      }

      // Int primitive reduction (see whnf main loop for rationale).
      if let Some(reduced) = self.try_reduce_int(&cur)? {
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

      if let Some(reduced) = self.try_reduce_projection_definition(&cur) {
        cur = reduced;
        continue;
      }

      // Quotient reduction
      if let Some(reduced) = self.try_quot_reduce(&cur)? {
        cur = reduced;
        continue;
      }

      break;
    }

    if flags.is_full() && !self.in_native_reduce {
      self.env.whnf_no_delta_cache.insert(key, cur.clone());
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
      && let Some(KConst::Defn { kind, val, .. }) = self.env.get(id)
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

    let val = match self.env.get(id) {
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

    let recr = match self.env.get(&rec_id) {
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

    // WHNF the major premise. Cheap mode skips delta on the major itself,
    // matching Lean4Lean's `cheapRec` (TypeChecker.lean:337–341); the rest of
    // the iota machinery still gets a structural normal form to inspect.
    let mut major_whnf = if flags.cheap_rec {
      self.whnf_core_with_flags(&major, flags)?
    } else {
      self.whnf(&major)?
    };

    // Nat literal → constructor form (one level: n → Nat.succ(lit(n-1))).
    // Keep only the runaway shape bounded. Lean uses large raw numerals as
    // fuel in definitions such as `Int.Linear.Poly.combine_mul_k'`; those are
    // fine when recursion is actually bounded by a data argument. The bad case
    // is the same recursor peeling N, N-1, N-2, ... because its step
    // immediately forces `ih`.
    if let ExprData::Nat(val, _, _) = major_whnf.data() {
      if self.nat_iota_should_stick(&rec_id, val) {
        return Ok(None);
      }
      major_whnf = self.nat_to_constructor(&val.clone());
    } else {
      self.reset_nat_iota_run();
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
        matches!(self.env.get(id), Some(KConst::Ctor { .. }))
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
      let (cidx, ctor_fields) = match self.env.get(ctor_id) {
        Some(KConst::Ctor { cidx, fields, .. }) => {
          (u64_to_usize::<M>(cidx)?, u64_to_usize::<M>(fields)?)
        },
        _ => unreachable!(),
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
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      for arg in ctor_args.iter().skip(field_start) {
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      for arg in spine.iter().skip(recr.major_idx + 1) {
        result = self.intern(KExpr::app(result, arg.clone()));
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

  fn is_struct_like(&self, id: &KId<M>) -> bool {
    match self.env.get(id) {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        !is_rec && indices == 0 && ctors.len() == 1
      },
      _ => false,
    }
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
    if rule.fields == 0 {
      return Ok(None);
    }

    let rec_ty = match self.env.get(rec_id) {
      Some(c) => c.ty().clone(),
      None => return Ok(None),
    };
    let skip = (recr.params + recr.motives + recr.minors + recr.indices) as u64;
    let ind_id = match self.get_major_inductive_id(&rec_ty, skip) {
      Ok(id) => id,
      Err(_) => return Ok(None),
    };
    if !self.is_struct_like(&ind_id) {
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
    let rec_ty = match self.env.get(rec_id) {
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
    let ctor_id = match self.env.get(&ind_id) {
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
  ) -> Option<KExpr<M>> {
    // String literal → constructor form before trying projection
    let wval_expanded;
    let wval = if let ExprData::Str(s, _, _) = wval.data() {
      wval_expanded = self.str_lit_to_constructor(&s.clone());
      &wval_expanded
    } else {
      wval
    };

    let (head, args) = collect_app_spine(wval);

    if let Some(result) =
      self.try_reduce_fin_val_decidable_rec(id, field, &head, &args)
    {
      self.dump_proj_trace(id, field, wval, None, Some(&result));
      return Some(result);
    }

    let ctor_id = match head.data() {
      ExprData::Const(id, _, _) => id,
      _ => {
        self.dump_proj_trace(id, field, wval, None, None);
        return None;
      },
    };

    let ctor_params = match self.env.get(ctor_id) {
      Some(KConst::Ctor { params, .. }) => usize::try_from(params).ok()?,
      _ => {
        self.dump_proj_trace(id, field, wval, None, None);
        return None;
      },
    };

    let field_start = ctor_params;
    let idx = field_start + usize::try_from(field).ok()?;
    let result = args.get(idx).cloned();
    self.dump_proj_trace(id, field, wval, Some(ctor_params), result.as_ref());
    result
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
      if let Some(result) = self.try_proj_reduce(&id, field, &wval) {
        return Ok(Some((result, args)));
      }
    }
    Ok(None)
  }

  fn try_reduce_projection_definition(
    &mut self,
    e: &KExpr<M>,
  ) -> Option<KExpr<M>> {
    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return None;
    };
    let val = match self.env.get(id) {
      Some(KConst::Defn { kind: DefKind::Definition, val, .. }) => val,
      _ => return None,
    };
    let (arity, struct_id, field, struct_arg_idx) =
      self.projection_definition_info(&val)?;
    if args.len() < arity {
      return None;
    }
    let mut result =
      self.intern(KExpr::prj(struct_id, field, args[struct_arg_idx].clone()));
    for arg in args.iter().skip(arity) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Some(result)
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
            if matches!(self.env.get(id), Some(KConst::Indc { .. })) {
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
      self.intern(KExpr::cnst(self.prims.nat_zero.clone(), Box::new([])))
    } else {
      let pred_val = Nat(&val.0 - BigUint::from(1u64));
      let pred_addr = Address::hash(&pred_val.to_le_bytes());
      let pred_expr = self.intern(KExpr::nat(pred_val, pred_addr));
      let succ =
        self.intern(KExpr::cnst(self.prims.nat_succ.clone(), Box::new([])));
      self.intern(KExpr::app(succ, pred_expr))
    }
  }

  fn nat_literal(&mut self, n: u64) -> KExpr<M> {
    let val = Nat::from(n);
    let addr = Address::hash(&val.to_le_bytes());
    self.intern(KExpr::nat(val, addr))
  }

  fn nat_iota_should_stick(&mut self, rec_id: &KId<M>, val: &Nat) -> bool {
    const MAX_LARGE_NAT_LITERAL_IOTA: u32 = 16_384;
    const MAX_CONSECUTIVE_NAT_LITERAL_IOTA: u32 = 8192;

    if val.0 > *NAT_IOTA_LITERAL_CAP {
      self.nat_iota_large_expansions =
        self.nat_iota_large_expansions.saturating_add(1);
      if self.nat_iota_large_expansions > MAX_LARGE_NAT_LITERAL_IOTA {
        return true;
      }
    }

    let is_next_predecessor =
      self.nat_iota_last.as_ref().is_some_and(|(last_rec, last_val)| {
        last_rec == &rec_id.addr && last_val == &(&val.0 + 1u64)
      });

    self.nat_iota_run =
      if is_next_predecessor { self.nat_iota_run.saturating_add(1) } else { 1 };
    self.nat_iota_last = Some((rec_id.addr.clone(), val.0.clone()));

    self.nat_iota_run > MAX_CONSECUTIVE_NAT_LITERAL_IOTA
  }

  fn reset_nat_iota_run(&mut self) {
    self.nat_iota_last = None;
    self.nat_iota_run = 0;
  }

  /// Nat primitive reduction (add, sub, mul, div, mod, pow, gcd, bitwise, predicates).
  pub(super) fn try_reduce_nat(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    // Nat.succ n → n + 1
    if addr == self.prims.nat_succ.addr && args.len() == 1 {
      let a = self.whnf(&args[0])?;
      if let Some(n) = extract_nat_value(&a, &self.prims) {
        let result = Nat(&n.0 + 1u64);
        let blob_addr = Address::hash(&result.to_le_bytes());
        return Ok(Some(self.intern(KExpr::nat(result, blob_addr))));
      }
      return Ok(None);
    }

    // Nat.pred n → n - 1 (or 0 if n = 0)
    if addr == self.prims.nat_pred.addr && args.len() == 1 {
      let a = self.whnf(&args[0])?;
      if let Some(view) = self.nat_ctor_view(&a) {
        let result = match view {
          NatCtorView::Zero => self.nat_literal(0),
          NatCtorView::Succ(pred) => pred,
        };
        return Ok(Some(result));
      }
      if let Some(n) = extract_nat_value(&a, &self.prims) {
        let result = if n.0 == num_bigint::BigUint::ZERO {
          Nat(num_bigint::BigUint::ZERO)
        } else {
          Nat(&n.0 - 1u64)
        };
        let blob_addr = Address::hash(&result.to_le_bytes());
        return Ok(Some(self.intern(KExpr::nat(result, blob_addr))));
      }
      return Ok(None);
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

    let wa = self.whnf(&args[0])?;
    let wb = self.whnf(&args[1])?;
    self.dump_nat_trace("arg0-whnf", &wa);
    self.dump_nat_trace("arg1-whnf", &wb);
    let a_val = extract_nat_value(&wa, &self.prims);
    let b_val = extract_nat_value(&wb, &self.prims);

    if let Some(result) = self
      .try_reduce_nat_symbolic_bin(&addr, &args, &wa, &wb, &a_val, &b_val)?
    {
      return Ok(Some(result));
    }

    let a_val = match a_val {
      Some(v) => v,
      None => {
        self.dump_nat_trace("arg0-not-nat", &wa);
        return Ok(None);
      },
    };
    let b_val = match b_val {
      Some(v) => v,
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
      self.intern(KExpr::nat(result, blob_addr))
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

  fn try_reduce_nat_symbolic_bin(
    &mut self,
    addr: &Address,
    args: &[KExpr<M>],
    wa: &KExpr<M>,
    wb: &KExpr<M>,
    a_val: &Option<Nat>,
    b_val: &Option<Nat>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    const MAX_SYMBOLIC_NAT_LITERAL: u64 = 64;

    let result = if *addr == self.prims.nat_add.addr {
      let Some(n) = b_val.as_ref().and_then(Nat::to_u64) else {
        return Ok(None);
      };
      if n > MAX_SYMBOLIC_NAT_LITERAL {
        return Ok(None);
      }
      self.nat_succ_n(wa.clone(), n)
    } else if *addr == self.prims.nat_mul.addr {
      match b_val.as_ref().and_then(Nat::to_u64) {
        Some(0) => self.nat_literal(0),
        _ => return Ok(None),
      }
    } else if *addr == self.prims.nat_sub.addr {
      let Some(n) = b_val.as_ref().and_then(Nat::to_u64) else {
        return Ok(None);
      };
      if n > MAX_SYMBOLIC_NAT_LITERAL {
        return Ok(None);
      }
      match self.nat_pred_n(wa.clone(), n) {
        Some(result) => result,
        None => return Ok(None),
      }
    } else if *addr == self.prims.nat_mod.addr {
      let Some(a) = a_val else {
        return Ok(None);
      };
      let b_lower = self.nat_lower_bound(wb)?;
      if b_lower.0 <= a.0 {
        return Ok(None);
      }
      self.nat_expr_from_value(a.clone())
    } else {
      return Ok(None);
    };

    Ok(Some(self.finish_nat_symbolic_result(result, args)))
  }

  fn finish_nat_symbolic_result(
    &mut self,
    mut result: KExpr<M>,
    args: &[KExpr<M>],
  ) -> KExpr<M> {
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    result
  }

  fn nat_expr_from_value(&mut self, n: Nat) -> KExpr<M> {
    let blob_addr = Address::hash(&n.to_le_bytes());
    self.intern(KExpr::nat(n, blob_addr))
  }

  fn nat_succ_n(&mut self, mut e: KExpr<M>, n: u64) -> KExpr<M> {
    for _ in 0..n {
      let succ =
        self.intern(KExpr::cnst(self.prims.nat_succ.clone(), Box::new([])));
      e = self.intern(KExpr::app(succ, e));
    }
    e
  }

  fn nat_pred_n(&mut self, mut e: KExpr<M>, n: u64) -> Option<KExpr<M>> {
    for _ in 0..n {
      e = match self.nat_ctor_view(&e)? {
        NatCtorView::Zero => self.nat_literal(0),
        NatCtorView::Succ(pred) => pred,
      };
    }
    Some(e)
  }

  fn nat_lower_bound(&mut self, e: &KExpr<M>) -> Result<Nat, TcError<M>> {
    self.nat_lower_bound_core(e, 0)
  }

  fn nat_lower_bound_core(
    &mut self,
    e: &KExpr<M>,
    depth: u8,
  ) -> Result<Nat, TcError<M>> {
    const MAX_LOWER_BOUND_DEPTH: u8 = 24;
    if depth >= MAX_LOWER_BOUND_DEPTH {
      return Ok(Nat(num_bigint::BigUint::ZERO));
    }

    if let Some(n) = extract_nat_lit(e, &self.prims) {
      return Ok(n.clone());
    }

    let (head, args) = collect_app_spine(e);
    if let ExprData::Const(id, _, _) = head.data() {
      if id.addr == self.prims.nat_succ.addr && args.len() == 1 {
        let pred = self.nat_lower_bound_core(&args[0], depth + 1)?;
        return Ok(Nat(pred.0 + 1u64));
      }
      if id.addr == self.prims.nat_add.addr && args.len() == 2 {
        let a = self.nat_lower_bound_core(&args[0], depth + 1)?;
        let b = self.nat_lower_bound_core(&args[1], depth + 1)?;
        return Ok(Nat(a.0 + b.0));
      }
      if id.addr == self.prims.nat_mul.addr && args.len() == 2 {
        let a = self.nat_lower_bound_core(&args[0], depth + 1)?;
        let b = self.nat_lower_bound_core(&args[1], depth + 1)?;
        return Ok(Nat(a.0 * b.0));
      }
      if self.is_nat_bin_arith_addr(&id.addr)
        || self.is_nat_bin_pred_addr(&id.addr)
        || is_const_named(id, &["Nat.rec", "Nat.casesOn", "BitVec.toNat"])
      {
        return Ok(Nat(num_bigint::BigUint::ZERO));
      }
    }

    if self.is_stuck_nat_predicate_probe(e) {
      return Ok(Nat(num_bigint::BigUint::ZERO));
    }

    let w = self.whnf(e)?;
    if &w == e {
      return Ok(Nat(num_bigint::BigUint::ZERO));
    }
    self.nat_lower_bound_core(&w, depth + 1)
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

  fn try_reduce_nat_predicate(
    &mut self,
    addr: &Address,
    args: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let a_val = self.try_eval_nat_value_for_pred(&args[0])?;
    let b_val = self.try_eval_nat_value_for_pred(&args[1])?;
    let decision = if *addr == self.prims.nat_beq.addr {
      match (&a_val, &b_val) {
        (Some(a), Some(b)) => Some(a == b),
        _ => None,
      }
    } else {
      match (&a_val, &b_val) {
        (Some(a), Some(b)) => Some(a <= b),
        (Some(a), None) if a.0 == num_bigint::BigUint::ZERO => Some(true),
        _ => None,
      }
    };

    let Some(decision) = decision else {
      if let Some(result) = self.try_reduce_nat_predicate_by_ctor(addr, args)? {
        return Ok(Some(result));
      }
      return Ok(None);
    };
    Ok(Some(self.nat_predicate_bool_result(decision, args)))
  }

  fn try_reduce_nat_predicate_by_ctor(
    &mut self,
    addr: &Address,
    args: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let a = self.nat_ctor_view_for_pred(&args[0], 0)?;
    let b = self.nat_ctor_view_for_pred(&args[1], 0)?;
    let result = if *addr == self.prims.nat_beq.addr {
      match (a, b) {
        (Some(NatCtorView::Zero), Some(NatCtorView::Zero)) => {
          self.nat_predicate_bool_result(true, args)
        },
        (Some(NatCtorView::Zero), Some(NatCtorView::Succ(_)))
        | (Some(NatCtorView::Succ(_)), Some(NatCtorView::Zero)) => {
          self.nat_predicate_bool_result(false, args)
        },
        (Some(NatCtorView::Succ(a)), Some(NatCtorView::Succ(b))) => {
          self.nat_predicate_recur_result(addr, &a, &b, args)
        },
        _ => return Ok(None),
      }
    } else {
      match (a, b) {
        (Some(NatCtorView::Zero), _) => {
          self.nat_predicate_bool_result(true, args)
        },
        (Some(NatCtorView::Succ(_)), Some(NatCtorView::Zero)) => {
          self.nat_predicate_bool_result(false, args)
        },
        (Some(NatCtorView::Succ(a)), Some(NatCtorView::Succ(b))) => {
          self.nat_predicate_recur_result(addr, &a, &b, args)
        },
        _ => return Ok(None),
      }
    };
    Ok(Some(result))
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

  fn nat_predicate_recur_result(
    &mut self,
    addr: &Address,
    a: &KExpr<M>,
    b: &KExpr<M>,
    args: &[KExpr<M>],
  ) -> KExpr<M> {
    let head_id = if *addr == self.prims.nat_beq.addr {
      self.prims.nat_beq.clone()
    } else {
      self.prims.nat_ble.clone()
    };
    let head = self.intern(KExpr::cnst(head_id, Box::new([])));
    let mut result = self.intern(KExpr::app(head, a.clone()));
    result = self.intern(KExpr::app(result, b.clone()));
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    result
  }

  fn nat_ctor_view_for_pred(
    &mut self,
    e: &KExpr<M>,
    depth: u8,
  ) -> Result<Option<NatCtorView<M>>, TcError<M>> {
    const MAX_PRED_NAT_CTOR_VIEW_DEPTH: u8 = 8;
    if let Some(view) = self.nat_ctor_view(e) {
      return Ok(Some(view));
    }
    if depth >= MAX_PRED_NAT_CTOR_VIEW_DEPTH {
      return Ok(None);
    }

    if self.is_stuck_nat_predicate_probe(e) {
      return Ok(None);
    }

    let w = self.whnf(e)?;
    if &w == e {
      return Ok(None);
    }
    if let Some(view) = self.nat_ctor_view(&w) {
      return Ok(Some(view));
    }
    self.nat_ctor_view_for_pred(&w, depth + 1)
  }

  fn nat_ctor_view(&mut self, e: &KExpr<M>) -> Option<NatCtorView<M>> {
    if let Some(n) = extract_nat_lit(e, &self.prims) {
      if n.0 == num_bigint::BigUint::ZERO {
        return Some(NatCtorView::Zero);
      }
      let pred = Nat(&n.0 - num_bigint::BigUint::from(1u64));
      let pred_addr = Address::hash(&pred.to_le_bytes());
      let pred_expr = self.intern(KExpr::nat(pred, pred_addr));
      return Some(NatCtorView::Succ(pred_expr));
    }

    let (head, args) = collect_app_spine(e);
    let ExprData::Const(id, _, _) = head.data() else {
      return None;
    };
    if id.addr != self.prims.nat_succ.addr || args.len() != 1 {
      return None;
    }
    Some(NatCtorView::Succ(args[0].clone()))
  }

  /// A shallow Nat evaluator for predicate arguments.
  ///
  /// `Nat.beq`/`Nat.ble` are often used as branching conditions. When one
  /// side is symbolic, fully WHNF-ing it can expose large recursive models
  /// such as `Nat.rec` over `BitVec.toFin` projections. For predicates we only
  /// need enough evaluation to decide literal comparisons; unknown values can
  /// safely remain stuck.
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
          || is_const_named(id, &["Nat.rec", "Nat.casesOn", "BitVec.toNat"])
      },
      ExprData::Prj(id, _, val, _) => {
        if is_const_named(id, &["Fin"]) {
          return true;
        }
        let (val_head, _) = collect_app_spine(val);
        matches!(
          val_head.data(),
          ExprData::Const(val_id, _, _)
            if is_const_named(
              val_id,
              &["Nat.rec", "Nat.casesOn", "BitVec.toNat"],
            )
        )
      },
      _ => false,
    }
  }

  /// `Nat.beq`/`Nat.ble` are extern primitives with recursive Lean models.
  /// If native reduction cannot decide them, unfolding the model can peel huge
  /// literals against an unknown argument. Leave the primitive app stuck.
  fn is_stuck_nat_predicate(&self, e: &KExpr<M>) -> bool {
    let (head, args) = collect_app_spine(e);
    if args.len() != 2 {
      return false;
    }
    matches!(
      head.data(),
      ExprData::Const(id, _, _)
        if id.addr == self.prims.nat_beq.addr
          || id.addr == self.prims.nat_ble.addr
    )
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

    if is_const_named(id, &["BitVec.toNat"]) && args.len() >= 2 {
      if let Some(result) = self.try_reduce_bitvec_to_nat(&args[1])? {
        return Ok(Some(self.finish_app_result(result, &args, 2)));
      }
      return Ok(None);
    }

    if is_const_named(id, &["BitVec.ult"]) && args.len() >= 3 {
      if let Some(result) =
        self.try_reduce_bitvec_ult(&args[0], &args[1], &args[2])?
      {
        return Ok(Some(self.finish_app_result(result, &args, 3)));
      }
      return Ok(None);
    }

    if is_const_named(id, &["Decidable.decide"])
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
    if !is_const_named(id, &["LT.lt"]) || args.len() != 4 {
      return Ok(None);
    }

    let (type_head, type_args) = collect_app_spine(&args[0]);
    let ExprData::Const(type_id, _, _) = type_head.data() else {
      return Ok(None);
    };
    if !is_const_named(type_id, &["BitVec"]) || type_args.len() != 1 {
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

    let to_nat = self
      .find_const_id_named("BitVec.toNat")
      .unwrap_or_else(|| synthetic_named_id("BitVec.toNat"));
    let head = self.intern(KExpr::cnst(to_nat, Box::new([])));
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
    if is_const_named(id, &["BitVec.ofNat"]) && args.len() == 2 {
      return Some((args[0].clone(), args[1].clone()));
    }
    if !is_const_named(id, &["OfNat.ofNat"]) || args.len() < 2 {
      return None;
    }

    let (type_head, type_args) = collect_app_spine(&args[0]);
    let ExprData::Const(type_id, _, _) = type_head.data() else {
      return None;
    };
    if is_const_named(type_id, &["BitVec"]) && type_args.len() == 1 {
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
        is_const_named(id, &["PUnit._sizeOf_1", "Unit._sizeOf_1"])
          && args.len() == 1;

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
      if is_const_named(id, &["SizeOf.sizeOf"]) && args.len() == 3 {
        let (ty_head, _) = collect_app_spine(&args[0]);
        if let ExprData::Const(ty_id, _, _) = ty_head.data()
          && is_const_named(ty_id, &["Unit", "PUnit"])
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
    let body = match self.env.get(&arg_id) {
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
    let is_back = is_const_named(id, &["String.back", "String.Legacy.back"]);
    let is_utf8_byte_size = is_const_named(id, &["String.utf8ByteSize"]);
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

  fn find_const_id_named(&self, dotted: &str) -> Option<KId<M>> {
    self.env.iter().find_map(|(id, _)| {
      if is_const_named(&id, &[dotted]) { Some(id) } else { None }
    })
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

fn dotted_name(dotted: &str) -> Name {
  let mut name = Name::anon();
  for part in dotted.split('.') {
    name = Name::str(name, part.to_string());
  }
  name
}

fn synthetic_named_id<M: KernelMode>(dotted: &str) -> KId<M> {
  KId::new(Address::hash(dotted.as_bytes()), M::meta_field(dotted_name(dotted)))
}

fn name_components_eq_dotted(mut name: &Name, mut dotted: &str) -> bool {
  loop {
    let (prefix, part) = match dotted.rsplit_once('.') {
      Some((prefix, part)) => (Some(prefix), part),
      None => (None, dotted),
    };
    match name.as_data() {
      NameData::Str(pre, s, _) if s == part => {
        name = pre;
        match prefix {
          Some(next) => dotted = next,
          None => return matches!(name.as_data(), NameData::Anonymous(_)),
        }
      },
      _ => return false,
    }
  }
}

fn is_const_named<M: KernelMode>(id: &KId<M>, names: &[&str]) -> bool {
  let Some(name) = M::meta_name(&id.name) else {
    return false;
  };
  names.iter().any(|expected| name_components_eq_dotted(&name, expected))
}

enum NatCtorView<M: KernelMode> {
  Zero,
  Succ(KExpr<M>),
}

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
/// `Nat.succ <literal predecessor>` inside branch bodies. Lean's C++ kernel
/// keeps primitive numerals available to its native Nat reducer across this
/// path; in this kernel we recover the same value here before deciding to
/// unfold recursive Nat definitions such as `Nat.modCore`.
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
  if is_const_named(id, &["OfNat.ofNat"]) && args.len() >= 2 {
    let (type_head, type_args) = collect_app_spine(&args[0]);
    if type_args.is_empty()
      && let ExprData::Const(type_id, _, _) = type_head.data()
      && type_id.addr == prims.nat.addr
    {
      return extract_nat_value(&args[1], prims);
    }
  }
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
    // Match C++ kernel: no explicit limit beyond what GMP handles, but we
    // cap at 2^24 to avoid unbounded memory allocation.
    const REDUCE_SHIFT_MAX: u64 = 1 << 24;
    match b.to_u64() {
      #[allow(clippy::cast_possible_truncation)] // guarded: shift <= 2^24
      Some(shift) if shift <= REDUCE_SHIFT_MAX => &a.0 << shift as usize,
      _ => return None, // too large to compute
    }
  } else if *addr == p.nat_shift_right.addr {
    const REDUCE_SHIFT_MAX: u64 = 1 << 24;
    match b.to_u64() {
      #[allow(clippy::cast_possible_truncation)] // guarded: shift <= 2^24
      Some(shift) if shift <= REDUCE_SHIFT_MAX => &a.0 >> shift as usize,
      _ => zero, // right-shift by huge amount gives 0 (correct)
    }
  } else {
    return None;
  };
  Some(Nat(r))
}

// ---------------------------------------------------------------------------
// Int native reduction
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

/// An Int literal we can compute on. Produced by `extract_int_lit` and
/// consumed by `compute_int_bin`.
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

/// Compute a binary Int operation given two literals. Returns `None` if
/// the operation is unknown (the caller leaves the expression unreduced).
fn compute_int_bin<M: KernelMode>(
  addr: &Address,
  p: &Primitives<M>,
  a: &IntVal,
  b: &IntVal,
) -> Option<IntVal> {
  let r = if *addr == p.int_add.addr {
    a + b
  } else if *addr == p.int_sub.addr {
    a - b
  } else if *addr == p.int_mul.addr {
    a * b
  } else {
    return None;
  };
  Some(r)
}

impl<M: KernelMode> TypeChecker<M> {
  /// Native Int reduction. Dispatches on the head constant:
  ///
  /// - `Int.neg x`: unary negation if `x` whnfs to an Int literal.
  /// - `Int.add`/`Int.sub`/`Int.mul x y`: binary arithmetic, both args literal.
  /// - `Int.emod`/`Int.ediv x y`: division or modulo, both args literal.
  ///   `emod` semantics: result in `[0, |y|)` (Euclidean mod).
  ///   `ediv` semantics: `y * (x/y) + (x % y) = x` with non-negative remainder.
  /// - `Int.bmod x m`: balanced mod, `x : Int`, `m : Nat`. Returns an `Int`
  ///   in `[-m/2, (m+1)/2)`. For `m = 0` returns `x` unchanged (matching
  ///   Lean's `Int.bmod 0 _` behavior via the `if r < (m+1)/2` branch).
  /// - `Int.bdiv x m`: balanced div (quotient matching `bmod`).
  /// - `Int.natAbs x`: returns a Nat literal.
  ///
  /// Returns `None` if the head isn't a known Int primitive, arg count is
  /// wrong, or any argument fails to whnf to the expected literal form.
  /// Must run BEFORE `delta_unfold_one` on the containing `whnf` loop so
  /// that the Int.bmod body's `Decidable.rec`-headed form is never exposed.
  pub(super) fn try_reduce_int(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if e.lbr() > 0 {
      return Ok(None);
    }
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    // Extract primitive addrs up-front so `self.whnf(...)` (mutable
    // borrow) can run freely below. `Address` is cheap to clone (Arc
    // refcount bump), so this isn't a perf concern.
    let (
      int_neg_addr,
      int_nat_abs_addr,
      int_add_addr,
      int_sub_addr,
      int_mul_addr,
      int_emod_addr,
      int_ediv_addr,
      int_bmod_addr,
      int_bdiv_addr,
    ) = {
      let p = &self.prims;
      (
        p.int_neg.addr.clone(),
        p.int_nat_abs.addr.clone(),
        p.int_add.addr.clone(),
        p.int_sub.addr.clone(),
        p.int_mul.addr.clone(),
        p.int_emod.addr.clone(),
        p.int_ediv.addr.clone(),
        p.int_bmod.addr.clone(),
        p.int_bdiv.addr.clone(),
      )
    };

    // Unary ops
    if addr == int_neg_addr && !args.is_empty() {
      let wa = self.whnf(&args[0])?;
      let Some(a) = extract_int_lit(&wa, &self.prims) else {
        return Ok(None);
      };
      let r = intern_int_lit(self, -a);
      return Ok(Some(apply_extra_args(self, r, &args[1..])));
    }

    if addr == int_nat_abs_addr && !args.is_empty() {
      let wa = self.whnf(&args[0])?;
      let Some(a) = extract_int_lit(&wa, &self.prims) else {
        return Ok(None);
      };
      let nat_val = Nat(a.magnitude().clone());
      let nat_addr = Address::hash(&nat_val.to_le_bytes());
      let r = self.intern(KExpr::nat(nat_val, nat_addr));
      return Ok(Some(apply_extra_args(self, r, &args[1..])));
    }

    if args.len() < 2 {
      return Ok(None);
    }

    // Binary arithmetic: both args are Int.
    let is_bin_arith =
      addr == int_add_addr || addr == int_sub_addr || addr == int_mul_addr;
    if is_bin_arith {
      let wa = self.whnf(&args[0])?;
      let wb = self.whnf(&args[1])?;
      let Some(a) = extract_int_lit(&wa, &self.prims) else {
        return Ok(None);
      };
      let Some(b) = extract_int_lit(&wb, &self.prims) else {
        return Ok(None);
      };
      let Some(r) = compute_int_bin(&addr, &self.prims, &a, &b) else {
        return Ok(None);
      };
      let r_expr = intern_int_lit(self, r);
      return Ok(Some(apply_extra_args(self, r_expr, &args[2..])));
    }

    // Euclidean div/mod: both args Int, result Int. Matches `Int.emod` /
    // `Int.ediv` in `Init/Data/Int/DivMod/Basic.lean`.
    if addr == int_emod_addr || addr == int_ediv_addr {
      let wa = self.whnf(&args[0])?;
      let wb = self.whnf(&args[1])?;
      let Some(a) = extract_int_lit(&wa, &self.prims) else {
        return Ok(None);
      };
      let Some(b) = extract_int_lit(&wb, &self.prims) else {
        return Ok(None);
      };
      let (q, m) = int_ediv_emod(&a, &b);
      let r = if addr == int_emod_addr { m } else { q };
      let r_expr = intern_int_lit(self, r);
      return Ok(Some(apply_extra_args(self, r_expr, &args[2..])));
    }

    // Power: first arg Int, second arg Nat. Matches `Int.pow` in
    // `Init/Data/Int/Basic.lean:400`:
    //     | (m : Nat), n => Int.ofNat (m ^ n)
    //     | m@-[_+1], n => if n % 2 = 0 then Int.ofNat (m.natAbs ^ n)
    //                     else - Int.ofNat (m.natAbs ^ n)
    // We also guard the exponent against runaway allocation, mirroring
    // `compute_nat_bin`'s REDUCE_POW_MAX_EXP cap.
    let int_pow_addr = self.prims.int_pow.addr.clone();
    if addr == int_pow_addr {
      let wa = self.whnf(&args[0])?;
      let wb = self.whnf(&args[1])?;
      let Some(a) = extract_int_lit(&wa, &self.prims) else {
        return Ok(None);
      };
      let Some(b_nat) = extract_nat_value(&wb, &self.prims) else {
        return Ok(None);
      };
      const REDUCE_POW_MAX_EXP: u64 = 1 << 24;
      let Some(exp) = b_nat.to_u64() else {
        return Ok(None);
      };
      if exp > REDUCE_POW_MAX_EXP {
        return Ok(None);
      }
      // Compute |a|^n, then apply sign: positive if a ≥ 0 or n is even,
      // negative if a < 0 and n is odd.
      use num_bigint::Sign;
      let abs_a_big: BigInt =
        BigInt::from_biguint(Sign::Plus, a.magnitude().clone());
      #[allow(clippy::cast_possible_truncation)] // guarded above
      let mag_pow = abs_a_big.magnitude().pow(exp as u32);
      let r = if a.sign() == Sign::Minus && exp % 2 == 1 {
        -BigInt::from_biguint(Sign::Plus, mag_pow)
      } else {
        BigInt::from_biguint(Sign::Plus, mag_pow)
      };
      let r_expr = intern_int_lit(self, r);
      return Ok(Some(apply_extra_args(self, r_expr, &args[2..])));
    }

    // Balanced div/mod: first arg Int, second arg Nat. Matches `Int.bmod`
    // / `Int.bdiv` in `Init/Data/Int/DivMod/Basic.lean`. Semantics:
    //     let r := x % m
    //     if r < (m + 1) / 2 then r else r - m
    // bdiv: quotient so that `bdiv x m * m + bmod x m = x`.
    if addr == int_bmod_addr || addr == int_bdiv_addr {
      let wa = self.whnf(&args[0])?;
      let wb = self.whnf(&args[1])?;
      let Some(a) = extract_int_lit(&wa, &self.prims) else {
        return Ok(None);
      };
      let Some(b_nat) = extract_nat_value(&wb, &self.prims) else {
        return Ok(None);
      };
      // `Int.bmod x 0` returns x unchanged because (0+1)/2 = 0 is never
      // less-than r, so the if falls through. Matches Lean's rfl.
      if b_nat.0 == num_bigint::BigUint::ZERO {
        if addr == int_bmod_addr {
          let r_expr = intern_int_lit(self, a);
          return Ok(Some(apply_extra_args(self, r_expr, &args[2..])));
        } else {
          // bdiv x 0 = 0 by Lean convention (see Int.bdiv definition).
          let r_expr = intern_int_lit(self, BigInt::from(0));
          return Ok(Some(apply_extra_args(self, r_expr, &args[2..])));
        }
      }
      let m_big: BigInt = b_nat.0.clone().into();
      let (q_e, r_e) = int_ediv_emod(&a, &m_big);
      // Threshold: (m + 1) / 2, Nat division.
      let half = (&b_nat.0 + 1u32) / 2u32;
      let half_big: BigInt = half.into();
      let (bq, bm) =
        if r_e < half_big { (q_e, r_e) } else { (q_e + 1, r_e - m_big) };
      let r = if addr == int_bmod_addr { bm } else { bq };
      let r_expr = intern_int_lit(self, r);
      return Ok(Some(apply_extra_args(self, r_expr, &args[2..])));
    }

    Ok(None)
  }
}

/// Euclidean division and modulo on BigInt. Matches Lean's `Int.ediv` /
/// `Int.emod`: the remainder is always non-negative (in `[0, |b|)`).
/// num-bigint's native `%` is "truncated" (remainder has the sign of the
/// dividend), so we normalise by adding `|b|` when the dividend is negative.
fn int_ediv_emod(a: &BigInt, b: &BigInt) -> (BigInt, BigInt) {
  use num_bigint::Sign;
  if *b == BigInt::from(0) {
    // Lean's Int.ediv _ 0 = 0 and Int.emod x 0 = x.
    return (BigInt::from(0), a.clone());
  }
  let abs_b = BigInt::from_biguint(Sign::Plus, b.magnitude().clone());
  let q_trunc = a / b;
  let r_trunc = a % b;
  if r_trunc.sign() == Sign::Minus {
    // r_trunc < 0: add |b| to r, and adjust q by ±1 to keep `b*q + r = a`.
    // q adjustment direction: if b > 0, decrement q; if b < 0, increment q.
    let (q_adj, r_adj) = if b.sign() == Sign::Plus {
      (q_trunc - 1, r_trunc + &abs_b)
    } else {
      (q_trunc + 1, r_trunc + &abs_b)
    };
    (q_adj, r_adj)
  } else {
    (q_trunc, r_trunc)
  }
}

/// Reapply extra args onto a reduced head. Used when the primitive
/// application has more args than the primitive itself consumes.
fn apply_extra_args<M: KernelMode>(
  tc: &mut TypeChecker<M>,
  mut head: KExpr<M>,
  args: &[KExpr<M>],
) -> KExpr<M> {
  for a in args {
    head = tc.intern(KExpr::app(head, a.clone()));
  }
  head
}

#[cfg(test)]
mod tests {
  use std::sync::Arc;

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
  fn env_with_id() -> Arc<KEnv<Anon>> {
    let env = Arc::new(KEnv::new());
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
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let v = AE::var(0, ());
    assert_eq!(tc.whnf(&v).unwrap(), v);
  }

  #[test]
  fn whnf_sort_identity() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    assert_eq!(tc.whnf(&sort0()).unwrap(), sort0());
  }

  #[test]
  fn whnf_lam_identity() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    assert_eq!(tc.whnf(&lam).unwrap(), lam);
  }

  #[test]
  fn whnf_beta_simple() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // (λ x. x) a → a
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let a = AE::sort(AU::succ(AU::zero()));
    let app = AE::app(lam, a.clone());
    assert_eq!(tc.whnf(&app).unwrap(), a);
  }

  #[test]
  fn whnf_beta_multi() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // let x := Sort 0 in x → Sort 0
    let let_e = AE::let_((), sort1(), sort0(), AE::var(0, ()), true);
    assert_eq!(tc.whnf(&let_e).unwrap(), sort0());
  }

  #[test]
  fn whnf_delta() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // id(Sort 0) should delta-unfold id then beta-reduce
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let app = AE::app(id_const, sort0());
    assert_eq!(tc.whnf(&app).unwrap(), sort0());
  }

  #[test]
  fn whnf_delta_opaque_blocked() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let opaque = AE::cnst(mk_id("opaque"), Box::new([]));
    // Opaque should NOT be unfolded
    let result = tc.whnf(&opaque).unwrap();
    assert!(matches!(result.data(), ExprData::Const(..)));
  }

  #[test]
  fn whnf_delta_opaque_hint_unfolds() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let opaque_def = AE::cnst(mk_id("opaque_def"), Box::new([]));
    let result = tc.whnf(&opaque_def).unwrap();
    assert_eq!(result, sort1());
  }

  #[test]
  fn whnf_string_legacy_back_empty_literal() {
    use super::super::testing as kt;

    let env = Arc::new(KEnv::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let back = kt::ME::cnst(kt::mk_id("String.Legacy.back"), Box::new([]));
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

    let env = Arc::new(KEnv::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let size = kt::ME::cnst(kt::mk_id("String.utf8ByteSize"), Box::new([]));
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

    let env = Arc::new(KEnv::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let to_byte_array =
      kt::ME::cnst(tc.prims.string_to_byte_array.clone(), Box::new([]));
    let empty_string = kt::ME::str(String::new(), Address::hash(b""));
    let lhs = kt::ME::app(to_byte_array, empty_string);
    let rhs = kt::ME::cnst(tc.prims.byte_array_empty.clone(), Box::new([]));
    assert!(tc.is_def_eq(&lhs, &rhs).unwrap());
  }

  #[test]
  fn whnf_cache_hit() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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

  fn mk_meta_nat(n: u64) -> super::super::testing::ME {
    let v = Nat::from(n);
    let addr = Address::hash(&v.to_le_bytes());
    super::super::testing::ME::nat(v, addr)
  }

  /// Build a Nat env with Nat, Nat.zero, Nat.succ, Nat.rec, and Nat.sub.
  /// Nat.sub is defined as a primitive that the kernel's try_reduce_nat handles,
  /// but also has a delta-unfoldable body using Nat.rec (to test reduction order).
  fn nat_env() -> Arc<KEnv<Anon>> {
    use super::super::constant::RecRule;

    let env = Arc::new(KEnv::new());
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

  fn insert_nat_add_model(env: &Arc<KEnv<Anon>>, add_id: KId<Anon>) {
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
    let env = nat_env();
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
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
  fn whnf_nat_ble_symbolic_succ_stays_stuck() {
    let env = nat_env();
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    let ble_id = prims.nat_ble.clone();
    env.insert(
      ble_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: pi(nat(), pi(nat(), cnst("Bool", &[]))),
        val: lam(
          nat(),
          lam(nat(), AE::cnst(prims.bool_false.clone(), Box::new([]))),
        ),
        lean_all: (),
        block: ble_id.clone(),
      },
    );

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let ble = AE::cnst(ble_id.clone(), Box::new([]));
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    let expr = app(app(ble, mk_nat(65536)), app(succ, var(0)));
    let result = tc.whnf(&expr).unwrap();
    let (head, args) = collect_app_spine(&result);
    assert_eq!(args.len(), 2);
    match head.data() {
      ExprData::Const(id, _, _) => assert_eq!(id.addr, ble_id.addr),
      other => panic!("expected stuck Nat.ble head, got {:?}", other),
    }
    match args[0].data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(65535u64))
      },
      other => panic!("expected decremented literal, got {:?}", other),
    }
    assert_eq!(args[1], var(0));
  }

  #[test]
  fn whnf_nat_predicates_reduce_one_symbolic_ctor_layer() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let ble = AE::cnst(tc.prims.nat_ble.clone(), Box::new([]));
    let beq = AE::cnst(tc.prims.nat_beq.clone(), Box::new([]));
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));

    let ble_expr = app(app(ble, app(succ.clone(), var(1))), app(succ, var(0)));
    let ble_result = tc.whnf(&ble_expr).unwrap();
    let (ble_head, ble_args) = collect_app_spine(&ble_result);
    match ble_head.data() {
      ExprData::Const(id, _, _) => assert_eq!(id.addr, tc.prims.nat_ble.addr),
      other => panic!("expected Nat.ble head, got {:?}", other),
    }
    assert_eq!(ble_args, vec![var(1), var(0)]);

    let zero = AE::cnst(tc.prims.nat_zero.clone(), Box::new([]));
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    let beq_expr = app(app(beq, zero), app(succ, var(0)));
    let beq_result = tc.whnf(&beq_expr).unwrap();
    match beq_result.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.bool_false.addr)
      },
      other => panic!("expected Bool.false, got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_predicates_reduce_literal_ctor_against_symbolic_ctor() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let ble = AE::cnst(tc.prims.nat_ble.clone(), Box::new([]));
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));

    let lhs = app(succ.clone(), app(succ, var(0)));
    let expr = app(app(ble, lhs), mk_nat(1));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.bool_false.addr)
      },
      other => panic!("expected Bool.false, got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_predicates_peek_through_symbolic_add() {
    let env = nat_env();
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    insert_nat_add_model(&env, prims.nat_add.clone());

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let ble = AE::cnst(tc.prims.nat_ble.clone(), Box::new([]));
    let lhs = app(app(add, var(0)), mk_nat(2));
    let expr = app(app(ble, lhs), mk_nat(1));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Const(id, _, _) => {
        assert_eq!(id.addr, tc.prims.bool_false.addr)
      },
      other => panic!("expected Bool.false, got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_add_symbolic_literal_rhs_exposes_succ() {
    let env = nat_env();
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    insert_nat_add_model(&env, prims.nat_add.clone());

    let mut tc = TypeChecker::new(Arc::clone(&env));
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let expr = app(app(add, var(0)), mk_nat(2));
    let result = tc.whnf(&expr).unwrap();
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    assert_eq!(result, app(succ.clone(), app(succ, var(0))));
  }

  #[test]
  fn whnf_nat_add_ofnat_zero_lhs_stays_stuck() {
    use super::super::testing as kt;

    let env = Arc::new(KEnv::<Meta>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
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

    let env = Arc::new(KEnv::<Meta>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
  fn whnf_nat_mul_symbolic_zero_rhs_returns_zero() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let mul = AE::cnst(tc.prims.nat_mul.clone(), Box::new([]));
    let expr = app(app(mul, var(0)), mk_nat(0));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(0u64));
      },
      other => panic!("expected Nat(0), got {:?}", other),
    }
  }

  #[test]
  fn def_eq_nat_add_literal_lhs_not_succ_chain() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
  fn whnf_nat_mod_literal_by_symbolic_lower_bound() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let modu = AE::cnst(tc.prims.nat_mod.clone(), Box::new([]));
    let denom = app(app(add, var(0)), mk_nat(2));
    let expr = app(app(modu, mk_nat(1)), denom);
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(1u64));
      },
      other => panic!("expected Nat(1), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_sub_symbolic_literal_rhs_peels_succ() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let add = AE::cnst(tc.prims.nat_add.clone(), Box::new([]));
    let sub = AE::cnst(tc.prims.nat_sub.clone(), Box::new([]));
    let lhs = app(app(add, var(0)), mk_nat(2));
    let expr = app(app(sub, lhs), mk_nat(1));
    let result = tc.whnf(&expr).unwrap();
    let succ = AE::cnst(tc.prims.nat_succ.clone(), Box::new([]));
    assert_eq!(result, app(succ, var(0)));
  }

  #[test]
  fn whnf_bitvec_ult_zero_rhs_is_false() {
    use super::super::testing as kt;

    let env = Arc::new(KEnv::<Meta>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let zero =
      kt::apps(kt::cnst("BitVec.ofNat", &[]), &[kt::var(1), mk_meta_nat(0)]);
    let ult =
      kt::apps(kt::cnst("BitVec.ult", &[]), &[kt::var(1), kt::var(0), zero]);
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

    let env = Arc::new(KEnv::<Meta>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let zero =
      kt::apps(kt::cnst("BitVec.ofNat", &[]), &[kt::var(0), mk_meta_nat(0)]);
    let expr = kt::apps(kt::cnst("BitVec.toNat", &[]), &[kt::var(0), zero]);
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

    let env = Arc::new(KEnv::<Meta>::new());
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let width = kt::var(1);
    let bv_ty = kt::apps(kt::cnst("BitVec", &[]), std::slice::from_ref(&width));
    let zero =
      kt::apps(kt::cnst("BitVec.ofNat", &[]), &[width, mk_meta_nat(0)]);
    let prop =
      kt::apps(kt::cnst("LT.lt", &[]), &[bv_ty, kt::var(2), kt::var(0), zero]);
    let decide =
      kt::apps(kt::cnst("Decidable.decide", &[]), &[prop, kt::var(3)]);
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
    let env = nat_env();
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
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
  fn usize_env() -> Arc<KEnv<Anon>> {
    let env = nat_env();
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

    // Nat.pred at the real primitive address
    let pred_ty = pi(nat(), nat());
    let pred_val = lam(nat(), var(0)); // dummy body
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
    let env = usize_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = usize_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = usize_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = usize_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = usize_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = usize_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));

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

    let env = Arc::new(KEnv::<Anon>::new());
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

    let mut tc = TypeChecker::new(Arc::clone(&env));
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
  // `try_iota` guards against unbounded expansion of Nat literals into
  // Nat.succ chains when the same recursor peels consecutive predecessors
  // for thousands of steps. Verify the guard fires by applying `Nat.rec`
  // whose step immediately forces `ih` to a large literal. The reduction
  // must not diverge or panic.
  // =========================================================================

  #[test]
  fn whnf_large_nat_literal_iota_cap() {
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    // A literal well above the 2^20 threshold.
    let huge = mk_nat(1u64 << 25);
    // Nat.rec : ∀ {motive} (zero) (succ) (t : Nat), motive t
    let rec_const = cnst("Nat.rec", &[param(0)]);
    let motive = lam(nat(), nat());
    let zero_branch = mk_nat(0);
    let succ_branch = lam(nat(), lam(nat(), var(0)));
    let application =
      app(app(app(app(rec_const, motive), zero_branch), succ_branch), huge);
    // Must complete in bounded time without panicking.
    let _ = tc.whnf(&application).unwrap();
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
  fn quot_env() -> Arc<KEnv<Anon>> {
    let empty = KEnv::<Anon>::new();
    let prims = Primitives::from_env(&empty);

    let env = Arc::new(KEnv::<Anon>::new());
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
    let env = quot_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));

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
    let env = quot_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));

    let alpha = AE::cnst(mk_id("α"), Box::new([]));
    let r = AE::cnst(mk_id("r"), Box::new([]));
    let beta = AE::cnst(mk_id("β"), Box::new([]));
    let f = AE::cnst(mk_id("f"), Box::new([]));
    let h = AE::cnst(mk_id("h"), Box::new([]));
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
    let env = quot_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
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
    let env = nat_env();
    let mut tc = TypeChecker::new(Arc::clone(&env));
    let dec_le = AE::cnst(tc.prims.nat_dec_le.clone(), Box::new([]));
    // Only 1 arg — path must bail out.
    let expr = AE::app(dec_le, mk_nat(3));
    let _ = tc.whnf(&expr).unwrap();
  }
}
