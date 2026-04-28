//! Performance counters for cache hit-rate and fuel-consumption analysis.
//!
//! All counters are gated behind the `IX_PERF_COUNTERS=1` environment variable.
//! When the variable is unset (production default), every recording call is a
//! single inlined branch on a `LazyLock<bool>` and skips the atomic increment
//! entirely. When set, the counters track:
//!
//! - `whnf_cache` and `whnf_no_delta_cache` hit/miss counts (audit §10).
//! - `infer_cache` and `infer_only_cache` hit/miss counts.
//! - `def_eq_cache` hit/miss counts.
//! - `def_eq_failure` set hit and insert counts.
//! - Per-constant peak `MAX_REC_FUEL` consumption (running max across all
//!   constants checked, plus a total for averaging).
//!
//! Counters live on [`KEnv`](super::env::KEnv) and are dumped on `Drop` when
//! enabled, so a single `IX_PERF_COUNTERS=1` invocation of any harness that
//! tears down the kernel env (e.g. `rs_kernel_check_consts`) prints a summary
//! at the end.
//!
//! ## Why atomic counters even though we run per-constant in parallel?
//!
//! `KEnv` is shared across many `TypeChecker` threads, so the simplest
//! observability story is shared atomic counters. The `Ordering::Relaxed`
//! increment cost is negligible compared to the work being measured (cache
//! probes themselves involve DashMap shard locks which dwarf an atomic add).
//! When `IX_PERF_COUNTERS` is unset the lazy bool short-circuits even the
//! atomic op.

use std::fmt;
use std::sync::LazyLock;
use std::sync::atomic::{AtomicU64, Ordering};

static PERF_ENABLED: LazyLock<bool> =
  LazyLock::new(|| std::env::var_os("IX_PERF_COUNTERS").is_some());

/// Returns `true` iff `IX_PERF_COUNTERS` is set in the environment at the
/// time this is first read. The result is cached for the lifetime of the
/// process.
#[inline]
pub fn enabled() -> bool {
  *PERF_ENABLED
}

/// Atomic counters for cache hit-rate analysis. Gated by [`enabled`].
#[derive(Default, Debug)]
pub struct PerfCounters {
  // -- WHNF caches --
  pub whnf_cache_hits: AtomicU64,
  pub whnf_cache_misses: AtomicU64,
  pub whnf_no_delta_cache_hits: AtomicU64,
  pub whnf_no_delta_cache_misses: AtomicU64,
  pub whnf_core_cache_hits: AtomicU64,
  pub whnf_core_cache_misses: AtomicU64,

  // -- Infer caches --
  pub infer_cache_hits: AtomicU64,
  pub infer_cache_misses: AtomicU64,
  pub infer_only_cache_hits: AtomicU64,
  pub infer_only_cache_misses: AtomicU64,

  // -- Def-eq caches --
  pub def_eq_cache_hits: AtomicU64,
  pub def_eq_cache_misses: AtomicU64,
  pub def_eq_failure_hits: AtomicU64,
  pub def_eq_failure_inserts: AtomicU64,

  // -- Unfold cache (constant body instantiation) --
  pub unfold_cache_hits: AtomicU64,
  pub unfold_cache_misses: AtomicU64,

  // -- Recursive fuel --
  /// Running max of fuel actually consumed by any single constant check.
  pub peak_rec_fuel_used: AtomicU64,
  /// Cumulative fuel consumed across every constant check.
  pub total_rec_fuel_used: AtomicU64,
  /// Number of constants whose fuel was tracked (for averaging).
  pub constants_checked: AtomicU64,
}

/// Helper for the "record a cache hit" pattern: increments a counter only if
/// the global toggle is on. Marked `#[inline(always)]` so the unset-path
/// collapses to a single branch + return.
#[inline(always)]
fn bump(counter: &AtomicU64) {
  if enabled() {
    counter.fetch_add(1, Ordering::Relaxed);
  }
}

impl PerfCounters {
  // -----------------------------------------------------------------------
  // WHNF caches
  // -----------------------------------------------------------------------

  pub fn record_whnf_hit(&self) {
    bump(&self.whnf_cache_hits);
  }

  pub fn record_whnf_miss(&self) {
    bump(&self.whnf_cache_misses);
  }

  pub fn record_whnf_no_delta_hit(&self) {
    bump(&self.whnf_no_delta_cache_hits);
  }

  pub fn record_whnf_no_delta_miss(&self) {
    bump(&self.whnf_no_delta_cache_misses);
  }

  pub fn record_whnf_core_hit(&self) {
    bump(&self.whnf_core_cache_hits);
  }

  pub fn record_whnf_core_miss(&self) {
    bump(&self.whnf_core_cache_misses);
  }

  // -----------------------------------------------------------------------
  // Infer caches
  // -----------------------------------------------------------------------

  pub fn record_infer_hit(&self) {
    bump(&self.infer_cache_hits);
  }

  pub fn record_infer_miss(&self) {
    bump(&self.infer_cache_misses);
  }

  pub fn record_infer_only_hit(&self) {
    bump(&self.infer_only_cache_hits);
  }

  pub fn record_infer_only_miss(&self) {
    bump(&self.infer_only_cache_misses);
  }

  // -----------------------------------------------------------------------
  // Def-eq caches
  // -----------------------------------------------------------------------

  pub fn record_def_eq_hit(&self) {
    bump(&self.def_eq_cache_hits);
  }

  pub fn record_def_eq_miss(&self) {
    bump(&self.def_eq_cache_misses);
  }

  pub fn record_def_eq_failure_hit(&self) {
    bump(&self.def_eq_failure_hits);
  }

  pub fn record_def_eq_failure_insert(&self) {
    bump(&self.def_eq_failure_inserts);
  }

  // -----------------------------------------------------------------------
  // Unfold cache
  // -----------------------------------------------------------------------

  pub fn record_unfold_hit(&self) {
    bump(&self.unfold_cache_hits);
  }

  pub fn record_unfold_miss(&self) {
    bump(&self.unfold_cache_misses);
  }

  // -----------------------------------------------------------------------
  // Recursive fuel
  // -----------------------------------------------------------------------

  /// Record the fuel actually consumed by a single constant check. Updates
  /// both the running max and the cumulative total. No-op when disabled.
  pub fn record_constant_fuel_used(&self, used: u64) {
    if !enabled() {
      return;
    }
    self.total_rec_fuel_used.fetch_add(used, Ordering::Relaxed);
    self.constants_checked.fetch_add(1, Ordering::Relaxed);

    // CAS loop on peak. Worst-case contention is O(threads); we expect very
    // few peak updates over the life of a check, so this is cheap.
    let mut current = self.peak_rec_fuel_used.load(Ordering::Relaxed);
    while used > current {
      match self.peak_rec_fuel_used.compare_exchange_weak(
        current,
        used,
        Ordering::Relaxed,
        Ordering::Relaxed,
      ) {
        Ok(_) => break,
        Err(actual) => current = actual,
      }
    }
  }

  // -----------------------------------------------------------------------
  // Reporting
  // -----------------------------------------------------------------------

  /// Render a one-shot human-readable summary. Cheap to call (a single
  /// load of each counter) and safe to call concurrently with recording.
  ///
  /// When [`enabled`] is false the summary is empty so callers can dump
  /// unconditionally.
  pub fn summary(&self) -> String {
    if !enabled() {
      return String::new();
    }
    let mut s = String::with_capacity(1024);
    let _ = self.write_summary(&mut s);
    s
  }

  fn write_summary(&self, out: &mut impl fmt::Write) -> fmt::Result {
    writeln!(out, "[ix-perf] cache hit rates:")?;
    write_rate(out, "  whnf_cache         ", &self.whnf_cache_hits, &self.whnf_cache_misses)?;
    write_rate(out, "  whnf_no_delta      ", &self.whnf_no_delta_cache_hits, &self.whnf_no_delta_cache_misses)?;
    write_rate(out, "  whnf_core          ", &self.whnf_core_cache_hits, &self.whnf_core_cache_misses)?;
    write_rate(out, "  infer_cache        ", &self.infer_cache_hits, &self.infer_cache_misses)?;
    write_rate(out, "  infer_only_cache   ", &self.infer_only_cache_hits, &self.infer_only_cache_misses)?;
    write_rate(out, "  def_eq_cache       ", &self.def_eq_cache_hits, &self.def_eq_cache_misses)?;
    write_rate(out, "  unfold_cache       ", &self.unfold_cache_hits, &self.unfold_cache_misses)?;

    let fail_hits = self.def_eq_failure_hits.load(Ordering::Relaxed);
    let fail_inserts = self.def_eq_failure_inserts.load(Ordering::Relaxed);
    writeln!(
      out,
      "  def_eq_failure     {fail_hits} hits, {fail_inserts} inserts"
    )?;

    let peak = self.peak_rec_fuel_used.load(Ordering::Relaxed);
    let total = self.total_rec_fuel_used.load(Ordering::Relaxed);
    let n = self.constants_checked.load(Ordering::Relaxed);
    let avg = if n > 0 { total / n } else { 0 };
    writeln!(out, "[ix-perf] rec_fuel:")?;
    writeln!(
      out,
      "  peak/avg per constant: {peak} / {avg}  ({n} constants checked, {total} total)"
    )
  }
}

fn write_rate(
  out: &mut impl fmt::Write,
  label: &str,
  hits: &AtomicU64,
  misses: &AtomicU64,
) -> fmt::Result {
  let h = hits.load(Ordering::Relaxed);
  let m = misses.load(Ordering::Relaxed);
  let total = h + m;
  if total == 0 {
    return writeln!(out, "{label} (no probes)");
  }
  // 1-decimal rate is plenty for human reading.
  #[allow(clippy::cast_precision_loss)]
  let rate = (h as f64) / (total as f64) * 100.0;
  writeln!(out, "{label} {h:>10} hits / {total:>10} total ({rate:>5.1}%)")
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn disabled_summary_is_empty() {
    // Default test environment doesn't set IX_PERF_COUNTERS, so summary()
    // should return an empty string regardless of recorded counts.
    let p = PerfCounters::default();
    p.record_whnf_hit();
    p.record_whnf_miss();
    if !enabled() {
      assert_eq!(p.summary(), "");
    }
  }

  #[test]
  fn rate_formatting_handles_zero_probes() {
    let mut s = String::new();
    let h = AtomicU64::new(0);
    let m = AtomicU64::new(0);
    write_rate(&mut s, "test", &h, &m).unwrap();
    assert!(s.contains("no probes"));
  }

  #[test]
  fn peak_fuel_is_running_max() {
    let p = PerfCounters::default();
    // Even when disabled, calls are no-ops so the test only checks shape.
    if enabled() {
      p.record_constant_fuel_used(100);
      p.record_constant_fuel_used(50);
      p.record_constant_fuel_used(200);
      p.record_constant_fuel_used(150);
      assert_eq!(p.peak_rec_fuel_used.load(Ordering::Relaxed), 200);
      assert_eq!(p.total_rec_fuel_used.load(Ordering::Relaxed), 500);
      assert_eq!(p.constants_checked.load(Ordering::Relaxed), 4);
    }
  }
}
