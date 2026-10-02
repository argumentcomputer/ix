//! Scoped phase timers of the tiered construction, for profiling only.
//!
//! With the `sharing-profile` feature every [`scope`] adds its wall time
//! (per thread, summed over threads) to a process-wide counter of its
//! [`Phase`]; [`report`] reads the counters. Without the feature (the
//! default) [`scope`] is an empty value and nothing is measured. Timing never
//! affects the construction.

/// A timed part of the construction. Scopes of different phases do not
/// nest, except [`Phase::Total`], which wraps one construction after its DAG
/// is built (the [`Phase::Dag`] scope comes before it).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Phase {
  /// One whole tiered construction (DAG built).
  Total,
  /// Expansion of the input into the structural DAG.
  Dag,
  /// Per width: the candidate count and graph facts of `tiered_at`.
  Prep,
  /// Phase 1: graph facts, spine tables, bounds and the classification.
  Classify,
  /// Phase 1: the component searches.
  Search,
  /// Phase 1: the table-count knapsack.
  Knapsack,
  /// Phase 1: model length, pinned order and decisions of the uniform
  /// optimum, and the building of its expressions where they are built.
  UniformMaterialize,
  /// Phase 1: the dry run (what the expressions contain, their real length),
  /// or the re-expansion check and real length of built expressions.
  UniformCheck,
  /// Phase 2: reference counts, first tier, Kahn order.
  Allocate,
  /// Phase 3: dictionary evaluations (the whole table, or every prefix).
  RematerializeCosts,
  /// Phase 3: materialization decisions of the entries and roots.
  RematerializeDecide,
  /// Phase 3: building the expressions of the decisions.
  RematerializeBuild,
  /// Phase 3: price, re-expansion and length checks.
  RematerializeCheck,
  /// Reassembly and serialization of the output Constant.
  Output,
}

impl Phase {
  #[cfg_attr(not(feature = "sharing-profile"), allow(dead_code))]
  pub(crate) const ALL: [Phase; 14] = [
    Phase::Total,
    Phase::Dag,
    Phase::Prep,
    Phase::Classify,
    Phase::Search,
    Phase::Knapsack,
    Phase::UniformMaterialize,
    Phase::UniformCheck,
    Phase::Allocate,
    Phase::RematerializeCosts,
    Phase::RematerializeDecide,
    Phase::RematerializeBuild,
    Phase::RematerializeCheck,
    Phase::Output,
  ];

  #[cfg_attr(not(feature = "sharing-profile"), allow(dead_code))]
  fn name(self) -> &'static str {
    match self {
      Phase::Total => "total",
      Phase::Dag => "dag",
      Phase::Prep => "prep",
      Phase::Classify => "p1.classify",
      Phase::Search => "p1.search",
      Phase::Knapsack => "p1.knapsack",
      Phase::UniformMaterialize => "p1.materialize",
      Phase::UniformCheck => "p1.check",
      Phase::Allocate => "p2.allocate",
      Phase::RematerializeCosts => "p3.costs",
      Phase::RematerializeDecide => "p3.decide",
      Phase::RematerializeBuild => "p3.build",
      Phase::RematerializeCheck => "p3.check",
      Phase::Output => "output",
    }
  }
}

#[cfg(feature = "sharing-profile")]
mod imp {
  use std::sync::atomic::{AtomicU64, Ordering};
  use std::time::Instant;

  use super::Phase;

  const N: usize = Phase::ALL.len();
  static NANOS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];
  static CALLS: [AtomicU64; N] = [const { AtomicU64::new(0) }; N];

  pub(crate) struct Scope {
    phase: Phase,
    start: Instant,
  }

  impl Drop for Scope {
    fn drop(&mut self) {
      let ns = u64::try_from(self.start.elapsed().as_nanos()).unwrap_or(0);
      NANOS[self.phase as usize].fetch_add(ns, Ordering::Relaxed);
      CALLS[self.phase as usize].fetch_add(1, Ordering::Relaxed);
    }
  }

  pub(crate) fn scope(phase: Phase) -> Scope {
    Scope { phase, start: Instant::now() }
  }

  pub(crate) fn report() -> Vec<(&'static str, u64, u64)> {
    Phase::ALL
      .iter()
      .map(|&p| {
        (
          p.name(),
          NANOS[p as usize].load(Ordering::Relaxed),
          CALLS[p as usize].load(Ordering::Relaxed),
        )
      })
      .collect()
  }
}

#[cfg(not(feature = "sharing-profile"))]
mod imp {
  use super::Phase;

  pub(crate) struct Scope;

  // Scopes are ended with `drop`, as with the feature.
  impl Drop for Scope {
    fn drop(&mut self) {}
  }

  #[inline(always)]
  pub(crate) fn scope(_phase: Phase) -> Scope {
    Scope
  }

  pub(crate) fn report() -> Vec<(&'static str, u64, u64)> {
    Vec::new()
  }
}

pub(crate) use imp::scope;

/// Per phase: name, summed nanoseconds and scope count (empty without the
/// `sharing-profile` feature).
pub fn profile_report() -> Vec<(&'static str, u64, u64)> {
  imp::report()
}
