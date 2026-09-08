//! Diagnostic-only accounting of actual same-head conversion attempts.
//!
//! `IX_SAME_HEAD_PROFILE=1` records completed attempts by outcome and head.
//! Inclusive fuel overlaps for nested attempts; exclusive fuel subtracts
//! nested attempts, and root fuel counts each charged tick at most once.
//! Failed-attempt fuel is not necessarily all avoidable: even an abandoned
//! comparison can populate useful completed-result caches. Skipped probes
//! are counted separately and never reported as attempted comparisons.
//! No expression graphs are retained and no checking policy is changed.

use ix_common::address::Address;

static ENABLED: crate::EnvFlag =
  crate::EnvFlag::new(|| crate::env_var_os("IX_SAME_HEAD_PROFILE").is_some());

#[inline]
pub(crate) fn enabled() -> bool {
  *ENABLED
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Outcome {
  Success,
  Miss,
  FuelAbort,
  DepthAbort,
  Error,
}

#[cfg(not(target_os = "zkvm"))]
const OUTCOMES: [&str; 5] =
  ["success", "miss", "fuel_abort", "depth_abort", "error"];

#[derive(Clone, Copy)]
pub(crate) enum Skip {
  Window,
  FailureCache,
  Backoff,
}

#[cfg(not(target_os = "zkvm"))]
mod native {
  use super::*;
  use rustc_hash::FxHashMap;
  use std::{cell::RefCell, fmt::Write};

  const MAX_HEADS: usize = 1024;

  #[derive(Default, Clone, Copy)]
  struct Counts {
    calls: u64,
    inclusive: u64,
    exclusive: u64,
    roots: u64,
    root_fuel: u64,
    max: u64,
    ge4096: u64,
    ge65536: u64,
    ge1000000: u64,
  }

  impl Counts {
    fn record(&mut self, fuel: u64, child_fuel: u64, root: bool) {
      self.calls += 1;
      self.inclusive = self.inclusive.saturating_add(fuel);
      self.exclusive =
        self.exclusive.saturating_add(fuel.saturating_sub(child_fuel));
      if root {
        self.roots += 1;
        self.root_fuel = self.root_fuel.saturating_add(fuel);
      }
      self.max = self.max.max(fuel);
      self.ge4096 += u64::from(fuel >= 4096);
      self.ge65536 += u64::from(fuel >= 65536);
      self.ge1000000 += u64::from(fuel >= 1_000_000);
    }

    fn line(&self, out: &mut String, label: &str, outcome: &str) {
      if self.calls == 0 {
        return;
      }
      let _ = writeln!(
        out,
        "  {label} outcome={outcome} calls={} inclusive_fuel={} exclusive_fuel={} roots={} root_fuel={} max_fuel={} ge4096={} ge65536={} ge1000000={}",
        self.calls,
        self.inclusive,
        self.exclusive,
        self.roots,
        self.root_fuel,
        self.max,
        self.ge4096,
        self.ge65536,
        self.ge1000000
      );
    }
  }

  struct Frame {
    head: Address,
    regular: bool,
    children: u64,
  }

  #[derive(Default)]
  pub(super) struct State {
    stack: Vec<Frame>,
    totals: [[Counts; OUTCOMES.len()]; 2],
    heads: FxHashMap<(Address, bool), [Counts; OUTCOMES.len()]>,
    overflow: [Counts; OUTCOMES.len()],
    skips: [[u64; 3]; 2],
    max_depth: usize,
    accounting_errors: u64,
    root_traces: usize,
  }

  fn class(regular: bool) -> &'static str {
    if regular { "regular" } else { "non_regular" }
  }

  impl State {
    pub(super) fn begin(&mut self, head: &Address, regular: bool) -> usize {
      let ticket = self.stack.len();
      self.stack.push(Frame { head: head.clone(), regular, children: 0 });
      self.max_depth = self.max_depth.max(self.stack.len());
      ticket
    }

    pub(super) fn finish(
      &mut self,
      ticket: usize,
      fuel: u64,
      outcome: Outcome,
    ) {
      let frame = self.stack.pop().expect("paired diagnostic begin/finish");
      assert_eq!(ticket, self.stack.len(), "same-head diagnostic stack order");
      let root = self.stack.is_empty();
      self.accounting_errors += u64::from(frame.children > fuel);
      if let Some(parent) = self.stack.last_mut() {
        parent.children = parent.children.saturating_add(fuel);
      }
      let outcome = outcome as usize;
      self.totals[usize::from(frame.regular)][outcome].record(
        fuel,
        frame.children,
        root,
      );
      let key = (frame.head, frame.regular);
      if self.heads.len() < MAX_HEADS || self.heads.contains_key(&key) {
        self.heads.entry(key).or_default()[outcome].record(
          fuel,
          frame.children,
          root,
        );
      } else {
        // Keep global accounting exact even when per-head attribution fills.
        self.overflow[outcome].record(fuel, frame.children, root);
      }
    }

    pub(super) fn skip(&mut self, regular: bool, reason: Skip) {
      self.skips[usize::from(regular)][reason as usize] += 1;
    }

    pub(super) fn take_root_trace(
      &mut self,
      ticket: Option<usize>,
      fuel: u64,
    ) -> Option<usize> {
      if ticket != Some(0) || fuel < 65_536 || self.root_traces >= 32 {
        return None;
      }
      self.root_traces += 1;
      Some(self.root_traces)
    }

    pub(super) fn summary(&self) -> String {
      let mut out = format!(
        "[same-head-profile] thread-local; inclusive fuel overlaps; root/exclusive fuel do not; active={} max_depth={} tracked_heads={} accounting_errors={}\n",
        self.stack.len(),
        self.max_depth,
        self.heads.len(),
        self.accounting_errors
      );
      for regular in [true, false] {
        let cls = class(regular);
        let _ = writeln!(
          out,
          "  {cls} skipped_window={} skipped_failure_cache={} skipped_backoff={}",
          self.skips[usize::from(regular)][0],
          self.skips[usize::from(regular)][1],
          self.skips[usize::from(regular)][2]
        );
        for (outcome, c) in
          OUTCOMES.iter().zip(self.totals[usize::from(regular)])
        {
          c.line(&mut out, cls, outcome);
        }
      }
      let mut heads: Vec<_> = self.heads.iter().collect();
      heads.sort_unstable_by(|(ak, a), (bk, b)| {
        let cost = |cs: &[Counts; OUTCOMES.len()]| -> u128 {
          cs.iter().map(|c| u128::from(c.exclusive)).sum()
        };
        cost(b).cmp(&cost(a)).then_with(|| ak.cmp(bk))
      });
      for ((head, regular), counts) in heads.iter().take(20).copied() {
        let label = format!("head=#{} {}", head.hex(), class(*regular));
        for (outcome, c) in OUTCOMES.iter().zip(counts) {
          c.line(&mut out, &label, outcome);
        }
      }
      // A mostly nested head can have little exclusive cost but be the root
      // that repeatedly admits a large subtree. Show that attribution too.
      heads.sort_unstable_by(|(ak, a), (bk, b)| {
        let cost = |cs: &[Counts; OUTCOMES.len()]| -> u128 {
          cs.iter().map(|c| u128::from(c.root_fuel)).sum()
        };
        cost(b).cmp(&cost(a)).then_with(|| ak.cmp(bk))
      });
      for ((head, regular), counts) in heads.into_iter().take(20) {
        for (outcome, c) in OUTCOMES.iter().zip(counts) {
          if c.roots > 0 {
            let _ = writeln!(
              out,
              "  root_head=#{} {} outcome={outcome} roots={} root_fuel={}",
              head.hex(),
              class(*regular),
              c.roots,
              c.root_fuel
            );
          }
        }
      }
      for (outcome, c) in OUTCOMES.iter().zip(self.overflow) {
        c.line(&mut out, "untracked_heads", outcome);
      }
      out
    }
  }

  thread_local! {
    pub(super) static STATE: RefCell<State> = RefCell::new(State::default());
  }

  #[cfg(test)]
  mod tests {
    use super::*;

    #[test]
    fn nested_fuel_is_not_double_counted_and_skips_are_not_attempts() {
      let mut s = State::default();
      let head = Address::hash(b"head");
      let root = s.begin(&head, true);
      let child = s.begin(&head, false);
      s.finish(child, 70, Outcome::Success);
      s.skip(false, Skip::Window);
      s.finish(root, 100, Outcome::Miss);
      let child = s.totals[0][Outcome::Success as usize];
      let parent = s.totals[1][Outcome::Miss as usize];
      assert_eq!(child.exclusive + parent.exclusive, 100);
      assert_eq!(child.root_fuel + parent.root_fuel, 100);
      assert_eq!(child.inclusive + parent.inclusive, 170);
      assert_eq!(s.skips[0][0], 1);
      assert_eq!(child.calls + parent.calls, 2);
      assert!(s.stack.is_empty());
      assert_eq!(s.accounting_errors, 0);
    }

    #[test]
    fn root_cost_is_reported_even_when_exclusive_cost_is_zero() {
      let mut s = State::default();
      let head = Address::hash(b"root with nested cost");
      let root = s.begin(&head, true);
      let child = s.begin(&Address::hash(b"child"), false);
      s.finish(child, 100_000, Outcome::Miss);
      s.finish(root, 100_000, Outcome::FuelAbort);
      for i in 0u64..21 {
        let t = s.begin(&Address::hash(&i.to_le_bytes()), true);
        s.finish(t, 1, Outcome::Success);
      }
      let report = s.summary();
      assert!(!report.contains(&format!("\n  head=#{} ", head.hex())));
      assert!(report.contains(&format!(
        "root_head=#{} regular outcome=fuel_abort roots=1 root_fuel=100000",
        head.hex()
      )));
    }

    #[test]
    fn root_trace_is_bounded_and_never_reports_nested_or_disabled_probes() {
      let mut s = State::default();
      assert_eq!(s.take_root_trace(None, 100_000), None);
      assert_eq!(s.take_root_trace(Some(1), 100_000), None);
      assert_eq!(s.take_root_trace(Some(0), 65_535), None);
      for i in 1..=32 {
        assert_eq!(s.take_root_trace(Some(0), 65_536), Some(i));
      }
      assert_eq!(s.take_root_trace(Some(0), 100_000), None);
    }

    #[test]
    fn aborts_have_cost_but_skips_do_not_and_head_storage_is_bounded() {
      let mut s = State::default();
      for i in 0..MAX_HEADS + 1 {
        let t = s.begin(&Address::hash(&i.to_le_bytes()), true);
        s.finish(t, 4096, Outcome::FuelAbort);
      }
      let t = s.begin(&Address::hash(b"depth"), false);
      s.finish(t, 19, Outcome::DepthAbort);
      s.skip(true, Skip::FailureCache);
      assert_eq!(s.heads.len(), MAX_HEADS);
      assert_eq!(s.overflow[Outcome::FuelAbort as usize].calls, 1);
      let totals = s.totals[1][Outcome::FuelAbort as usize];
      assert_eq!(totals.root_fuel, 4096 * (MAX_HEADS as u64 + 1));
      assert_eq!(totals.ge4096, MAX_HEADS as u64 + 1);
      assert_eq!(totals.ge65536, 0);
      assert!(s.summary().contains("outcome=depth_abort calls=1"));
    }
  }
}

pub(crate) fn begin(head: &Address, regular: bool) -> Option<usize> {
  if !enabled() {
    return None;
  }
  #[cfg(not(target_os = "zkvm"))]
  return Some(native::STATE.with(|s| s.borrow_mut().begin(head, regular)));
  #[cfg(target_os = "zkvm")]
  {
    let _ = (head, regular);
    None
  }
}

pub(crate) fn finish(ticket: Option<usize>, fuel: u64, outcome: Outcome) {
  #[cfg(not(target_os = "zkvm"))]
  if let Some(ticket) = ticket {
    native::STATE.with(|s| s.borrow_mut().finish(ticket, fuel, outcome));
  }
  #[cfg(target_os = "zkvm")]
  let _ = (ticket, fuel, outcome);
}

pub(crate) fn skip(regular: bool, reason: Skip) {
  if enabled() {
    #[cfg(not(target_os = "zkvm"))]
    native::STATE.with(|s| s.borrow_mut().skip(regular, reason));
  }
  #[cfg(target_os = "zkvm")]
  let _ = (regular, reason);
}

/// Admit at most 32 expensive root snapshots per thread-local check. Callers
/// only format the expressions after admission; no expression is retained.
pub(crate) fn take_root_trace(
  ticket: Option<usize>,
  fuel: u64,
) -> Option<usize> {
  #[cfg(not(target_os = "zkvm"))]
  return native::STATE.with(|s| s.borrow_mut().take_root_trace(ticket, fuel));
  #[cfg(target_os = "zkvm")]
  {
    let _ = (ticket, fuel);
    None
  }
}

/// Clear only this thread's diagnostic state, between subject checks.
pub fn reset() {
  #[cfg(not(target_os = "zkvm"))]
  native::STATE.with(|s| *s.borrow_mut() = native::State::default());
}

/// Report only this thread; no effect on checking or the subject JSON.
pub fn summary() -> String {
  if !enabled() {
    return String::new();
  }
  #[cfg(not(target_os = "zkvm"))]
  return native::STATE.with(|s| s.borrow().summary());
  #[cfg(target_os = "zkvm")]
  String::new()
}
