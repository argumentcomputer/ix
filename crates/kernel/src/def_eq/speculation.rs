//! Admission backoff for repeatedly unproductive same-head comparisons.
//!
//! This is scheduling history, never a semantic equality/inequality cache.
//! Only an outermost unsuccessful Regular attempt charges the history;
//! its fuel includes its descendants, which must not charge again. Admitted
//! attempts keep their normal allowance. Nested attempts still share the
//! outer fuel slice and are not independently denied by history.

/// Preserve productive speculation in substantial checks while reserving
/// most of the default 100M fuel for ordinary conversion. Early backoff
/// regressed FLT: unsuccessful earlier pairs do not tell us whether
/// later comparisons of the same definition will be useful.
pub(super) const FAILED_FUEL_TOTAL: u64 = 33_554_432;

/// The threshold stops *new* root admissions. The last admitted attempt may
/// cross it by at most its allowance; it is never refunded or
/// prematurely truncated just because its eventual result might be a miss.
#[derive(Default)]
pub(crate) struct SameHeadBackoff {
  active: usize,
  failed_fuel: u64,
}

impl SameHeadBackoff {
  #[inline]
  pub(super) fn should_skip(&self, regular: bool) -> bool {
    self.active == 0 && regular && self.failed_fuel >= FAILED_FUEL_TOTAL
  }

  #[inline]
  pub(super) fn enter(&mut self) {
    self.active += 1;
  }

  pub(super) fn leave(
    &mut self,
    regular: bool,
    unsuccessful: bool,
    consumed: u64,
  ) {
    debug_assert!(self.active > 0);
    self.active -= 1;
    if self.active != 0 || !regular || !unsuccessful || consumed == 0 {
      return;
    }
    self.failed_fuel = self.failed_fuel.saturating_add(consumed);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn charge(s: &mut SameHeadBackoff, fuel: u64) {
    s.enter();
    s.leave(true, true, fuel);
  }

  #[test]
  fn backoff_only_blocks_new_regular_roots_after_the_threshold() {
    let mut s = SameHeadBackoff::default();
    charge(&mut s, FAILED_FUEL_TOTAL - 1);
    assert!(!s.should_skip(true));
    charge(&mut s, 1);
    assert!(s.should_skip(true));
    assert!(!s.should_skip(false));
    s.enter();
    assert!(!s.should_skip(true));
    s.leave(true, false, 100);
    assert_eq!(s.failed_fuel, FAILED_FUEL_TOTAL);
  }

  #[test]
  fn nested_cost_is_charged_once_and_successes_do_not_charge() {
    let mut s = SameHeadBackoff::default();
    s.enter();
    s.enter();
    s.leave(true, true, 90);
    assert_eq!(s.failed_fuel, 0);
    s.leave(true, true, 100);
    assert_eq!(s.failed_fuel, 100);
    s.enter();
    s.enter();
    s.leave(true, true, 90);
    s.leave(true, false, 100);
    assert_eq!(s.failed_fuel, 100);
    assert_eq!(s.active, 0);
  }

  #[test]
  fn a_complete_admitted_attempt_can_cross_the_threshold_without_refund() {
    let mut s = SameHeadBackoff::default();
    charge(&mut s, FAILED_FUEL_TOTAL - 1);
    assert!(!s.should_skip(true));
    charge(&mut s, 131_072);
    assert_eq!(s.failed_fuel, FAILED_FUEL_TOTAL + 131_071);
    assert!(s.should_skip(true));
  }

  #[test]
  fn non_regular_and_zero_cost_attempts_leave_no_history() {
    let mut s = SameHeadBackoff::default();
    s.enter();
    s.leave(false, true, 1_000);
    charge(&mut s, 0);
    assert_eq!(s.failed_fuel, 0);
    assert_eq!(s.active, 0);
  }
}
