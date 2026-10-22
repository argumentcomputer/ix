// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Choose lookup groups from the compiled degrees and the FFT tradeoff.
//! This runs before exposing the system or constructing its transcript.

use multi_stark::{
  expr::Source,
  graph::Node,
  lookup::{
    MAX_LOOKUP_GROUP, logup_constraint_count, logup_max_degree, stage2_width,
  },
  system::Circuit,
};

use crate::G;

/// The group-dependent part of `Aiur.fftCost`, divided by row height.
/// For h >= 2 it is `slope * log2(h) + intercept`; h = 1 uses the
/// repository model's clamped transform cost. Main-trace work cancels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FftCost {
  one: u128,
  two: u128,
  slope: u128,
  intercept: u128,
}

impl FftCost {
  fn new(
    stage2: usize,
    quotient: usize,
    blowup: usize,
    degree: usize,
  ) -> Option<Self> {
    if !quotient.is_power_of_two() || !blowup.is_power_of_two() {
      return None;
    }
    let log_q = u128::from(quotient.ilog2());
    let log_b = u128::from(blowup.ilog2());
    let qd = (quotient as u128).checked_mul(degree as u128)?;
    let b = blowup as u128;
    let trace = (b + 1).checked_mul(stage2 as u128)?;
    let slope = (b + 1).checked_mul((stage2 as u128).checked_add(qd)?)?;
    let intercept =
      qd.checked_mul(log_q.checked_add(b.checked_mul(log_b)?)?)?;
    let one = trace.checked_add(qd.checked_mul(
      log_q.max(1).checked_add(b.checked_mul(log_b.max(1))?)?,
    )?)?;
    let two = slope.checked_add(intercept)?;
    Some(Self { one, two, slope, intercept })
  }

  /// These three comparisons imply no larger FFT cost for every integer
  /// height h >= 1, including both padded and raw-height statistics.
  fn no_worse_than(self, other: Self) -> bool {
    self.one <= other.one && self.two <= other.two && self.slope <= other.slope
  }

  fn score(self) -> (u128, u128, u128) {
    (self.slope, self.intercept, self.one)
  }
}

fn max_degree(circuit: &Circuit<G>, group: usize) -> usize {
  circuit
    .graph
    .max_constraint_degree
    .max(logup_max_degree(&circuit.graph, group)) as usize
}

fn quotient_degree(circuit: &Circuit<G>, group: usize) -> Option<usize> {
  (max_degree(circuit, group).max(2) - 1).checked_next_power_of_two()
}

/// The pinned backend compiles user constraints and lookup expressions only;
/// its logUp constraints are evaluated directly from this circuit metadata.
/// Its prover key contains only preprocessed PCS data, which grouping does
/// not change. Keep all derived metadata synchronized before either is used.
pub(crate) fn set_group(circuit: &mut Circuit<G>, group: usize, degree: usize) {
  circuit.lookup_group_size = group;
  circuit.stage_2_width = stage2_width(circuit.num_lookups, group, degree);
  circuit.constraint_count = circuit.graph.zeros.len()
    + logup_constraint_count(circuit.num_lookups, group, degree);
  circuit.max_constraint_degree = max_degree(circuit, group);
}

pub(crate) fn retune(circuit: &mut Circuit<G>, blowup: usize, degree: usize) {
  // Aiur's authored constraints never refer to stage 2. Retain the layout
  // if a future circuit does: changing its column count would need a
  // separate proof that those references still have the intended meaning.
  if circuit
    .graph
    .nodes
    .iter()
    .any(|node| matches!(node, Node::Var(col) if col.source == Source::Stage2))
  {
    return;
  }
  let Some(baseline) = FftCost::new(
    circuit.stage_2_width,
    circuit.quotient_degree(),
    blowup,
    degree,
  ) else {
    return;
  };
  let mut best_group = circuit.lookup_group_size;
  let mut best_cost = baseline;
  for group in 1..=circuit.num_lookups.clamp(1, MAX_LOOKUP_GROUP) {
    let Some(quotient) = quotient_degree(circuit, group) else { continue };
    if quotient > blowup {
      continue;
    }
    let Some(cost) = FftCost::new(
      stage2_width(circuit.num_lookups, group, degree),
      quotient,
      blowup,
      degree,
    ) else {
      continue;
    };
    if cost.no_worse_than(baseline) && cost.score() < best_cost.score() {
      best_group = group;
      best_cost = cost;
    }
  }
  set_group(circuit, best_group, degree);
}

#[cfg(test)]
mod tests {
  use super::*;

  fn cost_at(stage2: usize, quotient: usize, blowup: usize, h: usize) -> f64 {
    let [stage2, quotient, blowup, h] = [stage2, quotient, blowup, h]
      .map(|n| f64::from(u32::try_from(n).unwrap()));
    let transform = |n: f64| n * n.max(2.0).log2();
    (blowup + 1.0) * stage2 * transform(h)
      + 2.0 * transform(quotient * h)
      + 2.0 * quotient * transform(blowup * h)
  }

  #[test]
  fn fft_dominance_preserves_cost_at_small_and_large_heights() {
    for blowup in [1, 2, 4, 8] {
      for before_q in [1, 2, 4, 8] {
        for after_q in [1, 2, 4, 8] {
          for before_s2 in [2, 4, 8, 16, 32, 128] {
            for after_s2 in [2, 4, 8, 16, 32, 128] {
              let before =
                FftCost::new(before_s2, before_q, blowup, 2).unwrap();
              let after = FftCost::new(after_s2, after_q, blowup, 2).unwrap();
              if after.no_worse_than(before) {
                for h in [1, 2, 3, 7, 16, 255, 1_024, 65_536, 1 << 30] {
                  assert!(
                    cost_at(after_s2, after_q, blowup, h)
                      <= cost_at(before_s2, before_q, blowup, h)
                  );
                }
              }
            }
          }
        }
      }
    }
  }

  #[test]
  fn fft_cost_rejects_invalid_dimensions_and_overflow() {
    assert!(FftCost::new(1, 0, 4, 2).is_none());
    assert!(FftCost::new(1, 3, 4, 2).is_none());
    assert!(FftCost::new(1, 2, 3, 2).is_none());
    assert!(
      FftCost::new(
        usize::MAX,
        1 << (usize::BITS - 1),
        1 << (usize::BITS - 1),
        usize::MAX
      )
      .is_none()
    );
  }
}
