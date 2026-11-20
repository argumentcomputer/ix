//! Choose lookup group sizes from compiled constraint degrees and the FFT cost
//! tradeoff. This runs during backend assembly before exposing the system or
//! constructing its transcript.

use multi_stark::{
  expr::Source,
  graph::{ConstraintGraph, Node},
  lookup::{
    MAX_LOOKUP_GROUP, logup_constraint_count, logup_max_degree, stage2_width,
  },
  system::Circuit,
  types::Val,
};

/// The group-dependent part of the FFT cost model, divided by row height.
/// For `h >= 2` it is `slope * log2(h) + intercept`; `h = 1` uses the clamped
/// transform cost. Main-trace work cancels across group sizes.
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
  /// height `h >= 1`, including both padded and unpadded statistics.
  const fn no_worse_than(self, other: Self) -> bool {
    self.one <= other.one && self.two <= other.two && self.slope <= other.slope
  }

  const fn score(self) -> (u128, u128, u128) {
    (self.slope, self.intercept, self.one)
  }
}

fn lookup_degrees(graph: &ConstraintGraph<Val>) -> Vec<(u32, u32)> {
  graph
    .lookups
    .iter()
    .map(|l| {
      let mult_deg = graph.degrees[l.multiplicity.index()];
      let payload_deg =
        l.args.iter().map(|&a| graph.degrees[a.index()]).max().unwrap_or(0);
      (mult_deg, payload_deg)
    })
    .collect()
}

fn logup_max_degree_for_order(
  degs: &[(u32, u32)],
  order: &[usize],
  group_size: usize,
) -> u32 {
  let group_size = group_size.max(1);
  order
    .chunks(group_size)
    .map(|chunk| {
      let sum: u32 = chunk.iter().map(|&i| degs[i].1).sum();
      let product_term = sum + 1;
      let mult_term = chunk
        .iter()
        .map(|&i| degs[i].0 + sum - degs[i].1)
        .max()
        .unwrap_or(0);
      product_term.max(mult_term)
    })
    .max()
    .unwrap_or(1)
}

/// Deterministically pack lookup indices into `ceil(L / group)` buckets
/// (full chunks of size `group` plus an optional trailing remainder chunk) to
/// minimize the maximum chunk degree when lookups have mixed degrees.
fn balanced_lookup_order(degs: &[(u32, u32)], group: usize) -> Vec<usize> {
  let n = degs.len();
  if n <= 1 || group <= 1 {
    return (0..n).collect();
  }
  let num_chunks = n.div_ceil(group);
  let rem = n % group;
  let mut caps = vec![group; num_chunks];
  if rem != 0 {
    caps[num_chunks - 1] = rem;
  }
  let mut sorted: Vec<usize> = (0..n).collect();
  // Place highest payload-degree (then multiplicity-degree) lookups first so
  // they spread evenly across chunks and prefer the shorter remainder chunk.
  sorted.sort_by(|&a, &b| {
    (degs[b].1, degs[b].0, a).cmp(&(degs[a].1, degs[a].0, b))
  });
  let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); num_chunks];
  let mut sum_payload = vec![0u32; num_chunks];
  for idx in sorted {
    let (mult_d, payload_d) = degs[idx];
    let best_bucket = (0..num_chunks)
      .filter(|&b| buckets[b].len() < caps[b])
      .min_by_key(|&b| {
        let new_sum = sum_payload[b] + payload_d;
        let prod = new_sum + 1;
        let mut worst_mult = mult_d + new_sum - payload_d;
        for &prev in &buckets[b] {
          let (pm, pp) = degs[prev];
          worst_mult = worst_mult.max(pm + new_sum - pp);
        }
        (prod.max(worst_mult), new_sum, caps[b], b)
      })
      .unwrap();
    buckets[best_bucket].push(idx);
    sum_payload[best_bucket] += payload_d;
  }
  buckets.into_iter().flatten().collect()
}

fn max_degree(circuit: &Circuit<Val>, group: usize) -> usize {
  circuit
    .graph
    .max_constraint_degree
    .max(logup_max_degree(&circuit.graph, group)) as usize
}

fn quotient_degree_from_max(max_degree: usize) -> Option<usize> {
  (max_degree.max(2) - 1).checked_next_power_of_two()
}

fn quotient_degree(circuit: &Circuit<Val>, group: usize) -> Option<usize> {
  quotient_degree_from_max(max_degree(circuit, group))
}

/// Synchronize all derived logUp metadata for `group` before the system or
/// prover key is exposed. The prover key holds only preprocessed PCS data,
/// which lookup grouping does not change.
pub(super) fn set_group(
  circuit: &mut Circuit<Val>,
  group: usize,
  degree: usize,
) {
  circuit.lookup_group_size = group;
  circuit.stage_2_width = stage2_width(circuit.num_lookups, group, degree);
  circuit.constraint_count = circuit.graph.zeros.len()
    + logup_constraint_count(circuit.num_lookups, group, degree);
  circuit.max_constraint_degree = max_degree(circuit, group);
}

pub(super) fn retune(
  circuit: &mut Circuit<Val>,
  blowup: usize,
  degree: usize,
) {
  // Authored Aiur constraints never reference stage 2. Retain the layout if a
  // circuit ever does, since changing its column count would change column IDs.
  if circuit
    .graph
    .nodes
    .iter()
    .any(|node| matches!(node, Node::Var(col) if col.source == Source::Stage2))
  {
    return;
  }
  let Some(initial_cost) = FftCost::new(
    circuit.stage_2_width,
    circuit.quotient_degree(),
    blowup,
    degree,
  ) else {
    return;
  };
  let max_group = circuit.num_lookups.clamp(1, MAX_LOOKUP_GROUP);
  let degs = lookup_degrees(&circuit.graph);
  let has_mixed = degs.first().is_some_and(|first| degs.iter().any(|d| d != first));

  // For each allowed quotient degree (sorted ascending, starting from the
  // initial quotient), keep the lowest-cost grouping, preferring original
  // lookup order on ties so reordering only occurs for a strict cost win.
  let mut by_quotient: Vec<(usize, FftCost, usize, Option<Vec<usize>>)> =
    Vec::new();
  let mut record =
    |quotient: usize, cost: FftCost, group: usize, order: Option<Vec<usize>>| {
      if let Some(entry) = by_quotient.iter_mut().find(|e| e.0 == quotient) {
        let better = cost.score() < entry.1.score()
          || (cost.score() == entry.1.score()
            && order.is_none()
            && entry.3.is_some());
        if better {
          *entry = (quotient, cost, group, order);
        }
      } else {
        by_quotient.push((quotient, cost, group, order));
      }
    };

  for group in 1..=max_group {
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
    record(quotient, cost, group, None);
  }

  if has_mixed {
    for group in 2..=max_group {
      let order = balanced_lookup_order(&degs, group);
      let max_deg = circuit
        .graph
        .max_constraint_degree
        .max(logup_max_degree_for_order(&degs, &order, group))
        as usize;
      let Some(quotient) = quotient_degree_from_max(max_deg) else { continue };
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
      record(quotient, cost, group, Some(order));
    }
  }

  // Advance across ascending quotient degrees only when the higher-quotient
  // layout dominates the current best at every integer height `h >= 1`.
  by_quotient.sort_by_key(|e| e.0);
  let mut best_group = circuit.lookup_group_size;
  let mut best_cost = initial_cost;
  let mut best_order: Option<Vec<usize>> = None;
  for (_, cost, group, order) in by_quotient {
    if cost.no_worse_than(best_cost) && cost.score() < best_cost.score() {
      best_group = group;
      best_cost = cost;
      best_order = order;
    }
  }

  if let Some(order) = best_order {
    let original = std::mem::take(&mut circuit.graph.lookups);
    circuit.graph.lookups =
      order.into_iter().map(|i| original[i].clone()).collect();
  }
  set_group(circuit, best_group, degree);
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    expr::Expr,
    lookup::Lookup,
    system::{CircuitInputs, System},
    types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config},
  };

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

  #[test]
  fn retune_allows_quotient_four_and_balances_mixed_degree_lookups() {
    let config = GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 2,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    );
    let lin = |i: u32| Lookup::push(Expr::main(0), vec![Expr::main(i)]);
    let quad =
      |i: u32| Lookup::push(Expr::main(0), vec![Expr::main(i) * Expr::main(i)]);
    // Circuit 0: 14 quadratic-payload lookups => upgrades to group=2, q=4, s2: 28 -> 14.
    // Circuit 1: [lin, quad, lin] => balanced packing puts quad in remainder chunk,
    // upgrading to group=2, s2: 6 -> 4 while keeping q=2.
    let (mut system, _) = System::new(
      config,
      [
        CircuitInputs {
          main_width: 4,
          lookups: (0..14).map(|i| quad(1 + (i % 3))).collect(),
          ..Default::default()
        },
        CircuitInputs {
          main_width: 4,
          lookups: vec![lin(1), quad(2), lin(3)],
          ..Default::default()
        },
      ],
    );
    assert_eq!(system.circuits[0].lookup_group_size, 1);
    assert_eq!(system.circuits[0].quotient_degree(), 2);
    assert_eq!(system.circuits[1].lookup_group_size, 1);
    assert_eq!(system.circuits[1].quotient_degree(), 2);

    for circuit in &mut system.circuits {
      retune(circuit, 4, 2);
    }
    assert_eq!(system.circuits[0].lookup_group_size, 2);
    assert_eq!(system.circuits[0].quotient_degree(), 4);
    assert_eq!(system.circuits[0].stage_2_width, 14);

    assert_eq!(system.circuits[1].lookup_group_size, 2);
    assert_eq!(system.circuits[1].quotient_degree(), 2);
    assert_eq!(system.circuits[1].stage_2_width, 4);

    // End-to-end STARK prove + verifying-key codec round-trip + verify with
    // both `q = 4` lookup grouping and balanced reordered `graph.lookups`.
    use multi_stark::{
      batch::ShardInput,
      p3_field::PrimeCharacteristicRing,
      p3_matrix::dense::RowMajorMatrix,
      system::SystemWitness,
    };
    let (mut system, key) = System::new(
      GoldilocksBlake3Config::new(
        CommitmentParameters { log_blowup: 2, cap_height: 0 },
        FriParameters {
          log_final_poly_len: 0,
          max_log_arity: 1,
          num_queries: 2,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 0,
        },
      ),
      [
        // Circuit 0 pushes 14 quadratic lookups (retuned to group=2, q=4)
        // plus pulls 1 linear lookup.
        CircuitInputs {
          main_width: 4,
          lookups: (0..14)
            .map(|_| Lookup::push(Expr::main(0), vec![Expr::main(1) * Expr::main(2)]))
            .collect(),
          ..Default::default()
        },
        // Circuit 1 pulls the 14 messages in mixed [lin, quad, lin] groups so
        // balanced packing reorders its lookups too.
        CircuitInputs {
          main_width: 4,
          lookups: vec![
            Lookup::pull(Expr::main(0), vec![Expr::main(1)]),
            Lookup::pull(
              Expr::main(0),
              vec![Expr::main(2) * Expr::main(3)],
            ),
            Lookup::pull(Expr::main(0), vec![Expr::main(1)]),
          ],
          ..Default::default()
        },
      ],
    );
    for circuit in &mut system.circuits {
      retune(circuit, 4, 2);
    }
    assert_eq!(system.circuits[0].quotient_degree(), 4);
    assert_eq!(system.circuits[0].lookup_group_size, 2);
    assert_eq!(system.circuits[1].quotient_degree(), 2);
    assert_eq!(system.circuits[1].lookup_group_size, 2);

    // Circuit 0 pushes 14 * 3 = 42 copies of `6` on row 0; Circuit 1 pulls
    // 3 * 14 = 42 copies of `6` across its mixed-degree lookups.
    let t0 = RowMajorMatrix::new(
      vec![
        Val::from_u64(3), Val::from_u64(2), Val::from_u64(3), Val::ZERO,
        Val::ZERO, Val::ZERO, Val::ZERO, Val::ZERO,
      ],
      4,
    );
    let t1 = RowMajorMatrix::new(
      vec![
        Val::from_u64(14), Val::from_u64(6), Val::from_u64(2), Val::from_u64(3),
        Val::ZERO, Val::ZERO, Val::ZERO, Val::ZERO,
      ],
      4,
    );
    let witness = SystemWitness::from_stage_1(vec![t0, t1], &system);
    let proof = system.prove_batch(
      &key,
      vec![ShardInput { claims: vec![], witness }],
      vec![],
    );
    let cp = CommitmentParameters { log_blowup: 2, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    let vk_bytes = stark_key::to_bytes(&system, cp, fp);
    let vk = crate::trace::stark::VerifyingKey::from_bytes_below_floor(&vk_bytes)
      .unwrap();
    vk.verify(&[], &proof).unwrap();
  }

  #[test]
  fn retune_never_regresses_against_quotient_preserving_group() {
    let config = GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 2,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    );
    let linear_lookups = |count| {
      (0..count)
        .map(|_| Lookup::push(Expr::main(0), vec![Expr::main(1)]))
        .collect()
    };
    let (mut system, _) = System::new(
      config,
      vec![
        // 11 linear lookups: g=2 keeps q=2 (s2=12), while g=4 raises q=4
        // (s2=6) and regresses small heights relative to (g=2, q=2).
        CircuitInputs {
          main_width: 2,
          lookups: linear_lookups(11),
          ..Default::default()
        },
        // 28 linear lookups: g=4 (q=4, s2=14) dominates g=2 (q=2, s2=28)
        // at every integer height h >= 1.
        CircuitInputs {
          main_width: 2,
          lookups: linear_lookups(28),
          ..Default::default()
        },
      ],
    );
    for circuit in &mut system.circuits {
      retune(circuit, 4, 2);
    }
    assert_eq!(system.circuits[0].quotient_degree(), 2);
    assert_eq!(system.circuits[0].lookup_group_size, 2);
    assert_eq!(system.circuits[1].quotient_degree(), 4);
    assert_eq!(system.circuits[1].lookup_group_size, 4);
  }
}
