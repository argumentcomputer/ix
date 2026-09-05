//! Opt-in lookup packing for a smaller recursively verified proof.
//!
//! The pinned protocol already supports circuit-local lookup groups. Larger
//! groups reduce committed accumulator columns but can require more quotient
//! columns. Minimize their SUM, within the existing PCS degree budget; do not
//! change FRI queries, grinding, blowup, lookup order or user constraints.

use multi_stark::{
  graph::ConstraintGraph,
  lookup::{MAX_LOOKUP_GROUP, stage2_width},
  p3_field::BasedVectorSpace,
  system::Circuit,
  types::ExtVal,
};

use crate::G;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LookupPacking {
  pub group_size: usize,
  pub stage2_width: usize,
  pub max_constraint_degree: usize,
  pub quotient_degree: usize,
}

impl LookupPacking {
  fn opening_width(self) -> usize {
    self.stage2_width + Self::extension_degree() * self.quotient_degree
  }

  fn extension_degree() -> usize {
    <ExtVal as BasedVectorSpace<G>>::DIMENSION
  }

  fn candidate(
    graph: &ConstraintGraph<G>,
    group_size: usize,
    max_quotient_degree: usize,
  ) -> Option<Self> {
    // Analytic degree of the EXISTING grouped logUp constraints, as in
    // multi_stark::lookup::logup_max_degree. Use u64 here: a decoded graph
    // can have valid u32 node degrees whose regrouped sum exceeds u32.
    let mut degree = u64::from(graph.max_constraint_degree).max(1);
    for group in graph.lookups.chunks(group_size) {
      let messages: Vec<_> = group
        .iter()
        .map(|lookup| {
          lookup
            .args
            .iter()
            .map(|id| u64::from(graph.degrees[id.index()]))
            .max()
            .unwrap_or(0)
        })
        .collect();
      let sum: u64 = messages.iter().sum();
      degree = degree.max(sum + 1);
      for (lookup, message_degree) in group.iter().zip(messages) {
        degree = degree.max(
          u64::from(graph.degrees[lookup.multiplicity.index()]) + sum
            - message_degree,
        );
      }
    }
    let quotient_degree = (degree.max(2) - 1).checked_next_power_of_two()?;
    if quotient_degree > u64::try_from(max_quotient_degree).ok()?
      || degree > u64::from(u32::MAX)
    {
      return None;
    }
    Some(Self {
      group_size,
      stage2_width: stage2_width(
        graph.lookups.len(),
        group_size,
        Self::extension_degree(),
      ),
      max_constraint_degree: usize::try_from(degree).ok()?,
      quotient_degree: usize::try_from(quotient_degree).ok()?,
    })
  }
}

/// Returns only a STRICT opening-width improvement. Preserve the existing
/// key on ties; among improvements prefer smaller degree, then smaller groups.
pub(crate) fn smaller_opening_packing(
  circuit: &Circuit<G>,
  max_quotient_degree: usize,
) -> Option<LookupPacking> {
  let current_width = circuit.stage_2_width
    + LookupPacking::extension_degree() * circuit.quotient_degree();
  (1..=MAX_LOOKUP_GROUP)
    .filter_map(|group| {
      LookupPacking::candidate(&circuit.graph, group, max_quotient_degree)
    })
    .filter(|plan| plan.opening_width() < current_width)
    .min_by_key(|plan| {
      (plan.opening_width(), plan.max_constraint_degree, plan.group_size)
    })
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    expr::{ColRef, RowOffset, Source},
    graph::{Node, NodeId},
    lookup::Lookup,
  };

  fn linear_lookup_circuit(count: usize) -> Circuit<G> {
    let graph = ConstraintGraph {
      nodes: (0..2)
        .map(|index| {
          Node::Var(ColRef {
            source: Source::Main,
            offset: RowOffset::Current,
            index,
          })
        })
        .collect(),
      degrees: vec![1, 1],
      zeros: vec![],
      lookups: vec![
        Lookup { multiplicity: NodeId(1), args: vec![NodeId(0)] };
        count
      ],
      lookup_prefix_len: 2,
      max_constraint_degree: 0,
    };
    let plan = LookupPacking::candidate(&graph, 2, 2).unwrap();
    Circuit {
      graph,
      main_width: 2,
      preprocessed: None,
      preprocessed_width: 0,
      preprocessed_height: 0,
      num_lookups: count,
      stage_2_width: plan.stage2_width,
      num_publics: 8,
      lookup_group_size: 2,
      constraint_count: plan.stage2_width,
      max_constraint_degree: plan.max_constraint_degree,
    }
  }

  #[test]
  fn packing_accounts_for_quotient_cost_and_preserves_ties() {
    // Twelve degree-1 messages: k=2 costs 12+4 columns, k=4 costs 6+8.
    let circuit = linear_lookup_circuit(12);
    let plan = smaller_opening_packing(&circuit, 4).unwrap();
    assert_eq!(plan.group_size, 4);
    assert_eq!(plan.opening_width(), 14);
    // No higher quotient budget is silently introduced at blowup two.
    assert_eq!(smaller_opening_packing(&circuit, 2), None);
    // Eight messages tie at 12 columns: keep the original key/profile.
    assert_eq!(smaller_opening_packing(&linear_lookup_circuit(8), 4), None);
    // Empty lookup sets retain a pass-through accumulator.
    let empty = linear_lookup_circuit(0);
    assert_eq!(empty.stage_2_width, 2);
    assert_eq!(smaller_opening_packing(&empty, 4), None);
  }

  #[test]
  fn packing_checks_multiplicity_degree_and_overflow_before_admission() {
    let mut circuit = linear_lookup_circuit(12);
    // Degree-only adversarial vectors: multiplicity, not the product term,
    // is now limiting. A bound looking only at argument degrees is unsound.
    circuit.graph.degrees[1] = 3;
    assert_eq!(LookupPacking::candidate(&circuit.graph, 4, 4), None);
    circuit.graph.degrees[0] = u32::MAX;
    circuit.graph.degrees[1] = u32::MAX;
    assert_eq!(LookupPacking::candidate(&circuit.graph, 8, usize::MAX), None);
  }

  #[test]
  fn persisted_aggregate_key_lookup_packing_census() {
    let bytes = std::fs::read(concat!(
      env!("CARGO_MANIFEST_DIR"),
      "/../../Tests/Fixtures/Aggregate/singleton-2026-09-05/aggr.vk"
    ))
    .unwrap();
    let (system, commitment, _) = crate::vk_codec::from_bytes(&bytes).unwrap();
    let mut before = 0;
    let mut after = 0;
    let mut changes = 0;
    let mut histogram = [0; MAX_LOOKUP_GROUP + 1];
    for (index, circuit) in system.circuits.iter().enumerate() {
      let old_width = circuit.main_width
        + circuit.stage_2_width
        + 2 * circuit.quotient_degree();
      before += old_width;
      let Some(plan) =
        smaller_opening_packing(circuit, 1 << commitment.log_blowup)
      else {
        after += old_width;
        continue;
      };
      let new_width = circuit.main_width + plan.opening_width();
      assert!(new_width < old_width);
      assert!(plan.quotient_degree <= 1 << commitment.log_blowup);
      assert_eq!(
        plan.max_constraint_degree,
        circuit.graph.max_constraint_degree.max(
          multi_stark::lookup::logup_max_degree(
            &circuit.graph,
            plan.group_size
          )
        ) as usize
      );
      eprintln!(
        "circuit {index}: width {old_width} -> {new_width}, group {} -> {}, quotient {} -> {}",
        circuit.lookup_group_size,
        plan.group_size,
        circuit.quotient_degree(),
        plan.quotient_degree,
      );
      after += new_width;
      changes += 1;
      histogram[plan.group_size] += 1;
    }
    assert!(changes > 0);
    eprintln!(
      "Aggregate key, all {} circuits: committed width {before} -> {after}; {changes} changed; new group histogram {histogram:?}",
      system.circuits.len()
    );
  }
}
