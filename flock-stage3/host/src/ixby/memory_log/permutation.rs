use super::{SwitchGate, switch::SWITCHES_PER_ROW};
use crate::sizing::{CircuitEmitter, CountedGate};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// A fixed butterfly followed by its reverse. Stages pair lanes at distances
/// 1,2,...,N/2,...,2,1. The setup fixes these edges before seeing any records.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PermutationPlan {
  lanes: usize,
}
impl PermutationPlan {
  pub fn new(lanes: usize) -> Result<Self> {
    ensure!(
      lanes.is_power_of_two() && lanes <= 1 << 20,
      "memory permutation lane capacity"
    );
    Ok(Self { lanes })
  }
  pub fn lanes(self) -> usize {
    self.lanes
  }
  pub fn stages(self) -> usize {
    (self.lanes.ilog2() as usize * 2).saturating_sub(1)
  }
  pub fn switches(self) -> usize {
    self.stages() * (self.lanes / 2)
  }
  pub fn rows(self) -> usize {
    self.stages() * (self.lanes / 2).div_ceil(SWITCHES_PER_ROW)
  }
  pub fn pairs(self, stage: usize) -> impl Iterator<Item = (usize, usize)> {
    assert!(stage < self.stages());
    let exponent = stage.min(self.stages() - 1 - stage);
    let distance = 1 << exponent;
    (0..self.lanes / 2).map(move |pair| {
      let first = (pair / distance) * 2 * distance + pair % distance;
      (first, first + distance)
    })
  }
  /// Untrusted routing advice. `destination[i]` is the output position of
  /// input record i. Changing this advice cannot change the fixed graph or
  /// create/drop records. The caller must constrain the resulting records.
  pub fn route(self, destination: &[usize]) -> Result<Vec<F128>> {
    ensure!(destination.len() == self.lanes, "memory permutation length");
    let mut seen = vec![false; self.lanes];
    for &at in destination {
      ensure!(
        at < self.lanes && !seen[at],
        "memory permutation is not bijective"
      );
      seen[at] = true;
    }
    Ok(
      route(destination)
        .into_iter()
        .flatten()
        .map(|bit| F128::new(u64::from(bit), 0))
        .collect(),
    )
  }
}

fn route(destination: &[usize]) -> Vec<Vec<bool>> {
  let lanes = destination.len();
  if lanes == 1 {
    return Vec::new();
  }
  if lanes == 2 {
    return vec![vec![destination[0] == 1]];
  }
  let mut inverse = vec![0; lanes];
  for (input, &output) in destination.iter().enumerate() {
    inverse[output] = input;
  }
  // Inputs form a degree-two graph: one edge joins an input pair, the other
  // joins inputs destined for an output pair. Alternating colors on each
  // even cycle routes exactly one record through each half of the network.
  let mut colors = vec![None; lanes];
  for start in 0..lanes {
    if colors[start].is_some() {
      continue;
    }
    colors[start] = Some(false);
    let mut queue = vec![start];
    while let Some(at) = queue.pop() {
      let opposite = !colors[at].unwrap();
      for neighbor in [at ^ 1, inverse[destination[at] ^ 1]] {
        if let Some(color) = colors[neighbor] {
          assert_eq!(color, opposite);
        } else {
          colors[neighbor] = Some(opposite);
          queue.push(neighbor);
        }
      }
    }
  }
  let first = (0..lanes / 2).map(|i| colors[2 * i].unwrap()).collect();
  let last = (0..lanes / 2).map(|i| colors[inverse[2 * i]].unwrap()).collect();
  let mut halves = [vec![0; lanes / 2], vec![0; lanes / 2]];
  for (input, &output) in destination.iter().enumerate() {
    halves[usize::from(colors[input].unwrap())][input / 2] = output / 2;
  }
  let upper = route(&halves[0]);
  let lower = route(&halves[1]);
  let mut result = vec![first];
  for (upper, lower) in upper.into_iter().zip(lower) {
    result
      .push(upper.into_iter().zip(lower).flat_map(|(u, l)| [u, l]).collect());
  }
  result.push(last);
  result
}

pub struct PermutationSlots {
  gate: SwitchGate,
  slot: SlotId,
  zero: Wire,
}
impl PermutationSlots {
  pub fn declare(b: &mut impl CircuitEmitter, words: usize) -> Result<Self> {
    let gate = SwitchGate::new(words)?;
    let slot = b.slot(gate.clone());
    Ok(Self { gate, slot, zero: b.fixed_public_input(F128::ZERO) })
  }
  pub fn gate(&self) -> (SlotId, &SwitchGate) {
    (self.slot, &self.gate)
  }
  pub fn permute(
    &self,
    b: &mut impl CircuitEmitter,
    plan: PermutationPlan,
    records: &[Vec<Wire>],
    switches: &[Wire],
  ) -> Vec<Vec<Wire>> {
    let words = self.gate.record_words();
    assert_eq!(records.len(), plan.lanes());
    assert_eq!(switches.len(), plan.switches());
    assert!(records.iter().all(|record| record.len() == words));
    let mut current = records.to_vec();
    let mut advice = switches.iter();
    for stage in 0..plan.stages() {
      let pairs = plan.pairs(stage).collect::<Vec<_>>();
      for batch in pairs.chunks(SWITCHES_PER_ROW) {
        let mut input = Vec::with_capacity(self.gate.input_count());
        for &(left, right) in batch {
          input.push(*advice.next().unwrap());
          input.extend_from_slice(&current[left]);
          input.extend_from_slice(&current[right]);
        }
        input.resize(self.gate.input_count(), self.zero);
        let output = b.gate(self.slot, &input);
        for (&(left, right), result) in
          batch.iter().zip(output.chunks_exact(2 * words))
        {
          current[left].copy_from_slice(&result[..words]);
          current[right].copy_from_slice(&result[words..]);
        }
      }
    }
    assert!(advice.next().is_none());
    current
  }
}
