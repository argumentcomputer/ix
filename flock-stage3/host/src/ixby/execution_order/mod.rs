//! Exact ordering of heterogeneous execution rows. Each semantic consumer
//! supplies its actual before/after state and clock. A fixed whole-record
//! permutation and local audit prove one uninterrupted positive-length chain.
//! This module does not itself establish instruction semantics.
mod gate;
mod linked;
#[cfg(test)]
mod linked_tests;
mod synthesis;
#[cfg(test)]
mod tests;

use crate::{
  ixby::memory_log::{
    PermutationPlan, PermutationSlots, RecordLayout, RoutingKind,
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};
pub use gate::{OrderGate, OrderKind, OrderRow};
pub use linked::linked_routing;

pub const SEED: u64 = 0;
pub const AFTER: u64 = 1;
pub const BEFORE: u64 = 2;
pub const SEAL: u64 = 3;
pub const PAD: u64 = 4;

#[derive(Clone)]
pub struct TransitionWires {
  pub enabled: Wire,
  pub clock: Wire,
  pub before: Vec<Wire>,
  pub after: Vec<Wire>,
}
pub struct BoundaryWires {
  pub clock: Wire,
  pub state: Vec<Wire>,
}
pub struct StateChainSlots {
  words: usize,
  prepare: (SlotId, OrderGate),
  audit: (SlotId, OrderGate),
  matching: Option<(SlotId, OrderGate)>,
  permutation: PermutationSlots,
  kinds: [Wire; 5],
  zero: Wire,
  one: Wire,
  residual: Wire,
  linked: bool,
}
impl StateChainSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    words: usize,
  ) -> Result<Self> {
    Self::declare_with_routing(b, nu, words, RoutingKind::Element)
  }
  pub fn declare_with_routing(
    b: &mut impl CircuitEmitter,
    nu: usize,
    words: usize,
    routing: RoutingKind,
  ) -> Result<Self> {
    Self::declare_with_record_layout(b, nu, words, routing, None)
  }
  pub fn declare_with_record_layout(
    b: &mut impl CircuitEmitter,
    nu: usize,
    words: usize,
    routing: RoutingKind,
    layout: Option<RecordLayout>,
  ) -> Result<Self> {
    Self::declare_inner(b, nu, words, routing, layout, false)
  }
  /// Match after-states and the initial boundary to before-states and the
  /// final boundary. Exact record equality and nonwrapping clocks establish
  /// the chain with half as many routed records as the sorted audit.
  pub fn declare_linked(
    b: &mut impl CircuitEmitter,
    nu: usize,
    words: usize,
    layout: RecordLayout,
  ) -> Result<Self> {
    Self::declare_inner(
      b,
      nu,
      words,
      RoutingKind::BooleanPacked,
      Some(layout),
      true,
    )
  }
  fn declare_inner(
    b: &mut impl CircuitEmitter,
    nu: usize,
    words: usize,
    routing: RoutingKind,
    layout: Option<RecordLayout>,
    linked: bool,
  ) -> Result<Self> {
    ensure!((1..=30).contains(&words), "state chain word capacity");
    let prepare = OrderGate::new(nu, OrderKind::Prepare(words))?;
    let audit = OrderGate::new(
      nu,
      if linked { OrderKind::Endpoints } else { OrderKind::Audit(words) },
    )?;
    Ok(Self {
      words,
      prepare: (b.slot(prepare.clone()), prepare),
      audit: (b.slot(audit.clone()), audit),
      matching: if linked {
        let gate = OrderGate::new(nu, OrderKind::Match(words))?;
        Some((b.slot(gate.clone()), gate))
      } else {
        None
      },
      permutation: if let Some(layout) = layout {
        ensure!(
          routing == RoutingKind::BooleanPacked && layout.words() == words + 2,
          "state record packing layout"
        );
        PermutationSlots::declare_packed(b, nu, layout)?
      } else {
        PermutationSlots::declare_with_routing(b, nu, words + 2, routing)?
      },
      kinds: std::array::from_fn(|i| {
        b.fixed_public_input(F128::new(i as u64, 0))
      }),
      zero: b.fixed_public_input(F128::ZERO),
      one: b.fixed_public_input(F128::ONE),
      residual: b.fixed_public_input(F128::ZERO),
      linked,
    })
  }
  pub fn prepare_gate(&self) -> (SlotId, &OrderGate) {
    (self.prepare.0, &self.prepare.1)
  }
  pub fn audit_gate(&self) -> (SlotId, &OrderGate) {
    (self.audit.0, &self.audit.1)
  }
  pub fn gates(&self) -> impl Iterator<Item = (SlotId, &OrderGate)> {
    [self.prepare_gate(), self.audit_gate()]
      .into_iter()
      .chain(self.matching.iter().map(|(slot, gate)| (*slot, gate)))
  }
  pub fn permutation(&self) -> &PermutationSlots {
    &self.permutation
  }
  pub fn plan(transitions: usize) -> Result<PermutationPlan> {
    let count = transitions
      .checked_mul(2)
      .and_then(|n| n.checked_add(2))
      .and_then(usize::checked_next_power_of_two)
      .ok_or_else(|| anyhow::anyhow!("state chain count overflow"))?;
    PermutationPlan::new(count)
  }
  pub fn linked_plan(transitions: usize) -> Result<PermutationPlan> {
    let count = transitions
      .checked_add(1)
      .and_then(usize::checked_next_power_of_two)
      .ok_or_else(|| anyhow::anyhow!("linked state chain count overflow"))?;
    PermutationPlan::new(count)
  }
  pub fn routing_plan(&self, transitions: usize) -> Result<PermutationPlan> {
    if self.linked {
      Self::linked_plan(transitions)
    } else {
      Self::plan(transitions)
    }
  }
  /// Bind both boundary states/clocks to the caller's statement. Every row's
  /// after-state must be derived by its semantic consumer, not free advice.
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    start: BoundaryWires,
    end: BoundaryWires,
    rows: &[TransitionWires],
    switches: &[Wire],
  ) {
    assert_eq!(start.state.len(), self.words);
    assert_eq!(end.state.len(), self.words);
    if self.linked {
      self.check_linked(b, start, end, rows, switches);
      return;
    }
    let plan = Self::plan(rows.len()).unwrap();
    let mut records = Vec::with_capacity(plan.lanes());
    for row in rows {
      assert_eq!(row.before.len(), self.words);
      assert_eq!(row.after.len(), self.words);
      let mut input = vec![row.enabled, row.clock];
      input.extend(&row.before);
      input.extend(&row.after);
      let out = b.gate(self.prepare.0, &input);
      b.connect(out[4], self.residual);
      let mut before = vec![out[0], out[1]];
      before.extend(&row.before);
      let mut after = vec![out[2], out[3]];
      after.extend(&row.after);
      records.extend([before, after]);
    }
    for (boundary, kind) in [(start, SEED), (end, SEAL)] {
      let mut record = vec![boundary.clock, self.kinds[kind as usize]];
      record.extend(boundary.state);
      records.push(record);
    }
    let mut padding = vec![self.zero; self.words + 2];
    padding[1] = self.kinds[PAD as usize];
    records.resize(plan.lanes(), padding.clone());
    let sorted = self.permutation.permute(b, plan, &records, switches);
    let mut previous = &padding;
    for (i, current) in sorted.iter().enumerate() {
      let mut input = previous.clone();
      input.extend(current);
      input.extend([
        if i == 0 { self.one } else { self.zero },
        if i + 1 == sorted.len() { self.one } else { self.zero },
      ]);
      let out = b.gate(self.audit.0, &input);
      b.connect(out[0], self.residual);
      previous = current;
    }
  }
}

/// Untrusted routing advice only. All clocks, records and order are checked
/// independently inside the circuit, including full high limbs and padding.
pub fn routing(records: &[Vec<F128>]) -> Result<Vec<F128>> {
  let plan = PermutationPlan::new(records.len())?;
  ensure!(records.iter().all(|r| r.len() >= 2), "state record length");
  let mut order = (0..records.len()).collect::<Vec<_>>();
  order.sort_by_key(|&i| {
    (records[i][1].lo == PAD, records[i][0].lo, records[i][1].lo)
  });
  let mut destination = vec![0; records.len()];
  for (to, from) in order.into_iter().enumerate() {
    destination[from] = to;
  }
  plan.route(&destination)
}
