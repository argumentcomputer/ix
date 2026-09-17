use super::*;
use std::collections::{BTreeMap, VecDeque};

impl StateChainSlots {
  pub(super) fn check_linked(
    &self,
    b: &mut impl CircuitEmitter,
    start: BoundaryWires,
    end: BoundaryWires,
    rows: &[TransitionWires],
    switches: &[Wire],
  ) {
    let plan = Self::linked_plan(rows.len()).unwrap();
    let mut sources = Vec::with_capacity(plan.lanes());
    let mut targets = Vec::with_capacity(plan.lanes());
    for row in rows {
      assert_eq!(row.before.len(), self.words);
      assert_eq!(row.after.len(), self.words);
      let mut input = vec![row.enabled, row.clock];
      input.extend(&row.before);
      input.extend(&row.after);
      let prepared = b.gate(self.prepare_slot(row.span), &input);
      b.connect(self.residual, prepared[4]);
      let record = |clock, state: &[Wire]| {
        [clock, self.zero].into_iter().chain(state.iter().copied()).collect()
      };
      targets.push(record(prepared[0], &row.before));
      sources.push(record(prepared[2], &row.after));
    }
    let residual = b.gate(self.audit.0, &[start.clock, end.clock]);
    b.connect(self.residual, residual[0]);
    sources
      .push([start.clock, self.zero].into_iter().chain(start.state).collect());
    targets.push([end.clock, self.zero].into_iter().chain(end.state).collect());
    let padding = vec![self.zero; self.words + 2];
    sources.resize(plan.lanes(), padding.clone());
    targets.resize(plan.lanes(), padding);
    let linked = self.permutation.permute(b, plan, &sources, switches);
    for (actual, expected) in linked.into_iter().zip(targets) {
      // Direct wire connections merge producers and can create cycles through
      // state consumers. XOR residuals retain the directed witness graph.
      let residuals = b.gate(
        self.matching.as_ref().unwrap().0,
        &actual.into_iter().chain(expected).collect::<Vec<_>>(),
      );
      for residual in residuals {
        // ShapeBuilder appends the second class into the first. Keep the
        // growing zero class first to avoid quadratic copying during setup.
        b.connect(self.residual, residual);
      }
    }
  }
}

/// Routing advice for the unpadded legacy record layout: before/after pairs,
/// followed by seed/seal. The new circuit ignores the record-kind column and
/// matches complete clock/state records. Advice cannot replace circuit checks.
pub fn linked_routing(records: &[Vec<F128>]) -> Result<Vec<F128>> {
  ensure!(
    records.len() >= 2 && records.len().is_multiple_of(2),
    "linked state records"
  );
  let width = records[0].len();
  ensure!(
    width >= 3 && records.iter().all(|r| r.len() == width),
    "linked state record width"
  );
  let count = records.len() / 2 - 1;
  let plan = StateChainSlots::linked_plan(count)?;
  let key = |record: &[F128]| {
    record
      .iter()
      .enumerate()
      .map(|(i, word)| if i == 1 { (0, 0) } else { (word.lo, word.hi) })
      .collect::<Vec<_>>()
  };
  let mut sources = Vec::with_capacity(plan.lanes());
  let mut targets = Vec::with_capacity(plan.lanes());
  for pair in records[..2 * count].as_chunks::<2>().0 {
    targets.push(key(&pair[0]));
    sources.push(key(&pair[1]));
  }
  sources.push(key(&records[2 * count]));
  targets.push(key(&records[2 * count + 1]));
  sources.resize(plan.lanes(), vec![(0, 0); width]);
  targets.resize(plan.lanes(), vec![(0, 0); width]);
  let mut destinations = BTreeMap::<_, VecDeque<usize>>::new();
  for (i, target) in targets.into_iter().enumerate() {
    destinations.entry(target).or_default().push_back(i);
  }
  let destination = sources
    .iter()
    .map(|source| {
      destinations.get_mut(source).and_then(VecDeque::pop_front).ok_or_else(
        || anyhow::anyhow!("linked state record has no matching target"),
      )
    })
    .collect::<Result<Vec<_>>>()?;
  plan.route(&destination)
}
