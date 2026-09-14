use super::*;
use crate::{
  ixby::bits::{fill_words, read_words},
  sizing::CountedGate,
};
use flock_prover::{field::F128, r1cs::BlockR1cs};

pub(super) fn input(
  state: [F128; GRAMMAR_STATE_WORDS],
  event: GrammarEvent,
  bounds: [F128; 3],
  fields: &[F128],
  next: F128,
) -> [F128; GRAMMAR_INPUTS] {
  let mut input = [F128::ZERO; GRAMMAR_INPUTS];
  input[..GRAMMAR_STATE_WORDS].copy_from_slice(&state);
  input[GRAMMAR_STATE_WORDS] = F128::new(event.tag().into(), 0);
  input[GRAMMAR_STATE_WORDS + 1..GRAMMAR_STATE_WORDS + 4]
    .copy_from_slice(&bounds);
  input[GRAMMAR_STATE_WORDS + 4..GRAMMAR_STATE_WORDS + 4 + fields.len()]
    .copy_from_slice(fields);
  input[GRAMMAR_INPUTS - 1] = next;
  input
}

pub(super) fn bits(
  gate: &GrammarStepGate,
  input: &[F128; GRAMMAR_INPUTS],
) -> Vec<bool> {
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  bits
}

pub(super) struct Trace {
  pub gate: GrammarStepGate,
  pub r1cs: BlockR1cs,
  pub state: [F128; GRAMMAR_STATE_WORDS],
  pub steps: usize,
}

impl Trace {
  pub(super) fn new(
    kind: GrammarKind,
    state: [F128; GRAMMAR_STATE_WORDS],
  ) -> Self {
    let gate = GrammarStepGate::new(3, kind).unwrap();
    Self { r1cs: gate.r1cs(), gate, state, steps: 0 }
  }
  pub(super) fn step(
    &mut self,
    event: GrammarEvent,
    bounds: [F128; 3],
    fields: &[F128],
    next: F128,
  ) {
    let input = input(self.state, event, bounds, fields, next);
    let expected = grammar_reference_tests::step(self.gate.kind(), &input)
      .expect(
        "independent integer grammar accepts the reference event schedule",
      );
    let row = bits(&self.gate, &input);
    assert!(tests::satisfies(&self.r1cs, &row));
    let output = read_words(&row, GRAMMAR_INPUTS, GRAMMAR_STATE_WORDS + 1);
    assert_eq!(
      output[GRAMMAR_STATE_WORDS],
      F128::ZERO,
      "grammar {:?} step {} phase {} at {}: event {event:?}; input {input:?}",
      self.gate.kind(),
      self.steps,
      self.state[1].lo & 255,
      self.state[0].lo
    );
    self.state.copy_from_slice(&output[..GRAMMAR_STATE_WORDS]);
    assert_eq!(
      self.state, expected,
      "independent complete-state grammar differential"
    );
    self.steps += 1;
  }
  pub(super) fn finish(&mut self) {
    assert_eq!(self.state[1].lo & 255, grammar::Phase::Done as u64);
    let state = self.state;
    self.step(GrammarEvent::Done, [F128::ZERO; 3], &[], state[0]);
    assert_eq!(self.state, state);
  }
}

pub(super) fn fixture(kind: GrammarKind) -> [F128; GRAMMAR_INPUTS] {
  use grammar::*;
  let mut state = [F128::ZERO; GRAMMAR_STATE_WORDS];
  state[0] = F128::new(0, 64);
  let mut fields = [F128::ZERO; GRAMMAR_EVENT_FIELDS];
  if kind == GrammarKind::Program {
    fields =
      [4, 3, 4, 4, 4, 0, 8, 4096, 99, 99, 123, 0, 2].map(record_tests::word);
    input(
      state,
      GrammarEvent::Header,
      [F128::new(64, 0), F128::ZERO, F128::ZERO],
      &fields,
      F128::new(26, 0),
    )
  } else {
    state[LIMITS + 4] = F128::new(4, 0);
    state[LIMITS + 6] = F128::new(8, 0);
    state[FUNCTIONS] = F128::new(1, 0);
    state[ENTRY_ARITY] = F128::new(2, 0);
    fields[0] = F128::new(if kind == GrammarKind::Input { 2 } else { 1 }, 0);
    let (event, bounds, offset) = if kind == GrammarKind::Input {
      (RecordKind::Input, [4, 2, 8], 13)
    } else {
      (RecordKind::Output, [8, 0, 0], 12)
    };
    input(
      state,
      GrammarEvent::Record(event),
      bounds.map(record_tests::word),
      &fields,
      F128::new(offset, 64),
    )
  }
}

fn differential(
  gate: &GrammarStepGate,
  r1cs: &BlockR1cs,
  input: &[F128; GRAMMAR_INPUTS],
) -> bool {
  let mut row = bits(gate, input);
  assert!(tests::satisfies(r1cs, &row));
  let output = read_words(&row, GRAMMAR_INPUTS, GRAMMAR_STATE_WORDS + 1);
  let expected = grammar_reference_tests::step(gate.kind(), input);
  assert_eq!(
    output[GRAMMAR_STATE_WORDS] == F128::ZERO,
    expected.is_ok(),
    "integer acceptance differential: {input:?}; {expected:?}"
  );
  if let Ok(expected) = expected {
    assert_eq!(output[..GRAMMAR_STATE_WORDS], expected);
    true
  } else {
    row[(GRAMMAR_INPUTS + GRAMMAR_STATE_WORDS) * 128] = false;
    assert!(!tests::satisfies(r1cs, &row));
    false
  }
}

fn local_rows(kind: GrammarKind) -> Vec<[F128; GRAMMAR_INPUTS]> {
  use grammar::*;
  let mut rows = vec![fixture(kind)];
  for p in 1..=20 {
    if (kind == GrammarKind::Program && p == Phase::Value as u64)
      || (kind != GrammarKind::Program && p < Phase::Scalar as u64)
    {
      continue;
    }
    let mut s = [0u128; GRAMMAR_STATE_WORDS];
    s[0] = 40 | (200 << 64);
    s[1] = u128::from(p)
      | ((Phase::FinishBlock as u128) << 8)
      | ((Phase::FinishBlock as u128) << 16)
      | ((if kind == GrammarKind::Program {
        Phase::FinishBlock
      } else {
        Phase::FinishValue
      } as u128)
        << 24)
      | (1 << 32);
    s[LIMITS..LIMITS + 10].fill(64);
    s[CTORS] = 8;
    s[FUNCTIONS] = 8;
    s[FUNCTIONS_LEFT] = u128::from(kind == GrammarKind::Program);
    s[BLOCKS] = 8;
    s[BLOCKS_LEFT] = u128::from(kind == GrammarKind::Program);
    s[CTORS_LEFT] = u128::from(p == Phase::Constructor as u64);
    s[FUNCTION_INDEX] = 3;
    s[LOCALS] = 5;
    s[ITEMS] = 2;
    s[PAYLOAD] = 8;
    s[PENDING] = 3;
    s[SEEN] = 3;
    s[ENTRY_ARITY] = 2;
    s[ARITY] = 2;
    s[FUEL] = u128::MAX;
    let mut f = [0u128; GRAMMAR_EVENT_FIELDS];
    let (event, bounds, variants) = match p {
      1 => (GrammarEvent::Record(RecordKind::Constructor), [64, 0, 0], 1),
      2 => {
        f[0] = 2;
        (GrammarEvent::Record(RecordKind::Count), [64, 0, 0], 1)
      },
      3 => {
        f[..3].copy_from_slice(&[2, 0, 3]);
        (GrammarEvent::Record(RecordKind::Function), [64; 3], 1)
      },
      4 => {
        f[0] = 5;
        (GrammarEvent::Record(RecordKind::Block), [64, 0, 0], 8)
      },
      5 => {
        f[3] = 2;
        (GrammarEvent::Record(RecordKind::Operation), [64, 8, 8], 8)
      },
      6 => (GrammarEvent::Record(RecordKind::Operand), [5, 0, 0], 3),
      7 => {
        f[0] = 2;
        (GrammarEvent::Record(RecordKind::Count), [64, 0, 0], 1)
      },
      8 => (GrammarEvent::Record(RecordKind::Index), [8, 0, 0], 1),
      9 => (GrammarEvent::Record(RecordKind::Metadata), [0; 3], 1),
      10 => (GrammarEvent::Record(RecordKind::Index), [8, 0, 0], 1),
      11 => {
        f[0] = 2;
        (GrammarEvent::Record(RecordKind::Count), [64, 0, 0], 1)
      },
      12 => (GrammarEvent::Record(RecordKind::Alternative), [8, 8, 0], 1),
      13 => (GrammarEvent::Record(RecordKind::Scalar), [0; 3], 7),
      14 => {
        f[0] = 1;
        (GrammarEvent::Natural, [0; 3], 1)
      },
      15 | 17 => {
        f[0] = 2;
        (GrammarEvent::Record(RecordKind::Count), [64, 0, 0], 1)
      },
      16 => (GrammarEvent::StringPayload, [0; 3], 1),
      18 => (GrammarEvent::BytesPayload, [0; 3], 1),
      19 => (GrammarEvent::Record(RecordKind::Value), [64, 8, 60], 4),
      20 => {
        s[0] = 200 | (200 << 64);
        for i in
          [FUNCTIONS_LEFT, BLOCKS_LEFT, CTORS_LEFT, ITEMS, PAYLOAD, PENDING]
        {
          s[i] = 0;
        }
        (GrammarEvent::Done, [0; 3], 1)
      },
      _ => unreachable!(),
    };
    for variant in 0..variants {
      if p == 4 {
        f[1] = variant;
      } else if variants > 1 {
        f[0] = variant;
      }
      let next = if p == 20 {
        200
      } else if p == 16 || p == 18 {
        48
      } else {
        41
      };
      rows.push(input(
        s.map(record_tests::word),
        event,
        bounds.map(record_tests::word),
        &f.map(record_tests::word),
        F128::new(next, 200),
      ));
    }
  }
  rows
}

#[test]
fn grammar_every_production_and_malformed_advice_match_independent_integers() {
  let mut accepted = 0;
  let mut rejected = 0;
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    let gate = GrammarStepGate::new(3, kind).unwrap();
    let r1cs = gate.r1cs();
    for input in local_rows(kind) {
      assert!(differential(&gate, &r1cs, &input));
      accepted += 1;
      for index in 0..GRAMMAR_INPUTS {
        for bit in [0, 63, 64, 127] {
          let mut changed = input;
          if bit < 64 {
            changed[index].lo ^= 1 << bit;
          } else {
            changed[index].hi ^= 1 << (bit - 64);
          }
          if differential(&gate, &r1cs, &changed) {
            accepted += 1;
          } else {
            rejected += 1;
          }
        }
      }
    }
  }
  assert!(accepted > 1000 && rejected > 1000);
  eprintln!(
    "grammar adversarial integer differential: {accepted} accepted, {rejected} rejected"
  );
}

#[test]
fn grammar_every_output_padding_bit_and_fixed_count_stripe_is_bound() {
  use crate::sizing::{CircuitEmitter, CountingEmitter};
  use flock_prover::circuit::builder::ShapeBuilder;
  fn emit(b: &mut impl CircuitEmitter, gate: GrammarStepGate) {
    let slot = GrammarStepSlot::declare(b, gate);
    let mut state = GrammarState(std::array::from_fn(|_| b.input()));
    for _ in 0..3 {
      let tag = b.input();
      let bounds = std::array::from_fn(|_| b.input());
      let fields = std::array::from_fn(|_| b.input());
      let next = b.input();
      state = slot.step(b, state, tag, bounds, fields, next);
    }
    for field in state.0 {
      b.publish(field);
    }
  }
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    let gate = GrammarStepGate::new(3, kind).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, gate.clone());
    assert!(gate.plan.get().is_none());
    let mut shape = ShapeBuilder::new(3);
    emit(&mut shape, gate.clone());
    let shape = shape.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    assert_eq!(count.registry(3).1, shape.counts);
    let input = fixture(kind);
    let mut row = bits(&gate, &input);
    let r1cs = gate.r1cs();
    tests::output_bits_are_bound(
      &r1cs,
      &mut row,
      GRAMMAR_INPUTS * 128,
      gate.output_count() * 128,
    );
    row[gate.plan().k() - 1] = true;
    assert!(!tests::satisfies(&r1cs, &row));
    let good = GrammarStepRow(input);
    for rows in [vec![], vec![good.clone()], vec![good; 5]] {
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
    eprintln!(
      "grammar {kind:?}: k_log={}, useful_bits={}",
      gate.plan().k_log(),
      gate.plan().useful_bits()
    );
  }
}

#[test]
fn grammar_forest_completion_matches_an_independent_stack_exhaustively() {
  use grammar::*;
  let gate = GrammarStepGate::new(3, GrammarKind::Input).unwrap();
  let r1cs = gate.r1cs();
  let mut accepted = 0;
  let mut rejected = 0;
  for count in 0..=4u32 {
    for encoded in 0..3usize.pow(count) {
      let mut encoded = encoded;
      let children: Vec<usize> = (0..count)
        .map(|_| {
          let n = encoded % 3;
          encoded /= 3;
          n
        })
        .collect();
      for roots in 0..=3usize {
        // This explicit stack is deliberately independent of the circuit's
        // aggregate pending counter. Preorder degrees determine unique edges.
        let mut stack = vec![roots];
        let mut expected = true;
        for children in &children {
          while stack.last() == Some(&0) {
            stack.pop();
          }
          let Some(parent) = stack.last_mut() else {
            expected = false;
            break;
          };
          *parent -= 1;
          if *children != 0 {
            stack.push(*children);
          }
        }
        while stack.last() == Some(&0) {
          stack.pop();
        }
        expected &= stack.is_empty();
        let length = 13
          + children.iter().map(|n| if *n == 0 { 1 } else { 3 }).sum::<u64>();
        let mut s = [F128::ZERO; GRAMMAR_STATE_WORDS];
        s[0] = F128::new(0, length);
        s[FUNCTIONS] = F128::new(2, 0);
        s[LIMITS + 4] = F128::new(3, 0);
        s[LIMITS + 6] = F128::new(4, 0);
        s[ENTRY_ARITY] = F128::new(roots as u64, 0);
        let mut events = vec![(
          GrammarEvent::Record(RecordKind::Input),
          [3, roots as u64, 4],
          vec![F128::new(roots as u64, 0)],
          13,
        )];
        let mut offset = 13;
        for (index, children) in children.iter().enumerate() {
          offset += if *children == 0 { 1 } else { 3 };
          let mut f = vec![F128::ZERO; 6];
          f[0] = F128::new(if *children == 0 { 3 } else { 2 }, 0);
          if *children != 0 {
            f[1] = F128::new(1, 0);
            f[5] = F128::new(*children as u64, 0);
          }
          events.push((
            GrammarEvent::Record(RecordKind::Value),
            [3, 2, 3 - index as u64],
            f,
            offset,
          ));
        }
        events.push((GrammarEvent::Done, [0; 3], vec![], length));
        let mut actual = true;
        for (event, bounds, fields, offset) in events {
          let row = input(
            s,
            event,
            bounds.map(|v| F128::new(v, 0)),
            &fields,
            F128::new(offset, length),
          );
          if !differential(&gate, &r1cs, &row) {
            actual = false;
            break;
          }
          s = grammar_reference_tests::step(GrammarKind::Input, &row).unwrap();
        }
        assert_eq!(actual, expected, "roots={roots}; degrees={children:?}");
        if actual {
          accepted += 1;
          assert_eq!(s[SEEN].lo, count as u64);
        } else {
          rejected += 1;
        }
      }
    }
  }
  eprintln!(
    "exhaustive preorder forests: {accepted} complete, {rejected} rejected"
  );
}

#[test]
fn grammar_full_width_carries_exhaustion_and_eof_never_wrap() {
  use grammar::*;
  let gate = GrammarStepGate::new(3, GrammarKind::Input).unwrap();
  let r1cs = gate.r1cs();
  for bit in 0..128 {
    let old = (1u128 << bit) - 1;
    let mut s = [F128::ZERO; GRAMMAR_STATE_WORDS];
    s[0] = F128::new(u64::MAX - 1, u64::MAX);
    s[1] = F128::new(Phase::Value as u64, 0);
    s[PENDING] = F128::new(1, 0);
    s[SEEN] = record_tests::word(old);
    s[FUNCTIONS] = F128::new(1, 0);
    s[LIMITS + 4] = F128::new(3, 0);
    s[LIMITS + 6] = record_tests::word(u128::MAX);
    let bounds = [
      record_tests::word(3),
      record_tests::word(1),
      record_tests::word(u128::MAX - old - 1),
    ];
    let good = input(
      s,
      GrammarEvent::Record(RecordKind::Value),
      bounds,
      &[F128::new(3, 0)],
      F128::new(u64::MAX, u64::MAX),
    );
    assert!(differential(&gate, &r1cs, &good));
    let next =
      grammar_reference_tests::step(GrammarKind::Input, &good).unwrap();
    assert_eq!(next[SEEN], record_tests::word(1u128 << bit));
    let mut bad = good;
    bad[GRAMMAR_INPUTS - 1].lo = 0;
    assert!(!differential(&gate, &r1cs, &bad));
  }
  let mut s = [F128::ZERO; GRAMMAR_STATE_WORDS];
  s[0] = F128::new(40, 41);
  s[1] = F128::new(Phase::Value as u64, 0);
  s[PENDING] = F128::new(1, 0);
  s[FUNCTIONS] = F128::new(1, 0);
  s[LIMITS + 4] = F128::new(3, 0);
  s[LIMITS + 6] = record_tests::word(u128::MAX);
  for (seen, pending, children, remaining) in [
    (u128::MAX, 1, 0, u128::MAX),
    (0, u128::MAX, 2, u128::MAX - 1),
    (u128::MAX - 1, 2, 0, 0),
    (0, 0, 0, u128::MAX - 1),
  ] {
    s[SEEN] = record_tests::word(seen);
    s[PENDING] = record_tests::word(pending);
    let fields = [2, 0, 0, 0, 0, children].map(record_tests::word);
    let row = input(
      s,
      GrammarEvent::Record(RecordKind::Value),
      [3, 1, remaining].map(record_tests::word),
      &fields,
      F128::new(41, 41),
    );
    assert!(!differential(&gate, &r1cs, &row));
  }
  let program = GrammarStepGate::new(3, GrammarKind::Program).unwrap();
  let r1cs = program.r1cs();
  let mut row = local_rows(GrammarKind::Program)
    .into_iter()
    .find(|row| row[1].lo & 255 == Phase::Function as u64)
    .unwrap();
  row[FUNCTION_INDEX] = record_tests::word(u128::MAX);
  assert!(!differential(&program, &r1cs, &row));
  let good = local_rows(GrammarKind::Program)
    .into_iter()
    .find(|row| row[1].lo & 255 == Phase::Done as u64)
    .unwrap();
  for index in
    [FUNCTIONS_LEFT, BLOCKS_LEFT, CTORS_LEFT, ITEMS, PAYLOAD, PENDING]
  {
    let mut bad = good;
    bad[index] = F128::new(1, 0);
    assert!(!differential(&program, &r1cs, &bad));
  }
  let mut bad = good;
  bad[0].lo -= 1;
  bad[GRAMMAR_INPUTS - 1].lo -= 1;
  assert!(!differential(&program, &r1cs, &bad));
}

#[test]
fn grammar_minimal_program_and_empty_input_reach_exact_eof() {
  let mut state = [F128::ZERO; GRAMMAR_STATE_WORDS];
  state[0] = F128::new(0, 33);
  let mut trace = Trace::new(GrammarKind::Program, state);
  let fields =
    [4, 0, 4, 4, 4, 0, 4, 4096, 99, 99, 123, 0, 0].map(record_tests::word);
  trace.step(
    GrammarEvent::Header,
    [F128::new(33, 0), F128::ZERO, F128::ZERO],
    &fields,
    F128::new(26, 0),
  );
  trace.step(
    GrammarEvent::Record(RecordKind::Count),
    [F128::new(4, 0), F128::ZERO, F128::ZERO],
    &[F128::new(1, 0)],
    F128::new(27, 33),
  );
  trace.step(
    GrammarEvent::Record(RecordKind::Function),
    [F128::new(4, 0); 3],
    &[F128::ZERO, F128::ZERO, F128::new(1, 0)],
    F128::new(30, 33),
  );
  trace.step(
    GrammarEvent::Record(RecordKind::Block),
    [F128::new(4, 0), F128::ZERO, F128::ZERO],
    &[F128::ZERO, F128::new(1, 0)],
    F128::new(32, 33),
  );
  trace.step(
    GrammarEvent::Record(RecordKind::Operand),
    [F128::ZERO; 3],
    &[F128::new(2, 0)],
    F128::new(33, 33),
  );
  trace.finish();
  assert_eq!(trace.state[grammar::FUNCTION_INDEX], F128::new(1, 0));
  let mut state = [F128::ZERO; GRAMMAR_STATE_WORDS];
  state[0] = F128::new(0, 13);
  let mut trace = Trace::new(GrammarKind::Input, state);
  trace.step(
    GrammarEvent::Record(RecordKind::Input),
    [F128::ZERO; 3],
    &[F128::ZERO],
    F128::new(13, 13),
  );
  trace.finish();
  eprintln!(
    "grammar k_log={} useful_bits={}",
    trace.gate.plan().k_log(),
    trace.gate.plan().useful_bits()
  );
}
