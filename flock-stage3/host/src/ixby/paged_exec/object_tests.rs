use super::*;
use crate::{
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    memory_log::MemoryBatch,
    paged_code::{CONSTRUCTORS, FUNCTIONS, Header, block_address},
    paged_frame::{FrameState, HEAP, Phase, SCRATCH},
  },
  sizing::{CountedGate, CountingEmitter},
};
use flock_prover::circuit::builder::{GateType, ShapeBuilder};

const BUDGET: u64 = tests::BUDGET;
fn nat(n: u64) -> [F128; 2] {
  [F128::new(8, 0), F128::new(n, 0)]
}
fn local(n: u64) -> [F128; 2] {
  [F128::ZERO, F128::new(n, 0)]
}
fn erased() -> [F128; 2] {
  [F128::new(5, 0), F128::ZERO]
}
fn put(
  memory: &mut SparseMemory,
  function: u16,
  block: u8,
  header: Header,
  operands: &[[F128; 2]],
) {
  let address = block_address(function, block);
  memory.replace(address, header.words()).unwrap();
  for (i, value) in operands.iter().enumerate() {
    memory.replace(address + 1 + i as u64, *value).unwrap();
  }
}
fn let_header(
  locals: u8,
  operation: u8,
  arguments: u8,
  reference: u16,
  target: u8,
) -> Header {
  Header {
    locals,
    operation,
    operands: arguments + u8::from(matches!(operation, 0 | 3 | 7)),
    arguments,
    reference,
    target,
    ..Header::default()
  }
}
pub(super) fn program() -> (SparseMemory, [F128; 3], [F128; STATE_WORDS]) {
  let mut m = SparseMemory::new(MemoryDepth::new(40).unwrap());
  put(&mut m, 0, 0, let_header(0, 2, 2, 7, 1), &[nat(10), nat(20)]);
  let mut project = let_header(1, 3, 0, 0, 2);
  project.projection = 1;
  put(&mut m, 0, 1, project, &[local(0)]);
  put(
    &mut m,
    0,
    2,
    Header {
      locals: 2,
      instruction: 5,
      operands: 1,
      alternatives: 2,
      ..Header::default()
    },
    &[local(0)],
  );
  m.replace(
    block_address(0, 2) + 128,
    [F128::new(6 | (13 << 8), 0), F128::ZERO],
  )
  .unwrap();
  m.replace(
    block_address(0, 2) + 129,
    [F128::new(7 | (3 << 8), 0), F128::ZERO],
  )
  .unwrap();
  put(&mut m, 0, 3, let_header(4, 4, 1, 1, 4), &[local(2)]);
  put(&mut m, 0, 4, let_header(5, 7, 1, 0, 5), &[local(4), local(1)]);
  put(&mut m, 0, 5, let_header(6, 7, 1, 0, 6), &[local(5), nat(7)]);
  put(&mut m, 0, 6, let_header(7, 4, 0, 2, 7), &[]);
  put(&mut m, 0, 7, let_header(8, 7, 2, 0, 8), &[local(7), nat(5), nat(9)]);
  put(&mut m, 0, 8, let_header(9, 1, 2, 0, 9), &[local(6), local(8)]);
  put(&mut m, 0, 9, let_header(10, 7, 1, 0, 10), &[erased(), nat(1)]);
  let mut project = let_header(11, 3, 0, 0, 11);
  project.projection = u16::MAX;
  put(&mut m, 0, 10, project, &[local(10)]);
  put(&mut m, 0, 11, let_header(12, 7, 0, 0, 12), &[local(9)]);
  put(
    &mut m,
    0,
    12,
    Header {
      locals: 13,
      instruction: 4,
      operands: 2,
      arguments: 1,
      ..Header::default()
    },
    &[local(5), nat(52)],
  );
  put(&mut m, 1, 0, let_header(3, 1, 2, 0, 1), &[local(0), local(1)]);
  put(&mut m, 1, 1, let_header(4, 1, 2, 0, 2), &[local(3), local(2)]);
  put(
    &mut m,
    1,
    2,
    Header { locals: 5, instruction: 1, operands: 1, ..Header::default() },
    &[local(4)],
  );
  put(&mut m, 2, 0, let_header(1, 4, 1, 3, 1), &[local(0)]);
  put(
    &mut m,
    2,
    1,
    Header { locals: 2, instruction: 1, operands: 1, ..Header::default() },
    &[local(1)],
  );
  let mut mul = let_header(2, 1, 2, 0, 1);
  mul.primitive = 2;
  put(&mut m, 3, 0, mul, &[local(0), local(1)]);
  put(
    &mut m,
    3,
    1,
    Header { locals: 3, instruction: 1, operands: 1, ..Header::default() },
    &[local(2)],
  );
  for (function, arity, blocks) in [(1, 3, 3), (2, 1, 2), (3, 2, 2)] {
    m.replace(
      FUNCTIONS + function,
      [F128::new(arity | (blocks << 16), 0), F128::ZERO],
    )
    .unwrap();
  }
  m.replace(CONSTRUCTORS + 7 * 3 + 2, [F128::new(2, 0), F128::ZERO]).unwrap();
  let parameters =
    [F128::new(4096, 4096), F128::new(BUDGET, 0), F128::new(4096, 0)];
  let state = initial_state(FrameState::eval(0, 0, 0, 0).words(), BUDGET);
  (m, parameters, state)
}
pub(super) fn fixture() -> (BatchAdvice, Vec<RowAdvice>) {
  let (mut m, parameters, state) = program();
  let mut machine = NativeMachine::new(state, 0, parameters).unwrap();
  let mut memory = MemoryBatch::new(&mut m);
  let mut rows = Vec::new();
  while let Some(chip) = machine.next_chip().unwrap() {
    assert!(rows.len() < 250);
    let row = machine
      .step(&mut memory)
      .unwrap_or_else(|e| panic!("{chip:?} at clock {}: {e:#}", machine.clock));
    rows.push(row);
  }
  assert_eq!(machine.state[0], F128::new(Phase::Halted as u64, 0));
  assert_eq!(machine.state[2..4], nat(82));
  assert_eq!(memory.value(HEAP).unwrap(), nat(10));
  assert_eq!(memory.value(HEAP + 1).unwrap(), nat(20));
  assert_eq!(memory.value(SCRATCH + 2).unwrap(), nat(52));
  eprintln!("object trace touches {} cells", memory.prospective_cells(&[]));
  let memory = memory.finish_padded(BatchClass::Objects.cells()).unwrap();
  let advice =
    BatchAdvice::new(BatchClass::Objects, parameters, &rows, &memory).unwrap();
  eprintln!(
    "object execution: {} microsteps, {} logical steps, {} allocated fields, chip counts {:?}",
    machine.clock,
    machine.state[FUEL].hi,
    machine.state[HEAP_COUNT].lo,
    Chip::ALL.map(|c| rows.iter().filter(|r| r.chip == c).count())
  );
  (advice, rows)
}

#[test]
fn constructors_closures_partial_exact_excess_and_tail_application_share_authenticated_execution()
 {
  let class = BatchClass::Objects;
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let mut count = CountingEmitter::new();
  emit_batch(&mut count, class).unwrap();
  count.ensure_matches(&shape).unwrap();
  assert!(count.required_nu(3).unwrap() <= class.nu());
  let (advice, _) = fixture();
  let witness =
    shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(
    witness.public,
    emission.public.instantiate(&advice.expected).unwrap()
  );
  for (slot, gate) in emission.execution.gates() {
    let table = MicroGate::new(3, gate.kind()).unwrap().r1cs();
    for row in witness.rows::<MicroGate>(slot) {
      let mut bits = vec![false; gate.plan().k()];
      gate.plan().fill_row(&mut bits, |bits| fill_words(&row.0, bits));
      assert_eq!(
        *read_words(&bits, gate.input_count(), gate.output_count())
          .last()
          .unwrap(),
        F128::ZERO,
        "{:?}",
        gate.kind()
      );
      bits.resize(table.n(), false);
      assert!(table.satisfies(&bits));
    }
  }
}

fn evaluate(
  kind: ObjectKind,
  state: [F128; STATE_WORDS],
  extra: &[F128],
) -> Vec<F128> {
  let gate = MicroGate::new(3, MicroKind::Object(kind)).unwrap();
  let input = [F128::ONE]
    .into_iter()
    .chain(state)
    .chain(extra.iter().copied())
    .collect::<Vec<_>>();
  let mut out = Vec::new();
  gate.eval(&input, &(), &mut out);
  out
}
#[test]
fn immutable_reservations_reject_unallocated_spans_wrong_fields_and_skipped_copies()
 {
  let (_, rows) = fixture();
  let row = rows.iter().find(|r| r.chip == Chip::StoreCopy).unwrap();
  assert_eq!(
    *evaluate(ObjectKind::StoreCopy, row.before, &row.advice).last().unwrap(),
    F128::ZERO
  );
  for (at, value) in [
    (HEAP_COUNT, F128::new(3, 0)),
    (HEAP_COUNT, F128::new(2, 1)),
    (SOURCE_A, F128::new(HEAP, 2)),
    (SOURCE_A, F128::new(SCRATCH + 64, 2)),
    (DESTINATION, F128::new(HEAP + 1, 0)),
    (OLD_HEAP, F128::ONE),
    (CONTROL, F128::new(STORE | (2 << 8) | (2 << 16) | (1 << 24), 0)),
  ] {
    let mut bad = row.before;
    bad[at] = value;
    assert_eq!(
      *evaluate(ObjectKind::StoreCopy, bad, &row.advice).last().unwrap(),
      F128::ONE,
      "field {at}"
    );
  }
  assert_eq!(
    *evaluate(ObjectKind::StoreFinish, row.before, &[]).last().unwrap(),
    F128::ONE
  );
  let project = rows.iter().find(|r| r.chip == Chip::Project).unwrap();
  let mut bad = project.before;
  bad[HEADER].hi |= 2 << 32;
  assert_eq!(
    *evaluate(ObjectKind::ProjectRequest, bad, &project.advice[..2])
      .last()
      .unwrap(),
    F128::ONE
  );
  let case = rows.iter().find(|r| r.chip == Chip::Case).unwrap();
  let mut advice =
    [case.advice[0], case.advice[1], case.advice[3], case.advice[4]];
  advice[2].lo ^= 1;
  assert_eq!(
    *evaluate(ObjectKind::CaseAction, case.before, &advice).last().unwrap(),
    F128::ONE
  );
  let apply =
    rows.iter().find(|r| r.chip == Chip::Apply && r.before[2].lo == 9).unwrap();
  let mut advice = apply.advice.clone();
  advice[0].lo = (advice[0].lo & !255) | 1;
  assert_eq!(
    *evaluate(ObjectKind::ApplyStart, apply.before, &advice).last().unwrap(),
    F128::ONE
  );
}

#[test]
fn fixed_batches_resume_pending_allocations_and_argument_splices_without_losing_state()
 {
  let (whole, _) = fixture();
  let (mut memory, parameters, state) = program();
  let class = BatchClass::Compact;
  let mut machine = NativeMachine::new(state, 0, parameters).unwrap();
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let mut count = CountingEmitter::new();
  emit_batch(&mut count, class).unwrap();
  count.ensure_matches(&shape).unwrap();
  let mut batches = 0;
  let mut pending_copy_boundaries = 0;
  while machine.next_chip().unwrap().is_some() {
    let before = machine.state;
    let clock = machine.clock;
    let root = memory.root();
    let advice = machine.batch(class, &mut memory).unwrap().unwrap();
    assert_eq!(advice.expected[3], F128::new(clock, 0));
    assert_eq!(advice.expected[4..28], before);
    assert_eq!(advice.expected[28..30], root);
    assert_eq!(advice.expected[30], F128::new(machine.clock, 0));
    assert_eq!(advice.expected[31..55], machine.state);
    assert_eq!(advice.expected[55..], memory.root());
    let witness =
      shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      emission.public.instantiate(&advice.expected).unwrap()
    );
    if machine.state[CONTROL].lo as u8 == STORE as u8 {
      pending_copy_boundaries += 1;
    }
    batches += 1;
    assert!(batches < 100);
  }
  assert_eq!(machine.state, whole.expected[31..55]);
  assert_eq!(memory.root(), whole.expected[55..]);
  assert!(pending_copy_boundaries > 1);
  assert!(machine.batch(class, &mut memory).unwrap().is_none());
  eprintln!(
    "object execution split into {batches} batches, {pending_copy_boundaries} suspended-copy boundaries"
  );
}

#[test]
fn heap_capacity_zero_fields_full_vectors_and_empty_apply_follow_integer_boundaries()
 {
  let (_, _, initial) = program();
  for count in [0u8, 1, 64] {
    for old in [0, (1u64 << 36) - u64::from(count)] {
      let mut state = initial;
      state[CONTROL] = F128::new(EXECUTE, 0);
      state[HEADER] = let_header(0, 2, count, 7, 1).words()[0];
      state[HEAP_COUNT] = F128::new(old, 0);
      let decl = [F128::new(u64::from(count), 0), F128::ZERO];
      let out = evaluate(ObjectKind::Construct, state, &decl);
      assert_eq!(out.last(), Some(&F128::ZERO));
      let mut pending: [F128; STATE_WORDS] =
        out[..STATE_WORDS].try_into().unwrap();
      assert_eq!(pending[HEAP_COUNT], F128::new(old + u64::from(count), 0));
      assert_eq!(
        pending[PENDING + 3],
        F128::new(if count == 0 { 0 } else { HEAP + old }, u64::from(count))
      );
      if count != 0 {
        pending[CONTROL].lo |= u64::from(count - 1) << 8;
        let copied = evaluate(ObjectKind::StoreCopy, pending, &nat(7));
        assert_eq!(copied.last(), Some(&F128::ZERO));
        assert_eq!(
          copied[STATE_WORDS],
          F128::new(SCRATCH + u64::from(count - 1), 0)
        );
        assert_eq!(
          copied[STATE_WORDS + 4],
          F128::new(HEAP + old + u64::from(count - 1), 0)
        );
        pending = copied[..STATE_WORDS].try_into().unwrap();
      }
      assert_eq!(
        evaluate(ObjectKind::StoreFinish, pending, &[]).last(),
        Some(&F128::ZERO)
      );
      if count != 0 {
        state[HEAP_COUNT] = F128::new((1 << 36) - u64::from(count) + 1, 0);
        assert_eq!(
          evaluate(ObjectKind::Construct, state, &decl).last(),
          Some(&F128::ONE)
        );
      }
    }
  }
  let mut apply = initial;
  apply[0] = F128::new(Phase::Apply as u64, 0);
  apply[2..4].copy_from_slice(&nat(u64::MAX));
  assert_eq!(
    &evaluate(ObjectKind::ApplyRequest, apply, &[])[..2],
    &[F128::ZERO; 2]
  );
  let out = evaluate(ObjectKind::ApplyStart, apply, &[F128::ZERO; 2]);
  assert_eq!(out.last(), Some(&F128::ZERO));
  assert_eq!(&out[PENDING + 2..PENDING + 4], &nat(u64::MAX));
  apply[4] = F128::new(HEAP, 1);
  apply[HEAP_COUNT] = F128::ONE;
  assert_eq!(
    evaluate(ObjectKind::ApplyRequest, apply, &[]).last(),
    Some(&F128::ONE)
  );
  apply[2..4].copy_from_slice(&erased());
  assert_eq!(
    &evaluate(ObjectKind::ApplyRequest, apply, &[])[..2],
    &[F128::ZERO; 2]
  );
  assert_eq!(
    evaluate(ObjectKind::ApplyStart, apply, &[F128::ZERO; 2]).last(),
    Some(&F128::ZERO)
  );
}

#[test]
fn object_rows_and_recycled_padding_match_complete_matrices() {
  let (_, rows) = fixture();
  for kind in MicroKind::ALL {
    let MicroKind::Object(object) = kind else {
      continue;
    };
    let gate = MicroGate::new(3, kind).unwrap();
    let before = match object {
      ObjectKind::Reference | ObjectKind::Construct => {
        rows.iter().find(|r| r.chip == Chip::Construct).unwrap()
      },
      ObjectKind::Closure => {
        rows.iter().find(|r| r.chip == Chip::Closure).unwrap()
      },
      ObjectKind::OperandRequest | ObjectKind::ApplyInstruction => {
        rows.iter().find(|r| r.chip == Chip::ApplyInstruction).unwrap()
      },
      ObjectKind::ProjectRequest | ObjectKind::ProjectAction => {
        rows.iter().find(|r| r.chip == Chip::Project).unwrap()
      },
      ObjectKind::CaseAction => {
        rows.iter().find(|r| r.chip == Chip::Case).unwrap()
      },
      ObjectKind::ApplyRequest | ObjectKind::ApplyStart => {
        rows.iter().find(|r| r.chip == Chip::Apply).unwrap()
      },
      ObjectKind::StoreRequest | ObjectKind::StoreCopy => {
        rows.iter().find(|r| r.chip == Chip::StoreCopy).unwrap()
      },
      ObjectKind::StoreFinish => {
        rows.iter().find(|r| r.chip == Chip::StoreFinish).unwrap()
      },
    };
    let extra = if object == ObjectKind::CaseAction {
      vec![
        before.advice[0],
        before.advice[1],
        before.advice[3],
        before.advice[4],
      ]
    } else {
      before.advice[..object.extra_inputs()].to_vec()
    };
    let input = [F128::ONE]
      .into_iter()
      .chain(before.before)
      .chain(extra)
      .collect::<Vec<_>>();
    let active = gate.eval(&input, &(), &mut Vec::new());
    let inactive =
      gate.eval(&vec![F128::ZERO; gate.input_count()], &(), &mut Vec::new());
    let mut bad_input = input;
    bad_input[1 + BYTE_COUNT] = F128::new(0, 1);
    let bad = gate.eval(&bad_input, &(), &mut Vec::new());
    let selected = vec![active, inactive, bad];
    crate::ixby::test_support::padding(
      gate.plan(),
      &selected,
      |row: &MicroRow, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&selected, dst),
    );
  }
}
