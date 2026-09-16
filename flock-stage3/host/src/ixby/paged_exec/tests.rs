use super::*;
use crate::{
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    memory_log::MemoryBatch,
    paged_code::{FUNCTIONS, Header, block_address},
    paged_frame::{Action, ActionKind, FrameState, Phase, SCRATCH, Vector},
  },
  sizing::{CountedGate, CountingEmitter},
};
use flock_prover::circuit::builder::{GateType, ShapeBuilder};

pub(super) const BUDGET: u64 = 16_000_000_000;
pub(super) fn fixture() -> (BatchAdvice, Vec<RowAdvice>) {
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let nat = |n: u128| [F128::new(8, 0), F128::new(n as u64, (n >> 64) as u64)];
  let local = |n| [F128::ZERO, F128::new(n, 0)];
  let mut block = |function, block, header: Header, operands: &[[F128; 2]]| {
    let address = block_address(function, block);
    memory.replace(address, header.words()).unwrap();
    for (i, value) in operands.iter().enumerate() {
      memory.replace(address + 1 + i as u64, *value).unwrap();
    }
  };
  block(
    680,
    184,
    Header {
      operation: 1,
      primitive: 0,
      operands: 2,
      arguments: 2,
      target: 185,
      ..Header::default()
    },
    &[nat((1u128 << 65) + 3), nat(5)],
  );
  block(
    680,
    185,
    Header {
      locals: 1,
      operation: 5,
      reference: 671,
      operands: 1,
      arguments: 1,
      target: 186,
      ..Header::default()
    },
    &[local(0)],
  );
  block(
    680,
    186,
    Header { locals: 2, instruction: 1, operands: 1, ..Header::default() },
    &[local(1)],
  );
  block(
    671,
    180,
    Header {
      locals: 1,
      operation: 1,
      primitive: 2,
      operands: 2,
      arguments: 2,
      target: 181,
      ..Header::default()
    },
    &[local(0), nat(2)],
  );
  block(
    671,
    181,
    Header { locals: 2, instruction: 1, operands: 1, ..Header::default() },
    &[local(1)],
  );
  memory
    .replace(
      FUNCTIONS + 671,
      [F128::new(1 | (180 << 8) | (182 << 16), 0), F128::ZERO],
    )
    .unwrap();
  let parameters =
    [F128::new(4096, 4096), F128::new(BUDGET, 0), F128::new(4096, 0)];
  let initial = initial_state(FrameState::eval(680, 184, 0, 0).words(), BUDGET);
  let mut machine = NativeMachine::new(initial, 0, parameters).unwrap();
  let mut batch = MemoryBatch::new(&mut memory);
  let mut rows = Vec::new();
  while machine.next_chip().unwrap().is_some() {
    assert!(rows.len() < 100);
    rows.push(machine.step(&mut batch).unwrap());
  }
  assert_eq!(machine.clock, 20);
  assert_eq!(machine.state[0].lo, Phase::Halted as u64);
  assert_eq!(machine.state[2..4], nat((1u128 << 66) + 16));
  assert_eq!(machine.state[FUEL], F128::new(BUDGET - 7, 7));
  assert_eq!(machine.state[CONTROL], F128::ZERO);
  assert_eq!(machine.state[HEADER], F128::ZERO);
  let memory = batch.finish_padded(BatchClass::Small.cells()).unwrap();
  let advice =
    BatchAdvice::new(BatchClass::Small, parameters, &rows, &memory).unwrap();
  (advice, rows)
}

fn micro_input(header: Header, extra: &[F128]) -> Vec<F128> {
  let mut state = initial_state(
    FrameState::eval(680, 184, header.locals, 647).words(),
    BUDGET,
  );
  state[CONTROL] = F128::new(EXECUTE, 0);
  state[HEADER] = header.words()[0];
  [F128::ONE].into_iter().chain(state).chain(extra.iter().copied()).collect()
}
fn micro_checked(kind: MicroKind, input: &[F128]) -> Vec<F128> {
  let gate = MicroGate::new(3, kind).unwrap();
  let mut output = Vec::new();
  gate.eval(input, &(), &mut output);
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  assert_eq!(
    read_words(&bits, gate.input_count(), gate.output_count()),
    output
  );
  let r1cs = gate.r1cs();
  bits.resize(r1cs.n(), false);
  assert!(r1cs.satisfies(&bits));
  output
}
#[test]
fn control_actions_enforce_reference_branch_case_nat_and_tail_call_semantics() {
  let nat = |n| [F128::new(8, 0), F128::new(n, 0)];
  for (instruction, operation, value, kind, target, result) in [
    (
      0,
      0,
      [F128::new(5, 0), F128::ZERO],
      ActionKind::Bind,
      42,
      [F128::new(5, 0), F128::ZERO],
    ),
    (1, 0, nat(7), ActionKind::Return, 0, nat(7)),
    (6, 0, nat(0), ActionKind::Jump, 42, [F128::ZERO; 2]),
    (6, 0, nat(7), ActionKind::Bind, 43, nat(6)),
    (7, 0, [F128::ONE, F128::ONE], ActionKind::Jump, 42, [F128::ZERO; 2]),
    (7, 0, [F128::ONE, F128::ZERO], ActionKind::Jump, 43, [F128::ZERO; 2]),
  ] {
    let header = Header {
      locals: 73,
      instruction,
      operation,
      operands: 1,
      target: if instruction == 1 { 0 } else { 42 },
      other_target: if instruction >= 6 { 43 } else { 0 },
      ..Header::default()
    };
    let input = micro_input(header, &value);
    let out = micro_checked(MicroKind::ControlAction, &input);
    let mut action = Action::new(kind);
    action.target = target;
    action.value = result;
    assert_eq!(&out[..5], &action.words());
    assert_eq!(out[5], F128::ZERO);
    for (at, delta) in [
      (0, F128::ONE),
      (1 + CONTROL, F128::ONE),
      (1 + HEADER, F128::new(1 << 32, 0)),
    ] {
      let mut bad = input.clone();
      bad[at] += delta;
      assert_ne!(
        *micro_checked(MicroKind::ControlAction, &bad).last().unwrap(),
        F128::ZERO
      );
    }
    if instruction == 6 || instruction == 7 {
      let mut bad = input.clone();
      bad[1 + STATE_WORDS] = F128::new(5, 0);
      bad[2 + STATE_WORDS] = F128::ZERO;
      assert_eq!(
        *micro_checked(MicroKind::ControlAction, &bad).last().unwrap(),
        F128::ONE
      );
    }
  }
  for (instruction, operation, reference, kind, target) in [
    (0, 5, 671, ActionKind::Call, 42),
    (0, 6, 0, ActionKind::Call, 42),
    (2, 0, 671, ActionKind::TailCall, 0),
    (3, 0, 0, ActionKind::TailCall, 0),
  ] {
    let header = Header {
      locals: 73,
      instruction,
      operation,
      operands: 2,
      arguments: 2,
      reference,
      target,
      ..Header::default()
    };
    let declared = [F128::new(2 | (180 << 8) | (182 << 16), 0), F128::ZERO];
    let input = micro_input(header, &declared);
    let out = micro_checked(MicroKind::CallAction, &input);
    let mut action = Action::new(kind);
    action.target = target;
    action.callee = if reference == 0 { 680 } else { reference };
    action.entry = 180;
    action.arity = 2;
    action.arguments = Vector { pointer: SCRATCH, count: 2 };
    assert_eq!(&out[..5], &action.words());
    assert_eq!(out[5], F128::ZERO);
    let mut bad = input.clone();
    bad[1 + STATE_WORDS].lo ^= 1;
    assert_eq!(
      *micro_checked(MicroKind::CallAction, &bad).last().unwrap(),
      F128::ONE
    );
  }
}

#[test]
fn instructions_fetch_resolve_compute_call_copy_return_and_halt_in_one_authenticated_batch()
 {
  let class = BatchClass::Small;
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let mut count = CountingEmitter::new();
  emit_batch(&mut count, class).unwrap();
  count.ensure_matches(&shape).unwrap();
  assert!(count.required_nu(3).unwrap() <= class.nu());
  let (advice, rows) = fixture();
  assert_eq!(rows.len(), 20);
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
      let output = read_words(&bits, gate.input_count(), gate.output_count());
      assert_eq!(*output.last().unwrap(), F128::ZERO, "{:?}", gate.kind());
      bits.resize(table.n(), false);
      assert!(table.satisfies(&bits));
    }
  }
  eprintln!(
    "paged instruction batch: {} physical transitions, 7 logical steps, {} public words, {} memory requests",
    rows.len(),
    advice.expected.len(),
    class.accesses()
  );
}
