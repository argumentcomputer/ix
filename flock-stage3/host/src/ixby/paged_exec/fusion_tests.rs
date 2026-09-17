//! Differential and adversarial checks for fixed microstep compositions.
use super::*;
use crate::{
  blake3_backend::{Blake3Backend, Blake3CompressionSlots},
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf::DecodeLimits,
    memory_log::MemoryBatch,
    paged_code::{FUNCTIONS, Header, block_address},
    paged_frame::{FrameState, HEAP, LOCALS, Phase, SCRATCH},
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::{CircuitShape, ShapeBuilder};
use std::collections::BTreeSet;

const CLASS: BatchClass = BatchClass::FusedCompact;
fn word(n: u64) -> F128 {
  F128::new(n, 0)
}
fn parameters() -> [F128; 3] {
  [F128::new(4096, 4096), word(tests::BUDGET), word(4096)]
}
fn nat(n: u64) -> [F128; 2] {
  [word(8), word(n)]
}

/// Every omitted event is a read, and every write remains in original order.
/// Compare both the complete state and all cells touched by either path.
fn compare_step(
  old: &mut NativeMachine,
  new: &mut NativeMachine,
  old_memory: &mut MemoryBatch<'_>,
  new_memory: &mut MemoryBatch<'_>,
  end: u64,
) -> (RowAdvice, usize) {
  let row = new.preview_for_class(CLASS, new_memory, end).unwrap();
  let mut original = Vec::new();
  let mut original_rows = Vec::new();
  for _ in 0..row.chip.span() {
    let step = old.step(old_memory).unwrap();
    original_rows.push(quota_tests::CountedRow::from(&step));
    original.extend(step.accesses);
  }
  let transformed = fusion_census::fuse(&original_rows);
  assert_eq!(transformed.len(), 1);
  assert_eq!(transformed[0].chip, row.chip);
  assert_eq!(
    transformed[0].addresses,
    row.accesses.iter().map(|a| a.address).collect::<Vec<_>>()
  );
  new.commit(new_memory, &row).unwrap();
  assert_eq!(old.clock, new.clock);
  assert_eq!(old.state, new.state);
  let writes = |events: &[crate::ixby::memory_log::AccessAdvice]| {
    events
      .iter()
      .filter(|a| a.write)
      .map(|a| (a.address, a.value))
      .collect::<Vec<_>>()
  };
  assert_eq!(writes(&original), writes(&row.accesses));
  for address in original
    .iter()
    .chain(&row.accesses)
    .map(|a| a.address)
    .collect::<BTreeSet<_>>()
  {
    assert_eq!(
      old_memory.value(address).unwrap(),
      new_memory.value(address).unwrap()
    );
  }
  (row, original.len())
}

#[test]
fn fused_batches_check_actual_shared_memory_state_links_and_mid_instruction_stops()
 {
  let setup = CompiledPagedExecution::compile(CLASS).unwrap();
  let (mut memory, params, state) = object_tests::program();
  let mut machine = NativeMachine::new(state, 0, params).unwrap();
  let mut previous: Option<ExecutionStatement> = None;
  let mut batches = 0;
  while machine.next_chip().unwrap().is_some() {
    // Force some cuts through the ordinary interior of a potential fusion.
    let end = if machine.clock < 12 { machine.clock + 1 } else { u64::MAX };
    let advice = machine.batch_until(CLASS, &mut memory, end).unwrap().unwrap();
    setup.check_advice(&advice).unwrap();
    let statement = ExecutionStatement::from_words(&advice.expected).unwrap();
    if let Some(previous) = previous {
      assert_eq!(previous.final_state(), statement.initial());
    }
    previous = Some(statement);
    batches += 1;
    assert!(batches < 100);
  }
  assert_eq!(machine.state[2..4], nat(82));
  assert!(batches > 12);
}

#[test]
fn fused_objects_and_application_preserve_every_state_cell_write_and_boundary()
{
  for end in [1, 2, 3, 4, 5, 17, 41, u64::MAX] {
    let (mut a, params, state) = object_tests::program();
    let (mut b, _, _) = object_tests::program();
    let mut old = NativeMachine::new(state, 0, params).unwrap();
    let mut new = old.clone();
    let mut a = MemoryBatch::new(&mut a);
    let mut b = MemoryBatch::new(&mut b);
    let mut counts = [0; Chip::COUNT];
    let mut original_accesses = 0;
    let mut fused_accesses = 0;
    while new.clock < end && new.next_chip().unwrap().is_some() {
      let (row, original) =
        compare_step(&mut old, &mut new, &mut a, &mut b, end);
      counts[row.chip as usize] += 1;
      original_accesses += original;
      fused_accesses += row.accesses.len();
    }
    assert_eq!(a.finish().unwrap().final_root, b.finish().unwrap().final_root);
    if end == u64::MAX {
      assert!(
        [Chip::FusedControl, Chip::FusedNumeric, Chip::CopyPair]
          .into_iter()
          .all(|c| counts[c as usize] > 0)
      );
      assert!(fused_accesses < original_accesses);
      assert_eq!(new.state[0], word(Phase::Halted as u64));
      assert_eq!(new.state[2..4], nat(82));
    } else {
      assert_eq!(new.clock, end);
    }
  }
}

fn instruction_fixture(
  header: Header,
  operands: &[[F128; 2]],
) -> (SparseMemory, [F128; STATE_WORDS]) {
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  memory.replace(block_address(7, 19), header.words()).unwrap();
  for (i, operand) in operands.iter().enumerate() {
    memory.replace(block_address(7, 19) + 1 + i as u64, *operand).unwrap();
  }
  memory.replace(LOCALS + 128 * 3, nat(7)).unwrap();
  let state = initial_state(
    FrameState::eval(7, 19, header.locals, 3).words(),
    tests::BUDGET,
  );
  (memory, state)
}

#[test]
fn fused_batches_fall_back_when_one_call_exceeds_shared_parent_capacity() {
  let make = || {
    let header = Header {
      locals: 127,
      instruction: 0,
      operation: 5,
      operands: 4,
      arguments: 4,
      reference: 11,
      target: 20,
      ..Header::default()
    };
    let args = [0, 32, 64, 96].map(|i| [F128::ZERO, word(i)]);
    let (mut memory, state) = instruction_fixture(header, &args);
    for i in [0, 32, 64, 96] {
      memory.replace(LOCALS + 128 * 3 + i, nat(i + 7)).unwrap();
    }
    memory
      .replace(FUNCTIONS + 11, [word(4 | 21 << 8 | 22 << 16), F128::ZERO])
      .unwrap();
    (memory, NativeMachine::new(state, 0, parameters()).unwrap())
  };
  let (mut memory, mut machine) = make();
  let (mut original_memory, mut original) = make();
  {
    let view = MemoryBatch::new(&mut memory);
    let row = machine.preview_for_class(CLASS, &view, 10).unwrap();
    assert_eq!(row.chip, Chip::FusedCall4);
    assert!(view.prospective_cells(&row.accesses) <= CLASS.cells());
    assert!(!view.fits_shared(&row.accesses, CLASS.shared_memory().unwrap()));
  }
  let setup = CompiledPagedExecution::compile(CLASS).unwrap();
  let mut batches = 0;
  while machine.clock < 10 {
    let before = machine.clock;
    let advice = machine.batch_until(CLASS, &mut memory, 10).unwrap().unwrap();
    assert!(machine.clock > before);
    setup.check_advice(&advice).unwrap();
    batches += 1;
  }
  assert!(batches > 1);
  let mut original_view = MemoryBatch::new(&mut original_memory);
  while original.clock < 10 {
    original.step(&mut original_view).unwrap();
  }
  assert_eq!(machine.state, original.state);
  assert_eq!(memory.root(), original_view.finish().unwrap().final_root);
}

#[test]
fn fused_batches_authenticate_zero_cell_without_any_dummy_read() {
  let setup = CompiledPagedExecution::compile(CLASS).unwrap();
  // Inspect the verifier's actual wiring, not just the native input aliases.
  // An early connect() followed by later consumers passed native rejection
  // checks in the pinned emitter without adding those cells to the circuit.
  use crate::{ixby::io::PublicWord, sizing::CountingEmitter};
  use flock_prover::circuit::{Cell, CellSlot};
  let mut counter = CountingEmitter::new();
  let emission = emit_batch(&mut counter, CLASS).unwrap();
  let matching =
    setup.shape.registry_slot(emission.execution.forwarding_gate().unwrap().0);
  let circuit = &setup.shape.circuit;
  let cells = circuit.cells();
  let fixed_zero = emission
    .public
    .words()
    .iter()
    .enumerate()
    .filter(|(_, word)| **word == PublicWord::Fixed(F128::ZERO))
    .map(|(p, _)| (cells.num_gate_slots() << CLASS.nu()) + p)
    .collect::<BTreeSet<_>>();
  let count = setup.shape.counts[matching];
  for row in count - 2..count {
    for column in 0..9 {
      let slot = cells
        .slots()
        .iter()
        .position(|slot| {
          matches!(slot, CellSlot::Gate { ty, word }
            if *ty == matching && word.word_col == column)
        })
        .unwrap();
      let cell = cells.cell_index(Cell::new(slot, row));
      let wire = circuit.wires().iter().find(|w| w.contains(&cell)).unwrap();
      if column < 3 {
        assert!(wire.iter().any(|&other| {
          matches!(cells.slots()[other >> CLASS.nu()],
            CellSlot::Gate { ty, .. } if ty != matching)
        }));
      } else {
        assert!(wire.iter().any(|cell| fixed_zero.contains(cell)));
      }
    }
  }
  let cases = [
    ([F128::ZERO; 2], true, true),
    ([F128::ONE, F128::ZERO], true, false),
    ([F128::ZERO, F128::new(0, 1 << 63)], true, false),
    ([F128::ZERO; 2], false, false),
  ];
  for (nil, include_nil, accepted) in cases {
    let header = Header {
      instruction: 0,
      operation: 5,
      reference: 11,
      target: 20,
      ..Header::default()
    };
    let (mut memory, state) = instruction_fixture(header, &[]);
    memory.replace(0, nil).unwrap();
    memory
      .replace(FUNCTIONS + 11, [word(21 << 8 | 22 << 16), F128::ZERO])
      .unwrap();
    let mut machine = NativeMachine::new(state, 0, parameters()).unwrap();
    let mut view = MemoryBatch::new(&mut memory);
    if include_nil {
      view.include_cell(0).unwrap();
    } else {
      // Fill every otherwise-unused leaf with a different untouched cell,
      // leaving zero outside the proof. This must not evade the invariant.
      for address in 1..=CLASS.cells() as u64 - 3 {
        view.include_cell(address).unwrap();
      }
    }
    let row = machine.preview_for_class(CLASS, &view, 2).unwrap();
    assert_eq!(row.chip, Chip::FusedCall0);
    assert!(row.accesses.iter().all(|a| a.address != 0));
    machine.commit(&mut view, &row).unwrap();
    let (boundary, tree) =
      view.finish_shared(CLASS.shared_memory().unwrap()).unwrap();
    let advice =
      BatchAdvice::new_shared(CLASS, parameters(), &[row], &boundary, &tree)
        .unwrap();
    assert_eq!(setup.check_advice(&advice).is_ok(), accepted);
  }
}

fn gadget(chip: Chip) -> (CircuitShape, InputLayout, PublicLayout) {
  let mut builder = ShapeBuilder::new(8);
  let (inputs, public) = {
    let mut b = LayoutEmitter::new(&mut builder);
    let compression =
      Blake3CompressionSlots::declare(&mut b, 8, Blake3Backend::LegacyOptionF)
        .unwrap();
    let slots = ExecutionSlots::declare_fused(&mut b, 8, &compression).unwrap();
    let enabled = b.input();
    let state = std::array::from_fn(|_| b.input());
    let advice =
      (0..chip.advice_words()).map(|_| b.input()).collect::<Vec<_>>();
    let parameters = std::array::from_fn(|_| b.input());
    slots.parameters(&mut b, parameters);
    let step = slots.step(&mut b, chip, enabled, state, &advice, parameters);
    slots.finish_canonical(&mut b);
    for wire in step.state {
      b.publish(wire);
    }
    for access in step.accesses {
      for wire in
        [access.address, access.write, access.value[0], access.value[1]]
      {
        b.publish(wire);
      }
    }
    b.finish()
  };
  (builder.finish().unwrap(), inputs, public)
}
fn row_input(row: &RowAdvice, params: [F128; 3]) -> Vec<F128> {
  [F128::ONE]
    .into_iter()
    .chain(row.before)
    .chain(row.advice.iter().copied())
    .chain(params)
    .collect()
}
fn row_output(row: &RowAdvice) -> Vec<F128> {
  row
    .after
    .into_iter()
    .chain(row.accesses.iter().flat_map(|a| {
      [word(a.address), word(u64::from(a.write)), a.value[0], a.value[1]]
    }))
    .collect()
}
fn matches(
  shape: &CircuitShape,
  input: &InputLayout,
  public: &PublicLayout,
  words: &[F128],
  expected: &[F128],
) -> bool {
  std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    shape.run(&input.assign(words).unwrap(), &[]).public
      == public.instantiate(expected).unwrap()
  }))
  .unwrap_or(false)
}

#[test]
fn fused_consumers_bind_operands_instruction_fuel_and_disabled_rows() {
  for chip in [Chip::FusedControl, Chip::FusedNumeric] {
    let (shape, input, public) = gadget(chip);
    let header = if chip == Chip::FusedControl {
      Header {
        locals: 1,
        instruction: 6,
        operands: 1,
        target: 20,
        other_target: 21,
        ..Header::default()
      }
    } else {
      Header {
        locals: 1,
        operation: 1,
        operands: 2,
        arguments: 2,
        target: 20,
        ..Header::default()
      }
    };
    let operands = [[F128::ZERO, F128::ZERO], nat(13)];
    let count = if chip == Chip::FusedControl { 1 } else { 2 };
    let (mut memory, state) = instruction_fixture(header, &operands[..count]);
    let mut memory = MemoryBatch::new(&mut memory);
    let machine = NativeMachine::new(state, 0, parameters()).unwrap();
    let row = machine.preview_for_class(CLASS, &memory, u64::MAX).unwrap();
    assert_eq!(row.chip, chip);
    let words = row_input(&row, parameters());
    let expected = row_output(&row);
    assert!(matches(&shape, &input, &public, &words, &expected));
    for at in (0..1 + STATE_WORDS + chip.advice_words())
      .chain([1 + STATE_WORDS + chip.advice_words() + 1])
    {
      for delta in [F128::ONE, F128::new(0, 1 << 63)] {
        let mut bad = words.clone();
        bad[at] += delta;
        assert!(
          !matches(&shape, &input, &public, &bad, &expected),
          "{chip:?} mutation {at}"
        );
      }
    }
    // Exact stopping inside each potential fusion uses the original steps.
    for end in 1..u64::from(chip.span()) {
      assert_eq!(
        machine.preview_for_class(CLASS, &memory, end).unwrap().chip,
        Chip::Fetch
      );
    }
    let mut disabled = vec![F128::ZERO; words.len()];
    let n = disabled.len();
    disabled[n - 3..].copy_from_slice(&parameters());
    assert!(matches(
      &shape,
      &input,
      &public,
      &disabled,
      &vec![F128::ZERO; expected.len()]
    ));
    // A malicious producer cannot use a stale scratch cell as an operand.
    memory.write(SCRATCH, nat(999)).unwrap();
    let same = machine.preview_for_class(CLASS, &memory, u64::MAX).unwrap();
    assert_eq!(row.after, same.after);
    assert_eq!(row.advice, same.advice);
  }
}

#[test]
fn paired_copies_check_heap_scratch_final_partial_and_maximum_vectors() {
  let (shape, input, public) = gadget(Chip::CopyPair);
  for (pointer, count, index, base) in [
    (SCRATCH, 2, 0, 0),
    (HEAP + 31, 3, 0, 7),
    (SCRATCH, 64, 62, 64),
    (HEAP + (1 << 36) - 64, 64, 61, 64),
  ] {
    let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
    memory.replace(pointer + index, nat(13)).unwrap();
    memory.replace(pointer + index + 1, nat(17)).unwrap();
    let mut frame = FrameState::eval(7, 19, (base + count) as u8, 3);
    frame.phase = Phase::Copy;
    frame.copy_index = index as u8;
    frame.copy_count = count as u8;
    frame.copy_base = base as u8;
    frame.copy_pointer = pointer;
    let state = initial_state(frame.words(), tests::BUDGET);
    let memory = MemoryBatch::new(&mut memory);
    let machine = NativeMachine::new(state, 17, parameters()).unwrap();
    let row = machine.preview_for_class(CLASS, &memory, u64::MAX).unwrap();
    assert_eq!(row.chip, Chip::CopyPair);
    assert_eq!(row.after[FUEL], row.before[FUEL]);
    let words = row_input(&row, parameters());
    let expected = row_output(&row);
    assert!(matches(&shape, &input, &public, &words, &expected));
    for at in 0..1 + STATE_WORDS + 4 {
      let mut bad = words.clone();
      bad[at] += F128::ONE;
      assert!(
        !matches(&shape, &input, &public, &bad, &expected),
        "copy mutation {at}"
      );
    }
    let mut invalid = words.clone();
    // One remaining copy cannot be inflated into two microsteps.
    invalid[1].hi = (count - 1) | count << 8 | base << 16;
    assert!(!matches(&shape, &input, &public, &invalid, &expected));
    // Copy sources must remain disjoint from the destination locals.
    invalid = words.clone();
    invalid[2] = word(LOCALS + 3 * 128);
    assert!(!matches(&shape, &input, &public, &invalid, &expected));
  }
}

#[test]
fn fused_calls_resolve_before_overlapping_tail_writes_and_bind_each_forwarded_word()
 {
  for (arity, chip) in Chip::FUSED_CALLS.into_iter().enumerate() {
    let (shape, input, public) = gadget(chip);
    for (instruction, operation) in [(0, 5), (0, 6), (2, 0), (3, 0)] {
      let recursive = operation == 6 || instruction == 3;
      let header = Header {
        locals: 4,
        instruction,
        operation,
        operands: arity as u8,
        arguments: arity as u8,
        reference: if recursive { 0 } else { 11 },
        target: if instruction == 0 { 20 } else { 0 },
        ..Header::default()
      };
      let args = (0..arity)
        .rev()
        .map(|i| [F128::ZERO, word(i as u64)])
        .collect::<Vec<_>>();
      let make = || {
        let (mut memory, state) = instruction_fixture(header, &args);
        for i in 0..4 {
          memory.replace(LOCALS + 128 * 3 + i, nat(20 + i)).unwrap();
        }
        memory
          .replace(
            FUNCTIONS + if recursive { 7 } else { 11 },
            [word(arity as u64 | 21 << 8 | 22 << 16), F128::ZERO],
          )
          .unwrap();
        (memory, state)
      };
      let (mut a, state) = make();
      let (mut b, _) = make();
      let mut a = MemoryBatch::new(&mut a);
      let mut b = MemoryBatch::new(&mut b);
      let mut old = NativeMachine::new(state, 17, parameters()).unwrap();
      let mut new = old.clone();
      let (row, _) = compare_step(&mut old, &mut new, &mut a, &mut b, u64::MAX);
      assert_eq!(row.chip, chip);
      assert_eq!(new.state[0].lo as u8, Phase::Eval as u8);
      assert_eq!(new.state[FUEL], F128::new(tests::BUDGET - 1, 1));
      let words = row_input(&row, parameters());
      let expected = row_output(&row);
      assert!(matches(&shape, &input, &public, &words, &expected));
      for at in
        (0..1 + STATE_WORDS + chip.advice_words()).chain([words.len() - 2])
      {
        for delta in [F128::ONE, F128::new(0, 1 << 63)] {
          let mut bad = words.clone();
          bad[at] += delta;
          assert!(
            !matches(&shape, &input, &public, &bad, &expected),
            "{chip:?} mode {instruction}/{operation} word {at}"
          );
        }
      }
      // A wrong function arity cannot skip or append an argument copy.
      let mut bad = words.clone();
      bad[1 + STATE_WORDS + chip.advice_words() - 2].lo ^= 1;
      assert!(!matches(&shape, &input, &public, &bad, &expected));
    }
  }
}

#[test]
#[ignore = "original fixture differential replay, native states and cells, no proof"]
fn original_fused_execution_matches_each_original_boundary() {
  let fixture =
    std::path::PathBuf::from(std::env::var_os("IXBY_FUSION_FIXTURE").unwrap());
  let program = std::fs::read(fixture.join("program.ixby")).unwrap();
  let source = std::fs::read(fixture.join("input.ixbi")).unwrap();
  let mut a =
    NativeImage::load(&program, &source, DecodeLimits::default()).unwrap();
  let mut b =
    NativeImage::load(&program, &source, DecodeLimits::default()).unwrap();
  let mut old = a.machine().unwrap();
  let mut new = b.machine().unwrap();
  let end = std::env::var("IXBY_FUSION_END_CLOCK")
    .map_or(100_000, |s| s.parse().unwrap());
  assert!((1..=1_000_000).contains(&end));
  let compare = std::env::var_os("IXBY_FUSION_COMPARE").is_some();
  old.compare_native_advice = compare;
  new.compare_native_advice = compare;
  let mut a = MemoryBatch::new(&mut a.memory);
  let mut b = MemoryBatch::new(&mut b.memory);
  let mut counts = [0; Chip::COUNT];
  let mut original_accesses = 0;
  let mut fused_accesses = 0;
  while new.clock < end && new.next_chip().unwrap().is_some() {
    let (row, original) = compare_step(&mut old, &mut new, &mut a, &mut b, end);
    counts[row.chip as usize] += 1;
    original_accesses += original;
    fused_accesses += row.accesses.len();
    a.discard_profile_accesses();
    b.discard_profile_accesses();
  }
  assert_eq!(a.finish().unwrap().final_root, b.finish().unwrap().final_root);
  eprintln!(
    "fusion_differential,{},{},{original_accesses},{fused_accesses},{counts:?},{},{}",
    new.clock,
    new.state[FUEL].hi,
    blake3::hash(&program),
    blake3::hash(&source)
  );
}
