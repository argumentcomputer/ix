use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    memory_log::MemoryBatch,
    paged_code::{Header, block_address},
    paged_frame::{FrameState, LOCALS, Phase},
    paged_value::{DYNAMIC_BYTES, INPUT_BYTES},
  },
  sizing::{CountedGate, CountingEmitter},
};
use flock_prover::circuit::builder::{GateType, ShapeBuilder};

const BUDGET: u64 = tests::BUDGET;
fn scalar(tag: u64, n: u64) -> [F128; 2] {
  [F128::new(tag, 0), F128::new(n, 0)]
}
fn local(n: u64) -> [F128; 2] {
  scalar(0, n)
}
fn word(n: u64) -> [F128; 2] {
  scalar(2, n)
}
fn put(
  memory: &mut SparseMemory,
  block: u8,
  header: Header,
  args: &[[F128; 2]],
) {
  let base = block_address(0, block);
  memory.replace(base, header.words()).unwrap();
  for (i, arg) in args.iter().enumerate() {
    memory.replace(base + i as u64 + 1, *arg).unwrap();
  }
}
fn primitive(memory: &mut SparseMemory, block: u8, op: u8, args: &[[F128; 2]]) {
  put(
    memory,
    block,
    Header {
      locals: block,
      operation: 1,
      primitive: op,
      operands: args.len() as u8,
      arguments: args.len() as u8,
      target: block + 1,
      ..Header::default()
    },
    args,
  );
}
fn params(limit: u64) -> [F128; 3] {
  [F128::new(4096, 4096), F128::new(BUDGET, 0), F128::new(4096, limit)]
}
fn initial() -> [F128; STATE_WORDS] {
  initial_state(FrameState::eval(0, 0, 0, 0).words(), BUDGET)
}
fn raw_cells(memory: &mut SparseMemory, base: u64, data: &[u8]) {
  for (i, chunk) in data.chunks(32).enumerate() {
    let mut cell = [0u8; 32];
    cell[..chunk.len()].copy_from_slice(chunk);
    memory
      .replace(
        base + i as u64,
        [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])],
      )
      .unwrap();
  }
}
fn run(
  memory: &mut MemoryBatch<'_>,
  machine: &mut NativeMachine,
) -> Vec<RowAdvice> {
  let mut rows = Vec::new();
  while let Some(chip) = machine.next_chip().unwrap() {
    assert!(rows.len() < 10_000);
    rows.push(
      machine
        .step(memory)
        .unwrap_or_else(|err| panic!("{chip:?} at {}: {err:#}", machine.clock)),
    );
  }
  assert_eq!(machine.state[0], F128::new(Phase::Halted as u64, 0));
  rows
}
fn bytes_of(memory: &MemoryBatch<'_>, value: [F128; 2]) -> Vec<u8> {
  assert_eq!(value[0], F128::new(6, 0));
  (0..value[1].hi)
    .map(|i| {
      let at = value[1].lo + i;
      let cell = memory.value(at >> 5).unwrap();
      let bytes = cell
        .into_iter()
        .flat_map(|w| {
          [w.lo.to_le_bytes(), w.hi.to_le_bytes()].into_iter().flatten()
        })
        .collect::<Vec<_>>();
      bytes[(at & 31) as usize]
    })
    .collect()
}
pub(super) fn fixture() -> (BatchAdvice, Vec<RowAdvice>) {
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  for (block, op, args) in [
    (0, 21, vec![word(0x44332211)]),
    (1, 29, vec![scalar(3, 0x0123456789abcdef)]),
    (2, 41, vec![local(0), local(1)]),
    (3, 42, vec![local(2), word(3), word(8)]),
    (4, 30, vec![local(3)]),
    (5, 42, vec![local(2), word(1), word(4)]),
    (6, 22, vec![local(5)]),
    (7, 40, vec![local(2), word(11)]),
    (8, 39, vec![local(2)]),
    (9, 43, vec![local(0), local(0)]),
    (10, 43, vec![local(0), local(5)]),
    (11, 43, vec![local(0), local(2)]),
    (12, 42, vec![local(2), word(12), word(0)]),
    (13, 41, vec![local(12), local(1)]),
    (14, 44, vec![local(2)]),
  ] {
    primitive(&mut memory, block, op, &args);
  }
  put(
    &mut memory,
    15,
    Header { locals: 15, instruction: 1, operands: 1, ..Header::default() },
    &[local(14)],
  );
  let parameters = params(2 << 20);
  let mut machine = NativeMachine::new(initial(), 0, parameters).unwrap();
  let mut batch = MemoryBatch::new(&mut memory);
  let rows = run(&mut batch, &mut machine);
  assert_eq!(batch.value(LOCALS + 4).unwrap(), scalar(3, 0x23456789abcdef44));
  assert_eq!(batch.value(LOCALS + 6).unwrap(), word(0xef443322));
  assert_eq!(batch.value(LOCALS + 7).unwrap(), word(1));
  assert_eq!(batch.value(LOCALS + 8).unwrap(), word(12));
  assert_eq!(batch.value(LOCALS + 9).unwrap(), scalar(1, 1));
  assert_eq!(batch.value(LOCALS + 10).unwrap(), scalar(1, 0));
  assert_eq!(batch.value(LOCALS + 11).unwrap(), scalar(1, 0));
  assert!(bytes_of(&batch, batch.value(LOCALS + 12).unwrap()).is_empty());
  let value = bytes_of(&batch, [machine.state[2], machine.state[3]]);
  let input =
    [0x11, 0x22, 0x33, 0x44, 0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];
  assert_eq!(value, blake3::hash(&input).as_bytes());
  assert_eq!(machine.state[BYTE_COUNT], F128::new(5, 0));
  assert_eq!(machine.state[FUEL], F128::new(BUDGET - 17, 17));
  eprintln!(
    "byte instructions: {} microsteps, touched {} cells, chips {:?}",
    rows.len(),
    batch.prospective_cells(&[]),
    Chip::ALL.map(|c| rows.iter().filter(|r| r.chip == c).count())
  );
  let memory = batch.finish_padded(BatchClass::Bytes.cells()).unwrap();
  (
    BatchAdvice::new(BatchClass::Bytes, parameters, &rows, &memory).unwrap(),
    rows,
  )
}
pub(super) fn hash_program(
  data: &[u8],
  offset: usize,
) -> (SparseMemory, [F128; 3]) {
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let mut source = vec![0xa5; offset];
  source.extend(data);
  source.extend([0x5a; 64]);
  raw_cells(&mut memory, INPUT_BYTES, &source);
  let pointer =
    if data.is_empty() { 0 } else { (INPUT_BYTES << 5) + offset as u64 };
  let value = [F128::new(6, 0), F128::new(pointer, data.len() as u64)];
  primitive(&mut memory, 0, 44, &[value]);
  put(
    &mut memory,
    1,
    Header { locals: 1, instruction: 1, operands: 1, ..Header::default() },
    &[local(0)],
  );
  (memory, params(2 << 20))
}
pub(super) fn hash_fixture() -> (BatchAdvice, Vec<RowAdvice>) {
  let data = (0..1025).map(|i| (i * 37 + i / 13) as u8).collect::<Vec<_>>();
  let (mut memory, parameters) = hash_program(&data, 31);
  let mut machine = NativeMachine::new(initial(), 0, parameters).unwrap();
  let mut batch = MemoryBatch::new(&mut memory);
  let rows = run(&mut batch, &mut machine);
  assert_eq!(
    bytes_of(&batch, [machine.state[2], machine.state[3]]),
    blake3::hash(&data).as_bytes()
  );
  assert_eq!(machine.state[BYTE_COUNT], F128::ONE);
  let memory = batch.finish_padded(BatchClass::Bytes.cells()).unwrap();
  (
    BatchAdvice::new(BatchClass::Bytes, parameters, &rows, &memory).unwrap(),
    rows,
  )
}
fn check_class(class: BatchClass, advice: &BatchAdvice) {
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let mut count = CountingEmitter::new();
  emit_batch(&mut count, class).unwrap();
  count.ensure_matches(&shape).unwrap();
  assert!(count.required_nu(3).unwrap() <= class.nu());
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
#[test]
fn byte_instructions_and_unaligned_chunk_tree_hash_use_authenticated_cells() {
  let (advice, _) = fixture();
  check_class(BatchClass::Bytes, &advice);
  let (hash, _) = hash_fixture();
  check_class(BatchClass::Bytes, &hash);
}
#[test]
fn streaming_blake3_matches_reference_across_empty_blocks_chunks_and_tree_shapes()
 {
  for len in [
    0, 1, 31, 32, 63, 64, 65, 127, 128, 1023, 1024, 1025, 2048, 2049, 3072,
    4096, 8193,
  ] {
    let data = (0..len).map(|i| (i * 37 + i / 13) as u8).collect::<Vec<_>>();
    for offset in [0, 31] {
      let (mut memory, parameters) = hash_program(&data, offset);
      let mut machine = NativeMachine::new(initial(), 0, parameters).unwrap();
      let mut batch = MemoryBatch::new(&mut memory);
      run(&mut batch, &mut machine);
      assert_eq!(
        bytes_of(&batch, [machine.state[2], machine.state[3]]),
        blake3::hash(&data).as_bytes(),
        "length {len}, offset {offset}"
      );
      assert_eq!(machine.state[FUEL], F128::new(BUDGET - 3, 3));
    }
  }
}

fn evaluate(
  kind: ByteKind,
  state: [F128; STATE_WORDS],
  extra: &[F128],
) -> Vec<F128> {
  let gate = MicroGate::new(3, MicroKind::Byte(kind)).unwrap();
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
fn byte_windows_select_all_unaligned_lengths_and_reject_pointer_and_count_aliases()
 {
  let gate = MicroGate::new(3, MicroKind::Byte(ByteKind::Window)).unwrap();
  let raw = (0..96).map(|i| (i * 37 + 13) as u8).collect::<Vec<_>>();
  let packed =
    raw.as_chunks::<16>().0.iter().map(|w| pack_bytes(w)).collect::<Vec<_>>();
  let mut selected = Vec::new();
  for offset in 0usize..32 {
    for count in 0..=64 {
      let cells = if count == 0 { 0 } else { (offset + count).div_ceil(32) };
      let pointer =
        if count == 0 { 0 } else { (INPUT_BYTES << 5) + offset as u64 };
      let mut extra = vec![F128::new(pointer, 0), F128::new(count as u64, 0)];
      for (i, &value) in packed.iter().enumerate() {
        extra.push(if i / 2 < cells { value } else { F128::ZERO });
      }
      let mut input = vec![F128::ZERO; 1 + STATE_WORDS];
      input[0] = F128::ONE;
      input.extend(&extra);
      let mut out = Vec::new();
      let row = gate.eval(&input, &(), &mut out);
      assert_eq!(out.last(), Some(&F128::ZERO));
      let data = out[..4]
        .iter()
        .flat_map(|w| {
          [w.lo.to_le_bytes(), w.hi.to_le_bytes()].into_iter().flatten()
        })
        .collect::<Vec<_>>();
      assert_eq!(&data[..count], &raw[offset..offset + count]);
      assert!(data[count..].iter().all(|&b| b == 0));
      for i in 0..3 {
        assert_eq!(
          out[4 + 4 * i],
          F128::new(if i < cells { INPUT_BYTES + i as u64 } else { 0 }, 0)
        );
      }
      if offset == 31 && [1, 32, 64].contains(&count) {
        selected.push(row);
      }
    }
  }
  for (pointer, count) in [
    (F128::new(INPUT_BYTES << 5, 1), F128::ONE),
    (F128::new(7 << 41, 0), F128::ONE),
    (F128::new(INPUT_BYTES << 5, 0), F128::new(65, 0)),
    (F128::ZERO, F128::new(0, 1)),
  ] {
    let extra = [
      pointer,
      count,
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
      F128::ZERO,
    ];
    assert_eq!(
      evaluate(ByteKind::Window, [F128::ZERO; STATE_WORDS], &extra).last(),
      Some(&F128::ONE)
    );
  }
  crate::ixby::test_support::padding(
    gate.plan(),
    &selected,
    |row: &MicroRow, bits| fill_words(&row.0, bits),
    |dst| gate.generate_witness_into(&selected, dst),
  );
}

#[test]
fn byte_limits_slice_get_and_field_canonicality_reject_invalid_operations() {
  let mut state = initial();
  state[CONTROL] = F128::new(EXECUTE, 0);
  let bytes = |n| {
    [F128::new(6, 0), F128::new(if n == 0 { 0 } else { INPUT_BYTES << 5 }, n)]
  };
  for (op, args, limit) in [
    (21, vec![word(7)], 3),
    (29, vec![scalar(3, 7)], 7),
    (44, vec![bytes(0)], 31),
    (39, vec![bytes(4)], 3),
    (40, vec![bytes(4), word(4)], 4),
    (42, vec![bytes(4), word(u64::from(u32::MAX)), word(2)], 4),
    (42, vec![bytes(4), word(3), word(2)], 4),
    (41, vec![bytes(3), bytes(3)], 5),
    (22, vec![bytes(3)], 32),
    (30, vec![bytes(9)], 32),
  ] {
    state[HEADER] = Header {
      operation: 1,
      primitive: op,
      operands: args.len() as u8,
      arguments: args.len() as u8,
      target: 1,
      ..Header::default()
    }
    .words()[0];
    let mut extra = args.into_iter().flatten().collect::<Vec<_>>();
    extra.resize(6, F128::ZERO);
    extra.push(F128::new(4096, limit));
    assert_eq!(
      evaluate(ByteKind::Start, state, &extra).last(),
      Some(&F128::ONE),
      "opcode {op}"
    );
  }
  state[HEADER] = Header {
    operation: 1,
    primitive: 30,
    operands: 1,
    arguments: 1,
    target: 1,
    ..Header::default()
  }
  .words()[0];
  let extra = bytes(8)
    .into_iter()
    .chain([F128::ZERO; 4])
    .chain([F128::new(4096, 8)])
    .collect::<Vec<_>>();
  let pending = evaluate(ByteKind::Start, state, &extra);
  assert_eq!(pending.last(), Some(&F128::ZERO));
  let pending = pending[..STATE_WORDS].try_into().unwrap();
  for n in [0xffff_ffff_0000_0001, u64::MAX] {
    assert_eq!(
      evaluate(
        ByteKind::ReadFinish,
        pending,
        &[F128::new(n, 0), F128::ZERO, F128::ZERO, F128::ZERO]
      )
      .last(),
      Some(&F128::ONE)
    );
  }
  assert_eq!(
    evaluate(
      ByteKind::ReadFinish,
      pending,
      &[
        F128::new(0xffff_ffff_0000_0000, 0),
        F128::ZERO,
        F128::ZERO,
        F128::ZERO
      ]
    )
    .last(),
    Some(&F128::ZERO)
  );
}

#[test]
fn hash_batches_carry_chunk_counters_pending_merges_and_the_final_root_digest()
{
  hash_batches(BatchClass::Compact);
}
#[test]
fn shared_memory_batches_preserve_unaligned_hash_windows_and_tree_merges() {
  hash_batches(BatchClass::SharedCompact);
}
fn hash_batches(class: BatchClass) {
  let data = (0..3073).map(|i| (i * 37 + i / 13) as u8).collect::<Vec<_>>();
  let (mut memory, parameters) = hash_program(&data, 31);
  let mut machine = NativeMachine::new(initial(), 0, parameters).unwrap();
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let mut batches = 0;
  let mut pending = 0;
  while machine.next_chip().unwrap().is_some() {
    let before = machine.state;
    let root = memory.root();
    let clock = machine.clock;
    let advice = machine.batch(class, &mut memory).unwrap().unwrap();
    assert_eq!(advice.expected[3], F128::new(clock, 0));
    assert_eq!(advice.expected[4..28], before);
    assert_eq!(advice.expected[28..30], root);
    assert_eq!(advice.expected[31..55], machine.state);
    assert_eq!(advice.expected[55..], memory.root());
    let witness =
      shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
    assert_eq!(
      witness.public,
      emission.public.instantiate(&advice.expected).unwrap()
    );
    if [HASH_BLOCK, HASH_MERGE].contains(&machine.state[CONTROL].lo) {
      pending += 1;
    }
    batches += 1;
    assert!(batches < 100);
  }
  let expected = blake3::hash(&data);
  assert_eq!(
    memory.value(DYNAMIC_BYTES).unwrap(),
    [
      pack_bytes(&expected.as_bytes()[..16]),
      pack_bytes(&expected.as_bytes()[16..])
    ]
  );
  assert!(pending > 10);
  assert_eq!(machine.state[FUEL], F128::new(BUDGET - 3, 3));
  eprintln!(
    "streaming hash split across {batches} batches, {pending} unfinished hash boundaries"
  );
}

#[test]
fn every_inactive_byte_table_is_canonical_including_recycled_padding() {
  for kind in MicroKind::ALL {
    let MicroKind::Byte(_) = kind else {
      continue;
    };
    let gate = MicroGate::new(3, kind).unwrap();
    let input = vec![F128::ZERO; gate.input_count()];
    let mut out = Vec::new();
    let row = gate.eval(&input, &(), &mut out);
    assert!(out.iter().all(|&w| w == F128::ZERO), "{kind:?}");
    let rows = vec![row];
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row: &MicroRow, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}

#[test]
fn byte_append_splices_full_cells_and_resumes_partial_allocations() {
  let class = BatchClass::Compact;
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let mut suspended = 0;
  for (la, lb, oa, ob) in [
    (0, 0, 0, 0),
    (0, 64, 31, 15),
    (1, 64, 31, 31),
    (31, 65, 31, 15),
    (32, 32, 0, 0),
    (33, 17, 31, 5),
    (63, 2, 7, 31),
    (64, 65, 15, 31),
  ] {
    let a = (0..la).map(|i| (i * 17 + 9) as u8).collect::<Vec<_>>();
    let data_b = (0..lb).map(|i| (i * 31 + 37) as u8).collect::<Vec<_>>();
    let expected = a.iter().chain(&data_b).copied().collect::<Vec<_>>();
    let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
    let mut args = Vec::new();
    for (base, data, offset) in
      [(INPUT_BYTES, &a, oa), (INPUT_BYTES + 16, &data_b, ob)]
    {
      let mut source = vec![0xa5; offset];
      source.extend(data);
      source.extend([0x5a; 32]);
      raw_cells(&mut memory, base, &source);
      args.push([
        F128::new(6, 0),
        F128::new(
          if data.is_empty() { 0 } else { (base << 5) + offset as u64 },
          data.len() as u64,
        ),
      ]);
    }
    primitive(&mut memory, 0, 41, &args);
    put(
      &mut memory,
      1,
      Header { locals: 1, instruction: 1, operands: 1, ..Header::default() },
      &[local(0)],
    );
    let mut machine = NativeMachine::new(initial(), 0, params(1024)).unwrap();
    while let Some(advice) = machine.batch(class, &mut memory).unwrap() {
      let witness =
        shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
      assert_eq!(
        witness.public,
        emission.public.instantiate(&advice.expected).unwrap()
      );
      suspended +=
        usize::from(machine.state[CONTROL] == F128::new(BYTE_APPEND, 0));
    }
    let snapshot = MemoryBatch::new(&mut memory);
    assert_eq!(
      bytes_of(&snapshot, [machine.state[2], machine.state[3]]),
      expected
    );
    assert_eq!(
      machine.state[BYTE_COUNT],
      F128::new(expected.len().div_ceil(32) as u64, 0)
    );
    assert_eq!(machine.state[FUEL], F128::new(BUDGET - 3, 3));
  }
  assert!(suspended > 1);
}
