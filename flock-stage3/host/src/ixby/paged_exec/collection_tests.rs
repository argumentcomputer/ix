use super::*;
use crate::ixby::{
  ixbf::{self, DecodeLimits},
  memory_log::MemoryBatch,
  paged_frame::{HEAP, LOCALS, Phase},
  paged_value::{ARRAY_TAG, FLAT_ARRAY},
};
use flock_prover::circuit::builder::GateType;

fn natural(mut n: u128) -> Vec<u8> {
  let mut out = Vec::new();
  loop {
    let b = n as u8 & 127;
    n >>= 7;
    out.push(b | if n == 0 { 0 } else { 128 });
    if n == 0 {
      return out;
    }
  }
}
fn header(magic: &[u8]) -> Vec<u8> {
  magic.iter().copied().chain([1, 0, 0, 0, 2, 0, 0, 0]).collect()
}
fn local(i: usize) -> Vec<u8> {
  [vec![0], natural(i as u128)].concat()
}
fn nat(n: u128) -> Vec<u8> {
  [vec![1, 0], natural(n)].concat()
}
fn word(n: u32) -> Vec<u8> {
  [vec![1, 3], n.to_le_bytes().to_vec()].concat()
}
fn bytes(data: &[u8]) -> Vec<u8> {
  [vec![1, 6], natural(data.len() as u128), data.to_vec()].concat()
}
fn field(n: u64) -> Vec<u8> {
  [vec![1, 4], n.to_le_bytes().to_vec()].concat()
}
fn image(
  arity: usize,
  ops: &[(u8, Vec<Vec<u8>>)],
  ret: usize,
  fuel: u128,
  limit: u128,
) -> Vec<u8> {
  let mut out = header(b"IXBF");
  for n in [1, 0, (ops.len() + 1) as u128, 64, 3, 0, 4096, 128, 0, limit, fuel]
  {
    out.extend(natural(n));
  }
  out.extend([0, 0, 1]);
  out.extend(natural(arity as u128));
  out.push(0);
  out.extend(natural((ops.len() + 1) as u128));
  for (i, (opcode, args)) in ops.iter().enumerate() {
    out.extend(natural((arity + i) as u128));
    out.extend([0, 1, *opcode]);
    out.extend(natural(args.len() as u128));
    for arg in args {
      out.extend(arg);
    }
    out.extend(natural((i + 1) as u128));
  }
  out.extend(natural((arity + ops.len()) as u128));
  out.push(1);
  out.extend(local(ret));
  out
}
fn input(values: &[Vec<u8>]) -> Vec<u8> {
  [header(b"IXFI"), natural(values.len() as u128), values.concat()].concat()
}
fn run(
  image: &mut NativeImage,
) -> anyhow::Result<(NativeMachine, MemoryBatch<'_>, Vec<RowAdvice>)> {
  let mut machine = image.machine()?;
  let mut memory = MemoryBatch::new(&mut image.memory);
  let mut rows = Vec::new();
  while let Some(chip) = machine.next_chip()? {
    anyhow::ensure!(rows.len() < 100_000, "collection fixture did not halt");
    rows.push(machine.step(&mut memory).map_err(|err| {
      anyhow::anyhow!("{chip:?} at {}: {err:#}", machine.clock)
    })?);
  }
  assert_eq!(machine.state[0].lo as u8, Phase::Halted as u8);
  Ok((machine, memory, rows))
}
fn array_at(
  memory: &MemoryBatch<'_>,
  value: [F128; 2],
  mut index: u64,
) -> [F128; 2] {
  assert_eq!(value[0].lo, ARRAY_TAG);
  assert!(index < value[0].hi);
  let mut cap = value[0].hi.next_power_of_two();
  let mut pointer = value[1].lo;
  loop {
    if pointer & FLAT_ARRAY != 0 {
      return memory.value((pointer & !FLAT_ARRAY) + index).unwrap();
    }
    if cap == 1 {
      return memory.value(pointer).unwrap();
    }
    let children = memory.value(pointer).unwrap();
    assert_eq!(children[1], F128::ZERO);
    cap /= 2;
    if index < cap {
      pointer = children[0].lo;
    } else {
      pointer = children[0].hi;
      index -= cap;
    }
  }
}
fn bytes_of(memory: &MemoryBatch<'_>, value: [F128; 2]) -> Vec<u8> {
  assert_eq!(value[0], F128::new(6, 0));
  (0..value[1].hi)
    .map(|i| {
      let p = value[1].lo + i;
      let c = memory.value(p >> 5).unwrap();
      let words = [c[0].lo, c[0].hi, c[1].lo, c[1].hi];
      (words[((p & 31) >> 3) as usize] >> ((p & 7) * 8)) as u8
    })
    .collect()
}

#[test]
fn persistent_arrays_cross_every_tree_boundary_and_preserve_old_versions() {
  let mut ops = vec![(49, vec![])];
  for i in 0..33 {
    ops.push((53, vec![local(i), nat(i as u128 + 1)]));
  }
  ops.push((52, vec![local(33), nat(17), nat((1 << 65) + 99)]));
  ops.push((51, vec![local(34), nat(17)]));
  let code = image(0, &ops, 35, ops.len() as u128 + 2, 4096);
  let source = input(&[]);
  let mut loaded =
    NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
  let (machine, memory, rows) = run(&mut loaded).unwrap();
  assert_eq!(machine.state[2..4], [F128::new(8, 0), F128::new(99, 2)]);
  for len in 1..=33 {
    let version = memory.value(LOCALS + len).unwrap();
    assert_eq!(version[0], F128::new(11, len));
    for i in 0..len {
      assert_eq!(
        array_at(&memory, version, i),
        [F128::new(8, 0), F128::new(i + 1, 0)]
      );
    }
  }
  let changed = memory.value(LOCALS + 34).unwrap();
  for i in 0..33 {
    let expected = if i == 17 { F128::new(99, 2) } else { F128::new(i + 1, 0) };
    assert_eq!(array_at(&memory, changed, i), [F128::new(8, 0), expected]);
  }
  let writes = rows
    .iter()
    .flat_map(|r| &r.accesses)
    .filter(|a| a.write && a.address >> 36 == HEAP >> 36)
    .count();
  let expected: usize = (1u64..=33)
    .map(|n| (n.next_power_of_two().ilog2() + 1) as usize)
    .sum::<usize>()
    + 7;
  assert_eq!(writes, expected);
  assert_eq!(machine.state[HEAP_COUNT].lo as usize, expected);
  assert_eq!(machine.state[FUEL], F128::new(0, ops.len() as u64 + 2));
}

#[test]
fn flat_input_arrays_share_spans_on_update_and_accept_arbitrary_values() {
  let mut value = vec![4, 33];
  for i in 0..33 {
    value.extend([0, 0, i]);
  }
  let source = input(&[value]);
  let ops = vec![
    (52, vec![local(0), nat(17), bytes(&[7, 8, 9])]),
    (53, vec![local(1), nat(101)]),
    (51, vec![local(2), nat(17)]),
  ];
  let code = image(1, &ops, 3, 5, 4096);
  let mut loaded =
    NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
  let (machine, memory, _) = run(&mut loaded).unwrap();
  assert_eq!(
    bytes_of(&memory, machine.state[2..4].try_into().unwrap()),
    [7, 8, 9]
  );
  let old = memory.value(LOCALS).unwrap();
  assert!(old[1].lo & FLAT_ARRAY != 0);
  for i in 0..33 {
    assert_eq!(array_at(&memory, old, i), [F128::new(8, 0), F128::new(i, 0)]);
    assert_eq!(
      memory.value(HEAP + i).unwrap(),
      [F128::new(8, 0), F128::new(i, 0)]
    );
  }
  assert_eq!(machine.state[HEAP_COUNT].lo, 33 + 7 + 7);
  let changed = memory.value(LOCALS + 2).unwrap();
  assert_eq!(
    array_at(&memory, changed, 33),
    [F128::new(8, 0), F128::new(101, 0)]
  );
}

#[test]
fn builders_freeze_unaligned_chunks_without_recopying_prefixes_or_mutating_aliases()
 {
  for lengths in [
    vec![],
    vec![0],
    vec![1],
    vec![31, 1, 1],
    vec![32, 0, 33],
    vec![1, 31, 32, 33, 65],
  ] {
    let mut ops = vec![(54, vec![])];
    let mut expected = Vec::new();
    let mut prefix = Vec::new();
    for (i, &len) in lengths.iter().enumerate() {
      let chunk = (0..len).map(|j| (i * 79 + j) as u8).collect::<Vec<_>>();
      ops.push((55, vec![local(i), bytes(&chunk)]));
      expected.extend(&chunk);
      if i == 0 {
        prefix = expected.clone();
      }
    }
    let full = ops.len() - 1;
    let prefix_builder = usize::from(!lengths.is_empty());
    let frozen_prefix = ops.len();
    ops.push((56, vec![local(prefix_builder)]));
    let frozen = ops.len();
    ops.push((56, vec![local(full)]));
    let sliced = ops.len();
    let start = usize::from(!expected.is_empty());
    ops.push((
      42,
      vec![
        local(frozen),
        word(start as u32),
        word((expected.len() - start) as u32),
      ],
    ));
    let empty_slice = ops.len();
    ops.push((42, vec![local(frozen), word(expected.len() as u32), word(0)]));
    let hash = ops.len();
    ops.push((44, vec![local(frozen)]));
    let code = image(0, &ops, hash, ops.len() as u128 + 2, 4096);
    let source = input(&[]);
    let mut loaded =
      NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
    let (machine, memory, rows) = run(&mut loaded).unwrap();
    assert_eq!(
      bytes_of(&memory, memory.value(LOCALS + frozen_prefix as u64).unwrap()),
      prefix,
      "{lengths:?}"
    );
    assert_eq!(
      bytes_of(&memory, memory.value(LOCALS + sliced as u64).unwrap()),
      expected[start..],
      "{lengths:?}"
    );
    assert!(
      bytes_of(&memory, memory.value(LOCALS + empty_slice as u64).unwrap())
        .is_empty()
    );
    assert_eq!(
      bytes_of(&memory, memory.value(LOCALS + frozen as u64).unwrap()),
      expected,
      "{lengths:?}"
    );
    assert_eq!(
      bytes_of(&memory, machine.state[2..4].try_into().unwrap()),
      blake3::hash(&expected).as_bytes(),
      "{lengths:?}"
    );
    assert_eq!(
      machine.state[HEAP_COUNT].lo as usize,
      lengths.iter().filter(|&&n| n != 0).count() * 2
    );
    let copied: u64 = rows
      .iter()
      .filter(|r| r.chip == Chip::BuilderCopy)
      .map(|r| r.before[16].lo - r.after[16].lo)
      .sum();
    assert_eq!(copied as usize, prefix.len() + expected.len());
    // Only the two freezes and hash allocate byte cells; both slices are views.
    assert_eq!(
      machine.state[BYTE_COUNT].lo as usize,
      prefix.len().div_ceil(32) + expected.len().div_ceil(32) + 1
    );
  }
}

#[test]
fn array_bounds_types_fuel_and_builder_capacity_fail_closed() {
  for op in [51, 52] {
    for index in [0, 1, 1 << 80] {
      let mut args = vec![local(0), nat(index)];
      if op == 52 {
        args.push(nat(1));
      }
      let ops = vec![(49, vec![]), (op, args)];
      let code = image(0, &ops, 1, 4, 64);
      let source = input(&[]);
      let mut loaded =
        NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
      assert!(run(&mut loaded).is_err(), "op={op}, index={index}");
    }
  }
  let cases = [
    vec![(49, vec![]), (51, vec![local(0), word(0)])],
    vec![
      (54, vec![]),
      (55, vec![local(0), bytes(&[1])]),
      (55, vec![local(1), bytes(&[2])]),
    ],
  ];
  for ops in cases {
    let code = image(0, &ops, 1, 4, 1);
    let source = input(&[]);
    let mut loaded =
      NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
    assert!(run(&mut loaded).is_err());
  }
  let ops = vec![(49, vec![]), (53, vec![local(0), nat(7)])];
  let source = input(&[]);
  for fuel in [3, 4] {
    let code = image(0, &ops, 1, fuel, 64);
    let mut loaded =
      NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
    assert_eq!(run(&mut loaded).is_ok(), fuel == 4);
  }
}

#[test]
fn field_conversions_use_canonical_representatives_and_full_nat128_reduction() {
  for n in
    [0, 1, 0xffff_ffff_0000_0000, 0xffff_ffff_0000_0001, 1 << 65, u128::MAX]
  {
    let ops = vec![(48, vec![nat(n)]), (47, vec![local(0)])];
    let code = image(0, &ops, 1, 4, 64);
    let source = input(&[]);
    let mut loaded =
      NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
    let (machine, _, _) = run(&mut loaded).unwrap();
    assert_eq!(
      machine.state[2..4],
      [F128::new(8, 0), F128::new((n % 0xffff_ffff_0000_0001) as u64, 0)]
    );
  }
  let ops = vec![(47, vec![field(0xffff_ffff_0000_0000)])];
  let code = image(0, &ops, 0, 3, 64);
  assert!(ixbf::decode_program(&code, DecodeLimits::default()).is_ok());
}

#[test]
fn every_collection_gate_has_canonical_inactive_padding() {
  for kind in MicroKind::ALL {
    if !matches!(kind, MicroKind::Collection(_)) {
      continue;
    }
    let gate = MicroGate::new(3, kind).unwrap();
    let mut out = Vec::new();
    gate.eval(&vec![F128::ZERO; kind.inputs()], &(), &mut out);
    assert_eq!(out, vec![F128::ZERO; kind.outputs()], "{kind:?}");
  }
}

#[test]
fn collection_batches_bind_all_microstate_outputs_and_shared_memory() {
  use crate::{ixby::bits::fill_words, sizing::CountingEmitter};
  let chunk = (0..35).map(|i| i * 7).collect::<Vec<_>>();
  let ops = vec![
    (49, vec![]),
    (53, vec![local(1), nat(37)]),
    (52, vec![local(0), nat(1), local(2)]),
    (51, vec![local(3), nat(1)]),
    (50, vec![local(4)]),
    (54, vec![]),
    (55, vec![local(6), bytes(&chunk)]),
    (55, vec![local(7), bytes(&[251, 252, 253])]),
    (57, vec![local(8)]),
    (56, vec![local(8)]),
  ];
  let code = image(1, &ops, 10, 12, 4096);
  let source = input(&[vec![4, 2, 0, 0, 5, 0, 0, 9]]);
  // Exercise both ordinary and packed, linked state transport.
  for class in [BatchClass::Bytes, BatchClass::SharedCompactLinked] {
    let setup = CompiledPagedExecution::compile(class).unwrap();
    let emission = emit_batch(&mut CountingEmitter::new(), class).unwrap();
    let mut loaded =
      NativeImage::load(&code, &source, DecodeLimits::default()).unwrap();
    let mut machine = loaded.machine().unwrap();
    let mut checked = std::collections::BTreeSet::new();
    while let Some(advice) = machine.batch(class, &mut loaded.memory).unwrap() {
      setup.check_advice(&advice).unwrap();
      let witness = setup.witness(&advice).unwrap();
      for (slot, gate) in emission.execution.gates() {
        let MicroKind::Collection(_) = gate.kind() else {
          continue;
        };
        let index =
          MicroKind::ALL.iter().position(|&k| k == gate.kind()).unwrap();
        if checked.contains(&index) {
          continue;
        }
        let Some(row) =
          witness.rows::<MicroGate>(slot).iter().find(|r| r.0[0] == F128::ONE)
        else {
          continue;
        };
        checked.insert(index);
        let g = MicroGate::new(3, gate.kind()).unwrap();
        let table = g.r1cs();
        let mut bits = vec![false; table.n()];
        g.plan().fill_row(&mut bits[..g.plan().k()], |b| fill_words(&row.0, b));
        assert!(table.satisfies(&bits));
        for at in g.kind().inputs()..g.kind().inputs() + g.kind().outputs() {
          for bit in [0, 63, 64, 127] {
            bits[at * 128 + bit] ^= true;
            assert!(
              !table.satisfies(&bits),
              "{:?} output {at} bit {bit}",
              g.kind()
            );
            bits[at * 128 + bit] ^= true;
          }
        }
      }
    }
    assert_eq!(checked.len(), 11);
    assert_eq!(machine.state[0].lo as u8, Phase::Halted as u8);
    assert_eq!(machine.state[3].hi, 38);
    assert_eq!(machine.state[HEAP_COUNT].lo, 9);
    assert_eq!(machine.state[BYTE_COUNT].lo, 2);
  }
}
