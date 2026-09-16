use super::*;
use crate::{
  ixby::io::{InputLayout, LayoutEmitter, PublicLayout},
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{CircuitShape, GateType, ShapeBuilder, SlotWitness},
  field::F128,
};

pub(super) fn checked_audit(gate: &AuditGate, input: &[F128]) -> F128 {
  let mut bits = vec![false; gate.plan().k()];
  gate
    .plan()
    .fill_row(&mut bits, |bits| crate::ixby::bits::fill_words(input, bits));
  let expected = AuditGate::evaluate(input);
  assert_eq!(crate::ixby::bits::read_words(&bits, 12, 1), [expected]);
  let table = gate.r1cs();
  bits.resize(table.n(), false);
  assert!(table.satisfies(&bits));
  expected
}

#[test]
fn ordered_audit_requires_seed_seal_and_exact_read_after_write_values() {
  let gate = AuditGate::new(3).unwrap();
  let record = |address, time, kind, value| {
    [
      F128::new(address, 0),
      F128::new(time, 0),
      F128::new(kind, 0),
      F128::new(value, 4),
      F128::new(5, 6),
    ]
  };
  let padding =
    [F128::ZERO, F128::ZERO, F128::new(PAD, 0), F128::ZERO, F128::ZERO];
  let records = [
    record(3, 0, SEED, 1),
    record(3, 1, READ, 1),
    record(3, 2, WRITE, 2),
    record(3, 3, READ, 2),
    record(3, u64::MAX, SEAL, 2),
    record(1 << 63, 0, SEED, 7),
    record(1 << 63, u64::MAX, SEAL, 7),
    padding,
  ];
  let mut previous = padding;
  for (i, current) in records.into_iter().enumerate() {
    let mut input = previous.to_vec();
    input.extend(current);
    input.extend([
      F128::new(u64::from(i == 0), 0),
      F128::new(u64::from(i == records.len() - 1), 0),
    ]);
    assert_eq!(checked_audit(&gate, &input), F128::ZERO);
    for word in 5..12 {
      let mut changed = input.clone();
      changed[word].hi ^= 1 << 63;
      let result = checked_audit(&gate, &changed);
      if !(8..10).contains(&word)
        || current[2].lo == READ
        || current[2].lo == SEAL
        || current[2].lo == PAD
      {
        assert_eq!(result, F128::ONE);
      }
    }
    previous = current;
  }
  for previous in records {
    for current in records {
      for flags in [[0, 0], [1, 0], [0, 1]] {
        let mut input = previous.to_vec();
        input.extend(current);
        input.extend(flags.map(|flag| F128::new(flag, 0)));
        checked_audit(&gate, &input);
      }
    }
  }
  // Reads cannot skip initialization, forget a seal, repeat a timestamp,
  // change a high value limb, restart an address, or reappear after padding.
  for (previous, current, first, last) in [
    (padding, records[1], 1, 0),
    (records[1], records[5], 0, 0),
    (records[1], records[1], 0, 0),
    (records[1], records[3], 0, 0),
    (records[4], records[0], 0, 0),
    (padding, records[0], 0, 0),
    (records[0], records[1], 0, 1),
  ] {
    let mut input = previous.to_vec();
    input.extend(current);
    input.extend([F128::new(first, 0), F128::new(last, 0)]);
    assert_eq!(checked_audit(&gate, &input), F128::ONE);
  }
}

pub(super) const ACCESSES: usize = 10;
pub(super) const CELLS: usize = 4;
pub(super) const LOG_OUTPUTS: usize = 4 + ACCESSES * 4;
pub(super) struct LogEmission {
  pub slots: MemoryLogSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn log_emit(
  b: &mut impl CircuitEmitter,
  nu: usize,
  depth: crate::ixby::auth_memory::MemoryDepth,
) -> LogEmission {
  log_emit_counts(b, nu, depth, ACCESSES, CELLS)
}
pub(super) fn log_emit_counts(
  b: &mut impl CircuitEmitter,
  nu: usize,
  depth: crate::ixby::auth_memory::MemoryDepth,
  access_count: usize,
  cell_count: usize,
) -> LogEmission {
  let mut b = LayoutEmitter::new(b);
  let slots = MemoryLogSlots::declare(&mut b, nu, depth).unwrap();
  let root = std::array::from_fn(|_| b.input());
  for word in root {
    b.publish(word);
  }
  let accesses = (0..access_count)
    .map(|_| {
      let address = b.input();
      let write = b.input();
      let value = std::array::from_fn(|_| b.input());
      for word in [address, write, value[0], value[1]] {
        b.publish(word);
      }
      AccessWires { address, write, value }
    })
    .collect::<Vec<_>>();
  let cells = (0..cell_count)
    .map(|_| BoundaryWires {
      address: b.input(),
      opening: crate::ixby::auth_memory::MemoryOpeningWires {
        value: std::array::from_fn(|_| b.input()),
        siblings: (0..depth.bits())
          .map(|_| std::array::from_fn(|_| b.input()))
          .collect(),
      },
      final_value: std::array::from_fn(|_| b.input()),
    })
    .collect::<Vec<_>>();
  let switches =
    (0..MemoryLogSlots::plan(access_count, cell_count).unwrap().switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
  for word in slots.check(&mut b, root, &accesses, &cells, &switches) {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  LogEmission { slots, inputs, public }
}
pub(super) fn log_setup(
  nu: usize,
  depth: crate::ixby::auth_memory::MemoryDepth,
) -> (LogEmission, CircuitShape) {
  let mut b = ShapeBuilder::new(nu);
  let emission = log_emit(&mut b, nu, depth);
  (emission, b.finish().unwrap())
}
pub(super) fn log_fixture(
  depth: crate::ixby::auth_memory::MemoryDepth,
  salt: u64,
) -> (Vec<F128>, Vec<F128>) {
  use crate::ixby::auth_memory::SparseMemory;
  let initial = || {
    let mut memory = SparseMemory::new(depth);
    memory.replace(7, [F128::new(1, salt), F128::new(2, 3)]).unwrap();
    memory.replace(255, [F128::new(9, 8), F128::new(7, 6)]).unwrap();
    memory
  };
  let mut execution = initial();
  let mut private = execution.root().to_vec();
  let mut expected = private.clone();
  let mut records = Vec::new();
  for (i, (address, write, new_value)) in [
    (7, false, [F128::ZERO; 2]),
    (42, true, [F128::new(1, 2), F128::new(3, 4)]),
    (42, false, [F128::ZERO; 2]),
    (7, true, [F128::new(5, 6), F128::new(salt, 8)]),
    (7, false, [F128::ZERO; 2]),
    (7, true, [F128::new(9, 10), F128::new(11, 12)]),
    (255, false, [F128::ZERO; 2]),
    (7, false, [F128::ZERO; 2]),
    (255, true, [F128::ZERO; 2]),
    (255, false, [F128::ZERO; 2]),
  ]
  .into_iter()
  .enumerate()
  {
    let value = if write {
      execution.replace(address, new_value).unwrap();
      new_value
    } else {
      execution.open(address).unwrap().value
    };
    let fields = [
      F128::new(address, 0),
      F128::new(u64::from(write), 0),
      value[0],
      value[1],
    ];
    private.extend(fields);
    expected.extend(fields);
    records.push([
      fields[0],
      F128::new(i as u64 + 1, 0),
      F128::new(if write { WRITE } else { READ }, 0),
      value[0],
      value[1],
    ]);
  }
  let mut boundary = initial();
  for address in [255, 7, 42, 99] {
    let final_value = execution.open(address).unwrap().value;
    let old = boundary.replace(address, final_value).unwrap();
    private.extend(old.words());
    private.extend(final_value);
    records.push([
      F128::new(address, 0),
      F128::ZERO,
      F128::new(SEED, 0),
      old.value[0],
      old.value[1],
    ]);
    records.push([
      F128::new(address, 0),
      F128::new(u64::MAX, 0),
      F128::new(SEAL, 0),
      final_value[0],
      final_value[1],
    ]);
  }
  assert_eq!(boundary.root(), execution.root());
  expected.extend(execution.root());
  let plan = MemoryLogSlots::plan(ACCESSES, CELLS).unwrap();
  records.resize(
    plan.lanes(),
    [F128::ZERO, F128::ZERO, F128::new(PAD, 0), F128::ZERO, F128::ZERO],
  );
  let mut order = (0..plan.lanes()).collect::<Vec<_>>();
  order.sort_by_key(|&i| {
    (records[i][2].lo == PAD, records[i][0].lo, records[i][1].lo)
  });
  let mut destination = vec![0; plan.lanes()];
  for (output, input) in order.into_iter().enumerate() {
    destination[input] = output;
  }
  private.extend(plan.route(&destination).unwrap());
  (private, expected)
}

#[test]
fn authenticated_log_binds_repeated_accesses_boundaries_and_padding() {
  use crate::ixby::auth_memory::MemoryDepth;
  for depth in [8, 16, 64] {
    let depth = MemoryDepth::new(depth).unwrap();
    let nu = 10;
    let mut count = CountingEmitter::new();
    log_emit(&mut count, nu, depth);
    let (emission, shape) = log_setup(nu, depth);
    count.ensure_matches(&shape).unwrap();
    let (private, expected) = log_fixture(depth, u64::MAX);
    assert_eq!(expected.len(), LOG_OUTPUTS);
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
    assert_eq!(
      shape.counts[shape.registry_slot(emission.slots.audit_gate().0)],
      32
    );
    if depth.bits() == 8 {
      let boundary = 2 + ACCESSES * 4;
      for position in [
        2,
        4,
        2 + 2 * 4 + 2,
        boundary,
        boundary + 1,
        boundary + 3,
        boundary + 3 + 2 * depth.bits(),
      ] {
        let mut changed = private.clone();
        changed[position] += F128::ONE;
        assert!(
          std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || shape.run(&emission.inputs.assign(&changed).unwrap(), &[])
          ))
          .is_err(),
          "accepted changed input {position}"
        );
      }
    }
  }
}

fn check_route(destination: &[usize]) {
  let plan = PermutationPlan::new(destination.len()).unwrap();
  let bits = plan.route(destination).unwrap();
  assert_eq!(bits.len(), plan.switches());
  let mut positions = (0..destination.len()).collect::<Vec<_>>();
  let mut at = 0;
  for stage in 0..plan.stages() {
    for (left, right) in plan.pairs(stage) {
      assert!(bits[at] == F128::ZERO || bits[at] == F128::ONE);
      if bits[at] == F128::ONE {
        positions.swap(left, right);
      }
      at += 1;
    }
  }
  for (input, &output) in destination.iter().enumerate() {
    assert_eq!(positions[output], input);
  }
}
fn permutations(values: &mut [usize], at: usize, f: &mut impl FnMut(&[usize])) {
  if at == values.len() {
    f(values);
    return;
  }
  for selected in at..values.len() {
    values.swap(at, selected);
    permutations(values, at + 1, f);
    values.swap(at, selected);
  }
}
#[test]
fn complete_small_permutations_and_large_routes_cover_every_record() {
  for n in [1, 2, 4, 8] {
    permutations(&mut (0..n).collect::<Vec<_>>(), 0, &mut check_route);
  }
  let mut random = 0x123456789abcdef0u64;
  for bits in [4, 5, 8, 10, 14] {
    for _ in 0..8 {
      let mut destination = (0..1 << bits).collect::<Vec<_>>();
      for i in (1..destination.len()).rev() {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        destination.swap(i, random as usize % (i + 1));
      }
      check_route(&destination);
    }
  }
  assert!(PermutationPlan::new(0).is_err());
  assert!(PermutationPlan::new(3).is_err());
  assert!(PermutationPlan::new(1 << 21).is_err());
  let plan = PermutationPlan::new(4).unwrap();
  for invalid in [vec![0, 1], vec![0, 1, 1, 2], vec![0, 1, 2, 4]] {
    assert!(plan.route(&invalid).is_err());
  }
}

#[test]
fn switches_bind_whole_records_boolean_selectors_and_recycled_padding() {
  for words in [1, 5, 16] {
    let gate = SwitchGate::new(words).unwrap();
    let mut input = Vec::new();
    for lane in 0..16 {
      input.push(F128::new(lane % 2, 0));
      for at in 0..2 * words {
        input.push(F128::new((lane + 17) * (at + 19) as u64, !(at as u64)));
      }
    }
    let row = gate.eval(&input, &(), &mut Vec::new());
    let SlotWitness::Element(mut z) =
      gate.witness(std::slice::from_ref(&row), 2)
    else {
      panic!()
    };
    assert!(gate.element_table().satisfies(&z, 2, 1));
    for output in gate.input_count()..gate.input_count() + gate.output_count() {
      z[output << 2] += F128::ONE;
      assert!(!gate.element_table().satisfies(&z, 2, 1));
      z[output << 2] += F128::ONE;
    }
    let mut changed = input;
    changed[0] = F128::new(2, 0);
    let forged = gate.eval(&changed, &(), &mut Vec::new());
    let SlotWitness::Element(forged) = gate.witness(&[forged], 2) else {
      panic!()
    };
    assert!(!gate.element_table().satisfies(&forged, 2, 1));
    for count in [0, 1, 3] {
      let rows = vec![row.clone(); count];
      let SlotWitness::Element(expected) = gate.witness(&rows, 2) else {
        panic!()
      };
      let mut recycled = vec![F128::new(u64::MAX, u64::MAX); expected.len()];
      gate.fill_witness(&rows, 2, &mut recycled);
      assert_eq!(recycled, expected);
      assert!(gate.element_table().satisfies(&recycled, 2, count));
    }
  }
}

pub(super) struct Emission {
  pub slots: PermutationSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(
  b: &mut impl CircuitEmitter,
  plan: PermutationPlan,
  words: usize,
) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots = PermutationSlots::declare(&mut b, words).unwrap();
  let records = (0..plan.lanes())
    .map(|_| (0..words).map(|_| b.input()).collect::<Vec<_>>())
    .collect::<Vec<_>>();
  for record in &records {
    for &word in record {
      b.publish(word);
    }
  }
  let selectors = (0..plan.switches()).map(|_| b.input()).collect::<Vec<_>>();
  let output = slots.permute(&mut b, plan, &records, &selectors);
  for record in output {
    for word in record {
      b.publish(word);
    }
  }
  let (inputs, public) = b.finish();
  Emission { slots, inputs, public }
}
pub(super) fn setup(
  plan: PermutationPlan,
  words: usize,
) -> (Emission, CircuitShape) {
  let nu = plan.rows().max(1).next_power_of_two().ilog2() as usize;
  let mut b = ShapeBuilder::new(nu);
  let emission = emit(&mut b, plan, words);
  (emission, b.finish().unwrap())
}

#[test]
fn counted_fixed_topology_moves_all_record_words() {
  for lanes in [1, 2, 8, 32, 128] {
    let plan = PermutationPlan::new(lanes).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, plan, 5);
    let (emission, shape) = setup(plan, 5);
    count.ensure_matches(&shape).unwrap();
    assert_eq!(
      shape.counts[shape.registry_slot(emission.slots.gate().0)],
      plan.rows()
    );
    let input = (0..lanes * 5)
      .map(|i| F128::new(i as u64, !i as u64))
      .collect::<Vec<_>>();
    let destination = (0..lanes).rev().collect::<Vec<_>>();
    let mut private = input.clone();
    private.extend(plan.route(&destination).unwrap());
    let mut expected = input.clone();
    expected.extend(input.as_chunks::<5>().0.iter().rev().flatten());
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
  }
}

#[test]
#[ignore = "proof-free memory geometry for candidate execution batch sizes"]
fn memory_batch_census() {
  use crate::ixby::auth_memory::MemoryDepth;
  use flock_prover::union::UnionInstance;
  for (accesses, cells) in [(128, 16), (512, 32), (2048, 64), (8192, 128)] {
    for depth in [16, 40, 64] {
      let mut count = CountingEmitter::new();
      log_emit_counts(
        &mut count,
        20,
        MemoryDepth::new(depth).unwrap(),
        accesses,
        cells,
      );
      let nu = count.required_nu(3).unwrap();
      let (registry, counts) = count.registry(nu);
      let union = UnionInstance::new(&registry, counts);
      let plan = MemoryLogSlots::plan(accesses, cells).unwrap();
      eprintln!(
        "{{\"accesses\":{accesses},\"cells\":{cells},\"depth\":{depth},\"nu\":{nu},\"dense_m\":{},\"dense_words\":{},\"committed_words\":{},\"log_rows\":{},\"switch_rows\":{},\"blake3_compressions\":{}}}",
        union.dense_m(),
        union.dense_words(),
        union.committed_words(),
        plan.lanes(),
        plan.rows() + accesses.div_ceil(16),
        cells * 2 * (depth + 1)
      );
      assert!((22..=35).contains(&union.dense_m()));
    }
  }
}
