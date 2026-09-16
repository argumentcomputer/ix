use super::*;
use crate::{
  boolean::write_f128,
  ixby::{
    bits::{fill_words, read_words},
    io::{InputLayout, LayoutEmitter, PublicLayout},
  },
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{CircuitShape, ShapeBuilder},
  field::F128,
};

pub(super) fn checked(gate: &MemoryGate, input: &[F128]) -> Vec<F128> {
  let mut bits = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut bits, |bits| fill_words(input, bits));
  let expected = gate.evaluate(input);
  assert_eq!(read_words(&bits, input.len(), expected.len()), expected);
  let r1cs = gate.r1cs();
  let mut full = vec![false; r1cs.n()];
  full[..bits.len()].copy_from_slice(&bits);
  assert!(r1cs.satisfies(&full));
  expected
}

#[test]
fn address_and_direction_constraints_use_all_u64_bits() {
  for depth in [0, 1, 8, 32, 63, 64] {
    let depth = MemoryDepth::new(depth).unwrap();
    for kind in [MemoryGateKind::Address, MemoryGateKind::Path] {
      let gate = MemoryGate::new(3, depth, kind).unwrap();
      for address in [0, 1, 1 << 31, 1 << 32, 1 << 63, u64::MAX] {
        for level in [0, 1, 31, 32, 63, 64] {
          let mut input = vec![F128::new(address, 0)];
          if kind == MemoryGateKind::Path {
            input.extend([
              F128::new(level, 0),
              F128::new(3, 4),
              F128::new(5, 6),
              F128::new(7, 8),
              F128::new(9, 10),
            ]);
          }
          let result = checked(&gate, &input);
          assert_eq!(
            result.last() == Some(&F128::ZERO),
            depth.admits(address)
              && (kind == MemoryGateKind::Address
                || level < depth.bits() as u64)
          );
          input[0].hi = 1;
          assert_eq!(checked(&gate, &input).last(), Some(&F128::ONE));
          if kind == MemoryGateKind::Address {
            break;
          }
        }
      }
    }
  }
}

#[test]
fn address_outputs_and_recycled_witness_padding_are_constrained() {
  for kind in [MemoryGateKind::Address, MemoryGateKind::Path] {
    let gate = MemoryGate::new(3, MemoryDepth::new(64).unwrap(), kind).unwrap();
    let input = if kind == MemoryGateKind::Address {
      vec![F128::new(u64::MAX, 0)]
    } else {
      vec![
        F128::new(1 << 63, 0),
        F128::new(63, 0),
        F128::new(3, 4),
        F128::new(5, 6),
        F128::new(7, 8),
        F128::new(9, 10),
      ]
    };
    let mut bits = vec![false; gate.r1cs().n()];
    gate
      .plan()
      .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
    let r1cs = gate.r1cs();
    assert!(r1cs.satisfies(&bits));
    for at in
      128 * gate.input_count()..128 * (gate.input_count() + gate.output_count())
    {
      bits[at] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[at] ^= true;
    }
    for count in [0, 1, 7] {
      let rows = vec![MemoryRow(input.clone()); count];
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| {
          for (i, &word) in row.0.iter().enumerate() {
            write_f128(bits, i * 128, word);
          }
        },
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
}

pub(super) struct Emission {
  pub slots: MemoryAccessSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(
  b: &mut impl CircuitEmitter,
  nu: usize,
  depth: MemoryDepth,
) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots = MemoryAccessSlots::declare(&mut b, nu, depth).unwrap();
  let mut root = std::array::from_fn(|_| b.input());
  for word in root {
    b.publish(word);
  }
  for _ in 0..3 {
    let address = b.input();
    let opening = opening(&mut b, depth);
    let value = std::array::from_fn(|_| b.input());
    b.publish(address);
    for word in value {
      b.publish(word);
    }
    root = slots.replace(&mut b, root, address, &opening, value);
  }
  let address = b.input();
  b.publish(address);
  let opening = opening(&mut b, depth);
  let read = slots.read(&mut b, root, address, &opening);
  for word in read.into_iter().chain(root) {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  Emission { slots, inputs, public }
}
pub(super) fn opening(
  b: &mut impl CircuitEmitter,
  depth: MemoryDepth,
) -> MemoryOpeningWires {
  MemoryOpeningWires {
    value: std::array::from_fn(|_| b.input()),
    siblings: (0..depth.bits())
      .map(|_| std::array::from_fn(|_| b.input()))
      .collect(),
  }
}

#[test]
fn allocation_counts_and_read_bounds_are_exact_without_u64_wrap() {
  for bits in [0, 1, 16, 63, 64] {
    let depth = MemoryDepth::new(bits).unwrap();
    let gate = MemoryGate::new(3, depth, MemoryGateKind::Index).unwrap();
    let cap = if bits == 64 { u64::MAX } else { 1 << bits };
    for count in [0, 1, cap - 1, cap, u64::MAX] {
      for index in [0, 1, count.saturating_sub(1), count, u64::MAX] {
        for mode in [0, 1, 2, 3] {
          let input =
            [F128::new(index, 0), F128::new(count, 0), F128::new(mode, 0)];
          let out = checked(&gate, &input);
          let expected = mode <= 1
            && count <= cap
            && depth.admits(index)
            && if mode == 1 {
              index == count && count != u64::MAX
            } else {
              index < count
            };
          assert_eq!(
            out[1] == F128::ZERO,
            expected,
            "bits={bits} input={input:?}"
          );
        }
      }
    }
    for word in 0..3 {
      let mut input = [F128::ZERO, F128::ONE, F128::ZERO];
      input[word].hi = 1 << 63;
      assert_eq!(checked(&gate, &input)[1], F128::ONE);
    }
    let input = [F128::ZERO, F128::ZERO, F128::ONE];
    let mut row = vec![false; gate.r1cs().n()];
    gate
      .plan()
      .fill_row(&mut row[..gate.plan().k()], |bits| fill_words(&input, bits));
    let r1cs = gate.r1cs();
    for bit in 384..640 {
      row[bit] ^= true;
      assert!(!r1cs.satisfies(&row));
      row[bit] ^= true;
    }
    let rows = vec![MemoryRow(input.to_vec()); 3];
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}

pub(super) struct ArenaEmission {
  pub slots: ImmutableArenaSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn arena_setup(
  nu: usize,
  depth: MemoryDepth,
) -> (ArenaEmission, CircuitShape) {
  let mut shape = ShapeBuilder::new(nu);
  let mut b = LayoutEmitter::new(&mut shape);
  let slots = ImmutableArenaSlots::declare(&mut b, nu, depth).unwrap();
  let mut state = slots.initialize();
  for word in state.words() {
    b.publish(word);
  }
  for _ in 0..3 {
    let proof = opening(&mut b, depth);
    let value = std::array::from_fn(|_| b.input());
    let (next, address) = slots.allocate(&mut b, state, value, &proof);
    state = next;
    for word in [address, value[0], value[1]] {
      b.publish(word);
    }
  }
  let address = b.input();
  b.publish(address);
  let proof = opening(&mut b, depth);
  let value = slots.read(&mut b, state, address, &proof);
  for word in value.into_iter().chain(state.words()) {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  (ArenaEmission { slots, inputs, public }, shape.finish().unwrap())
}
pub(super) fn arena_fixture(depth: MemoryDepth) -> (Vec<F128>, Vec<F128>) {
  let mut memory = SparseMemory::new(depth);
  let mut expected = memory.root().to_vec();
  expected.push(F128::ZERO);
  let mut private = Vec::new();
  for index in 0..3 {
    let value = [F128::new(index, index + 1), F128::new(index + 2, index + 3)];
    let old = memory.replace(index, value).unwrap();
    private.extend_from_slice(&old.words()[1..]);
    private.extend(value);
    expected.push(F128::new(index, 0));
    expected.extend(value);
  }
  let read = memory.open(0).unwrap();
  private.extend(read.words());
  expected.push(F128::ZERO);
  expected.extend(read.value);
  expected.extend(memory.root());
  expected.push(F128::new(3, 0));
  (private, expected)
}

#[test]
fn immutable_allocations_bind_the_counter_cells_and_read_prefix() {
  let depth = MemoryDepth::new(16).unwrap();
  let (emission, shape) = arena_setup(8, depth);
  let (private, expected) = arena_fixture(depth);
  let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
  assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
  let read = 3 * (4 + 2 * depth.bits());
  for position in [0, 1, 2, 4 + 2 * depth.bits(), read, read + 1, read + 3] {
    let mut changed = private.clone();
    changed[position] += F128::ONE;
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || shape.run(&emission.inputs.assign(&changed).unwrap(), &[])
      ))
      .is_err()
    );
  }
}
pub(super) fn setup(nu: usize, depth: MemoryDepth) -> (Emission, CircuitShape) {
  let mut b = ShapeBuilder::new(nu);
  let emission = emit(&mut b, nu, depth);
  (emission, b.finish().unwrap())
}
pub(super) fn fixture(depth: MemoryDepth, salt: u64) -> (Vec<F128>, Vec<F128>) {
  let mut memory = SparseMemory::new(depth);
  let mut private = memory.root().to_vec();
  let mut expected = private.clone();
  let maximum =
    if depth.bits() == 64 { u64::MAX } else { (1 << depth.bits()) - 1 };
  for (address, value) in [
    (0, [F128::new(1, salt), F128::new(2, 3)]),
    (maximum, [F128::new(4, 5), F128::new(6, salt)]),
    (0, [F128::new(7, 8), F128::new(salt, 9)]),
  ] {
    let opening = memory.replace(address, value).unwrap();
    private.extend(opening.words());
    private.extend(value);
    expected.push(F128::new(address, 0));
    expected.extend(value);
  }
  let read = memory.open(0).unwrap();
  private.extend(read.words());
  expected.push(F128::ZERO);
  expected.extend(read.value);
  expected.extend(memory.root());
  (private, expected)
}

#[test]
fn writes_repeated_reads_and_64_bit_addresses_match_independent_hashes() {
  for depth in [0, 1, 8, 32, 64] {
    let depth = MemoryDepth::new(depth).unwrap();
    let (emission, shape) = setup(9, depth);
    let (private, expected) = fixture(depth, 0x0123456789abcdef);
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
    let mut memory = SparseMemory::new(depth);
    let empty = memory.root();
    memory.replace(0, [F128::ONE; 2]).unwrap();
    assert_ne!(empty, memory.root());
    memory.replace(0, [F128::ZERO; 2]).unwrap();
    assert_eq!(empty, memory.root());
  }
}

#[test]
fn stale_values_wrong_addresses_and_path_substitution_break_wiring() {
  let depth = MemoryDepth::new(8).unwrap();
  let (emission, shape) = setup(8, depth);
  let (private, _) = fixture(depth, 33);
  // First write: address, old value and siblings. Last read uses new data.
  let last_read = 2 + 3 * (5 + 2 * depth.bits());
  for position in [2, 3, 5, last_read, last_read + 1, last_read + 3] {
    let mut bad = private.clone();
    bad[position] += F128::ONE;
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || shape.run(&emission.inputs.assign(&bad).unwrap(), &[])
      ))
      .is_err()
    );
  }
}

#[test]
fn count_tracks_depth_without_allocating_a_memory_bank() {
  for bits in [0, 16, 32, 64] {
    let depth = MemoryDepth::new(bits).unwrap();
    let mut count = CountingEmitter::new();
    let _ = emit(&mut count, 9, depth);
    let (_, shape) = setup(9, depth);
    count.ensure_matches(&shape).unwrap();
  }
}
