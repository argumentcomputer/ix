use super::*;
use crate::{
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    bits::{fill_words, read_words},
    io::{InputLayout, LayoutEmitter, PublicLayout},
  },
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{CircuitShape, GateType, ShapeBuilder},
  field::F128,
};

pub(super) fn checked(gate: &MultiGate, input: &[F128]) -> Vec<F128> {
  let mut output = Vec::new();
  gate.eval(input, &(), &mut output);
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| fill_words(input, bits));
  assert_eq!(read_words(&row, input.len(), output.len()), output);
  let r1cs = gate.r1cs();
  row.resize(r1cs.n(), false);
  assert!(r1cs.satisfies(&row));
  output
}

#[test]
fn claim_outputs_and_recycled_padding_are_fully_constrained() {
  let depth = MemoryDepth::new(64).unwrap();
  for kind in MultiKind::ALL {
    let gate = MultiGate::new(3, depth, kind).unwrap();
    let mut input = vec![F128::new(3, 4); gate.input_count()];
    match kind {
      MultiKind::Leaf => input[0] = F128::new(u64::MAX, 0),
      MultiKind::Frontier | MultiKind::Parent => {
        input[0] = F128::ONE;
        input[1] = F128::new(1, (1 << 63) - 1);
      },
      MultiKind::Equal => {},
    }
    assert_eq!(checked(&gate, &input).last(), Some(&F128::ZERO));
    let r1cs = gate.r1cs();
    let mut row = vec![false; r1cs.n()];
    gate
      .plan()
      .fill_row(&mut row[..gate.plan().k()], |bits| fill_words(&input, bits));
    for bit in
      gate.input_count() * 128..(gate.input_count() + gate.output_count()) * 128
    {
      row[bit] ^= true;
      assert!(!r1cs.satisfies(&row));
      row[bit] ^= true;
    }
    for count in [0, 1, 7] {
      let rows = vec![MultiRow(input.clone()); count];
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
    if matches!(kind, MultiKind::Parent | MultiKind::Frontier) {
      for enable in [F128::new(2, 0), F128::new(1, 1 << 63)] {
        input[0] = enable;
        assert_eq!(checked(&gate, &input).last(), Some(&F128::ONE));
      }
      input[0] = F128::ONE;
      input[1].lo |= 1 << 63;
      assert_eq!(checked(&gate, &input).last(), Some(&F128::ONE));
    }
  }
}

#[test]
fn claims_bind_every_address_level_enable_and_complete_digest() {
  for bits in [0, 1, 8, 40, 64] {
    let depth = MemoryDepth::new(bits).unwrap();
    for kind in MultiKind::ALL {
      let gate = MultiGate::new(3, depth, kind).unwrap();
      if kind == MultiKind::Equal {
        let good = (0..6).map(|i| F128::new(i, !i)).collect::<Vec<_>>();
        let input = [good.clone(), good].concat();
        assert_eq!(checked(&gate, &input), [F128::ZERO]);
        for i in 0..12 {
          let mut bad = input.clone();
          bad[i] += F128::new(0, 1 << 63);
          assert_eq!(checked(&gate, &bad), [F128::ONE]);
        }
      } else if kind == MultiKind::Leaf {
        for address in [0, 1, 1 << 31, 1 << 63, u64::MAX] {
          let input = [
            F128::new(address, 0),
            F128::new(3, 4),
            F128::new(5, 6),
            F128::new(7, 8),
            F128::new(9, 10),
          ];
          let out = checked(&gate, &input);
          assert_eq!(out.last() == Some(&F128::ZERO), depth.admits(address));
          assert_eq!(out[0], F128::ONE);
          assert_eq!(out[1], F128::new(0, address));
          assert_eq!(out[2..6], input[1..]);
        }
        let mut input = [F128::ZERO; 5];
        input[0].hi = 1;
        assert_eq!(checked(&gate, &input).last(), Some(&F128::ONE));
      } else {
        for level in [0usize, 1, 7, 39, 40, 63, 64, 65, 127] {
          for index in [0u64, 1, 1 << 31, 1 << 63, u64::MAX] {
            let mut input = vec![F128::new(3, 4); gate.input_count()];
            input[0] = F128::ONE;
            input[1] = F128::new(level as u64, index);
            let valid = level <= bits
              && (kind != MultiKind::Parent || level > 0)
              && (bits - level.min(bits) == 64
                || index < 1u64 << (bits - level.min(bits)));
            let out = checked(&gate, &input);
            assert_eq!(
              out.last() == Some(&F128::ZERO),
              valid,
              "kind={kind:?} depth={bits} level={level} index={index}"
            );
            if valid && kind == MultiKind::Parent {
              assert_eq!(out[1], input[1]);
              assert_eq!(out[7], F128::new(level as u64 - 1, index * 2));
              assert_eq!(out[13], F128::new(level as u64 - 1, index * 2 + 1));
              assert_eq!(out[8..12], [input[2], input[3], input[6], input[7]]);
              assert_eq!(out[14..18], [input[4], input[5], input[8], input[9]]);
            }
          }
        }
        let input = vec![F128::ZERO; gate.input_count()];
        assert_eq!(
          checked(&gate, &input),
          vec![F128::ZERO; gate.output_count()]
        );
        let end =
          if kind == MultiKind::Parent { 10 } else { gate.input_count() };
        for i in 1..end {
          let mut bad = input.clone();
          bad[i] = F128::ONE;
          assert_eq!(checked(&gate, &bad).last(), Some(&F128::ONE));
        }
      }
    }
  }
}

pub(super) struct Emission {
  pub slots: MultiMemorySlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(
  b: &mut impl CircuitEmitter,
  nu: usize,
  depth: MemoryDepth,
  capacity: MultiCapacity,
) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots = MultiMemorySlots::declare(&mut b, nu, depth).unwrap();
  let initial = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let final_root = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let leaves = (0..capacity.leaves)
    .map(|_| {
      let mut next = || {
        let w = b.input();
        b.publish(w);
        w
      };
      LeafWires {
        address: next(),
        old: std::array::from_fn(|_| next()),
        new: std::array::from_fn(|_| next()),
      }
    })
    .collect::<Vec<_>>();
  let frontier = (0..capacity.frontier())
    .map(|_| FrontierWires {
      enabled: b.input(),
      position: b.input(),
      hash: std::array::from_fn(|_| b.input()),
    })
    .collect::<Vec<_>>();
  let parents = (0..capacity.parents)
    .map(|_| ParentWires {
      enabled: b.input(),
      position: b.input(),
      old_children: std::array::from_fn(|_| std::array::from_fn(|_| b.input())),
      new_children: std::array::from_fn(|_| std::array::from_fn(|_| b.input())),
    })
    .collect::<Vec<_>>();
  let switches =
    (0..capacity.plan().switches()).map(|_| b.input()).collect::<Vec<_>>();
  slots.check(
    &mut b,
    [initial, final_root],
    &MultiProofWires { leaves, parents, frontier, switches },
  );
  let (inputs, public) = b.finish();
  Emission { slots, inputs, public }
}
pub(super) fn setup(
  nu: usize,
  depth: MemoryDepth,
  capacity: MultiCapacity,
) -> (Emission, CircuitShape) {
  let mut b = ShapeBuilder::new(nu);
  let e = emit(&mut b, nu, depth, capacity);
  (e, b.finish().unwrap())
}
pub(super) fn fixture(depth: MemoryDepth) -> super::super::MultiUpdate {
  let mut memory = SparseMemory::from_cells(
    depth,
    [
      (0, [F128::new(3, 4), F128::new(5, 6)]),
      (2, [F128::new(7, 8), F128::new(9, 10)]),
      (255, [F128::new(11, 12), F128::new(13, 14)]),
    ],
  )
  .unwrap();
  memory
    .replace_many([
      (0, [F128::ZERO; 2]),
      (1, [F128::new(17, 18), F128::new(19, 20)]),
      (2, [F128::new(23, 24), F128::new(25, 26)]),
    ])
    .unwrap()
}

#[test]
fn shared_tree_binds_roots_cells_frontier_and_child_requests() {
  let depth = MemoryDepth::new(8).unwrap();
  let update = fixture(depth);
  let capacity = MultiCapacity::new(3, 12).unwrap();
  assert_eq!(update.parents.len(), 9);
  assert_eq!(update.frontier.len(), 7);
  let advice = MultiAdvice::new(capacity, &update).unwrap();
  let (e, shape) = setup(8, depth, capacity);
  let witness = shape.run(&e.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(witness.public, e.public.instantiate(&advice.expected).unwrap());
  let parent = 4 + 5 * capacity.leaves + 4 * capacity.frontier();
  let switches = parent + 10 * capacity.parents;
  for at in [
    0,
    2,
    4,
    5,
    7,
    19,
    21,
    parent,
    parent + 1,
    parent + 2,
    parent + 6,
    switches,
  ] {
    let mut bad = advice.private.clone();
    bad[at] += F128::ONE;
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || shape.run(&e.inputs.assign(&bad).unwrap(), &[])
      ))
      .is_err(),
      "accepted private word {at}"
    );
  }
  let mut count = CountingEmitter::new();
  let _ = emit(&mut count, 8, depth, capacity);
  count.ensure_matches(&shape).unwrap();
}

#[test]
fn native_simultaneous_updates_match_all_paths_and_full_u64_memory() {
  for bits in [0, 8, 40, 64] {
    let depth = MemoryDepth::new(bits).unwrap();
    let mask = if bits == 64 { u64::MAX } else { (1u64 << bits) - 1 };
    let mut initial = std::collections::BTreeMap::new();
    for i in 0..64u64 {
      initial.insert(
        i.wrapping_mul(0x6ba1_074f_1248_b931) & mask,
        [F128::new(i, !i), F128::new(!i, i)],
      );
    }
    let mut batch = SparseMemory::from_cells(depth, initial.clone()).unwrap();
    let mut sequential =
      SparseMemory::from_cells(depth, initial.clone()).unwrap();
    let before = batch.root();
    let mut updates = std::collections::BTreeMap::new();
    for i in 0..32u64 {
      updates.insert((mask - i.min(mask)) & mask, [F128::new(i, i), F128::ONE]);
    }
    updates.insert(0, [F128::ZERO; 2]);
    let update = batch.replace_many(updates.clone()).unwrap();
    for (&address, &value) in &updates {
      sequential.replace(address, value).unwrap();
    }
    assert_eq!(update.initial_root, before);
    assert_eq!(update.final_root, sequential.root());
    for address in initial.keys().chain(updates.keys()) {
      assert_eq!(
        batch.open(*address).unwrap().words(),
        sequential.open(*address).unwrap().words()
      );
    }
    assert_eq!(
      update.frontier.len() + update.leaves.len(),
      update.parents.len() + 1
    );
    let capacity =
      MultiCapacity::new(update.leaves.len(), update.parents.len()).unwrap();
    let _ = MultiAdvice::new(capacity, &update).unwrap();
    let empty = batch.replace_many([]).unwrap();
    assert_eq!(empty.initial_root, empty.final_root);
    assert_eq!(empty.frontier.len(), 1);
    let _ =
      MultiAdvice::new(MultiCapacity::new(0, 0).unwrap(), &empty).unwrap();
    let root = batch.root();
    assert!(batch.replace_many([(0, [F128::ZERO; 2]); 2]).is_err());
    assert_eq!(batch.root(), root);
    if bits < 64 {
      assert!(batch.replace_many([(mask + 1, [F128::ZERO; 2])]).is_err());
      assert_eq!(batch.root(), root);
    }
  }
}

#[test]
fn shared_tree_handles_empty_updates_root_leaves_and_full_depth_paths() {
  for bits in [0, 64] {
    let depth = MemoryDepth::new(bits).unwrap();
    let mut memory = SparseMemory::new(depth);
    let mut updates = vec![(0, [F128::new(3, 4), F128::new(5, 6)])];
    if bits == 64 {
      updates.push((u64::MAX, [F128::ONE; 2]));
    }
    let update = memory.replace_many(updates).unwrap();
    for update in [update, memory.replace_many([]).unwrap()] {
      let capacity =
        MultiCapacity::new(update.leaves.len(), update.parents.len()).unwrap();
      let advice = MultiAdvice::new(capacity, &update).unwrap();
      let (e, shape) = setup(10, depth, capacity);
      let witness = shape.run(&e.inputs.assign(&advice.private).unwrap(), &[]);
      assert_eq!(
        witness.public,
        e.public.instantiate(&advice.expected).unwrap()
      );
      let mut bad = advice.private.clone();
      bad[2] += F128::ONE;
      assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(
          || shape.run(&e.inputs.assign(&bad).unwrap(), &[])
        ))
        .is_err()
      );
    }
  }
}
