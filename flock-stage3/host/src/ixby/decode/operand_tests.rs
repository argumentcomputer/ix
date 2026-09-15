use super::*;
use crate::ixby::decode::test_support::{Value as V, meta};

fn input(
  gate: &OperandResolveGate,
  values: &[V],
  operands: &[Option<u32>],
) -> Vec<F128> {
  let mut input = vec![F128::ZERO; gate.input_count()];
  input[0] = meta(1, 2, values.len() as u32, 0);
  for (index, value) in values.iter().enumerate() {
    input[1 + 2 * index..3 + 2 * index].copy_from_slice(&value.words());
  }
  let base = gate.frame_words();
  input[base] = meta(values.len() as u32, 3, 1, 0);
  input[base + 1] = meta(1, 0, operands.len() as u32, 0);
  for (index, operand) in operands.iter().enumerate() {
    let start = base + 2 + 3 * index;
    match operand {
      Some(index) => input[start] = meta(1, *index, 0, 0),
      None => {
        input[start] = meta(2, 0, 0, 0);
        input[start + 1..start + 3].copy_from_slice(&V::Erased.words());
      },
    }
  }
  input
}

fn check(
  gate: &OperandResolveGate,
  r1cs: &BlockR1cs,
  input: &[F128],
  good: bool,
) {
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(input, bits));
  let residual = 128 * (gate.input_count() + 2 * gate.operands);
  assert_eq!(bits[residual], !good, "{input:?}");
  assert!(r1cs.satisfies(&bits));
  if !good {
    bits[residual] = false;
    assert!(!r1cs.satisfies(&bits));
  }
}

#[test]
fn all_live_local_positions_and_literal_types_resolve_in_original_order() {
  let gate = OperandResolveGate::new(3, 16, 4).unwrap();
  let r1cs = gate.r1cs();
  let mut values = vec![
    V::Bool(0),
    V::Bool(1),
    V::Word(u32::MAX),
    V::Field(0xffff_ffff_0000_0000),
    V::Ext(1, 0xffff_ffff_0000_0000),
    V::Erased,
  ];
  values.extend((6..16).map(V::Word));
  for count in 0..=16 {
    let used = count.min(4);
    let operands: Vec<_> =
      (0..used).map(|index| Some((count - 1 - index) as u32)).collect();
    let input = input(&gate, &values[..count], &operands);
    check(&gate, &r1cs, &input, true);
    let mut expected: Vec<_> =
      (0..used).flat_map(|index| values[count - 1 - index].words()).collect();
    expected.resize(gate.output_count(), F128::ZERO);
    assert_eq!(evaluate(gate.plan(), &input, gate.output_count()), expected);
  }
  for value in &values[..6] {
    let mut input = input(&gate, &[], &[None]);
    let base = gate.frame_words() + 3;
    input[base..base + 2].copy_from_slice(&value.words());
    check(&gate, &r1cs, &input, true);
    let mut expected = value.words().to_vec();
    expected.resize(gate.output_count(), F128::ZERO);
    assert_eq!(evaluate(gate.plan(), &input, gate.output_count()), expected);
  }
}

#[test]
fn full_width_access_counts_metadata_and_padding_are_constrained() {
  let gate = OperandResolveGate::new(3, 3, 2).unwrap();
  let r1cs = gate.r1cs();
  let good = input(&gate, &[V::Word(11), V::Bool(1)], &[Some(0)]);
  check(&gate, &r1cs, &good, true);
  let base = gate.frame_words();
  for index in [2, 3, 4, 1 << 16, 1 << 31, u32::MAX] {
    let mut bad = good.clone();
    bad[base + 2] = meta(1, index, 0, 0);
    check(&gate, &r1cs, &bad, false);
  }
  for kind in [0, 3, 4, 1 << 31, u32::MAX] {
    let mut bad = good.clone();
    bad[base + 2] = meta(kind, 0, 0, 0);
    check(&gate, &r1cs, &bad, false);
  }
  for count in [4, 1 << 31, u32::MAX] {
    let mut bad = good.clone();
    bad[0] = meta(1, 2, count, 0);
    check(&gate, &r1cs, &bad, false);
  }
  for count in [0, 3, 1 << 31, u32::MAX] {
    let mut bad = good.clone();
    bad[base + 1] = meta(1, 0, count, 0);
    check(&gate, &r1cs, &bad, false);
  }
  for (word, start) in [(0, 96), (base + 2, 64)] {
    for bit in start..128 {
      let mut bad = good.clone();
      flip(&mut bad[word], bit);
      check(&gate, &r1cs, &bad, false);
    }
  }
  // Unread local padding, local-operand constant cells, unused operands.
  for word in [5, 6, base + 3, base + 4, base + 5, base + 6, base + 7] {
    for bit in [0, 31, 32, 63, 64, 95, 96, 127] {
      let mut bad = good.clone();
      flip(&mut bad[word], bit);
      check(&gate, &r1cs, &bad, false);
    }
  }
  let mut bad = input(&gate, &[], &[None]);
  bad[base + 2] = meta(2, 1 << 31, 0, 0);
  check(&gate, &r1cs, &bad, false);
}

fn flip(word: &mut F128, bit: usize) {
  if bit < 64 {
    word.lo ^= 1 << bit;
  } else {
    word.hi ^= 1 << (bit - 64);
  }
}

#[test]
fn canonical_scalar_cells_are_checked_even_when_unread_and_outputs_cannot_be_forged()
 {
  let gate = OperandResolveGate::new(3, 2, 1).unwrap();
  let r1cs = gate.r1cs();
  for value in [
    V::Bool(0),
    V::Bool(1),
    V::Word(17),
    V::Field(19),
    V::Ext(23, 29),
    V::Erased,
  ] {
    // Check both constant cells and live locals that the instruction never reads.
    for literal in [false, true] {
      let mut good = if literal {
        input(&gate, &[], &[None])
      } else {
        input(&gate, std::slice::from_ref(&value), &[None])
      };
      let base = if literal { gate.frame_words() + 3 } else { 1 };
      good[base..base + 2].copy_from_slice(&value.words());
      check(&gate, &r1cs, &good, true);
      for bit in 3..128 {
        let mut bad = good.clone();
        flip(&mut bad[base], bit);
        check(&gate, &r1cs, &bad, false);
      }
      for tag in [0, 6, 7, u64::MAX] {
        let mut bad = good.clone();
        bad[base] = F128::new(tag, 0);
        check(&gate, &r1cs, &bad, false);
      }
      let start = match value {
        V::Bool(_) => 1,
        V::Word(_) => 32,
        V::Field(_) => 64,
        V::Ext(..) => 128,
        V::Erased => 0,
        V::Bytes(_) | V::Nat(_) | V::Ctor(..) | V::Pap(..) => {
          unreachable!("legacy scalar corpus")
        },
      };
      for bit in start..128 {
        let mut bad = good.clone();
        flip(&mut bad[base + 1], bit);
        check(&gate, &r1cs, &bad, false);
      }
      for lane in 0..if matches!(value, V::Ext(..)) {
        2
      } else if matches!(value, V::Field(_)) {
        1
      } else {
        0
      } {
        for invalid in [0xffff_ffff_0000_0001, u64::MAX] {
          let mut bad = good.clone();
          if lane == 0 {
            bad[base + 1].lo = invalid;
          } else {
            bad[base + 1].hi = invalid;
          }
          check(&gate, &r1cs, &bad, false);
        }
      }
    }
  }
  let good = input(&gate, &[V::Word(42)], &[Some(0)]);
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&good, bits));
  assert!(r1cs.satisfies(&bits));
  for bit in 0..128 * gate.output_count() {
    let column = 128 * gate.input_count() + bit;
    bits[column] ^= true;
    assert!(!r1cs.satisfies(&bits));
    bits[column] ^= true;
  }
  bits[gate.plan().k() - 1] = true;
  assert!(!r1cs.satisfies(&bits));
}

#[test]
fn operand_count_emit_is_lazy_and_padding_writes_match_the_allocating_driver() {
  use crate::sizing::CountingEmitter;
  use flock_prover::circuit::builder::ShapeBuilder;
  let gate = OperandResolveGate::new(3, 2, 2).unwrap();
  fn emit(b: &mut impl CircuitEmitter, gate: OperandResolveGate) {
    let frame: Vec<_> = (0..gate.frame_words()).map(|_| b.input()).collect();
    let block: Vec<_> = (0..gate.block_words()).map(|_| b.input()).collect();
    let slot = OperandResolveSlot::declare(b, gate);
    for word in slot.resolve(b, &frame, &block) {
      b.publish(word);
    }
  }
  let mut count = CountingEmitter::new();
  emit(&mut count, gate.clone());
  assert!(gate.plan.get().is_none());
  let mut b = ShapeBuilder::new(3);
  emit(&mut b, gate.clone());
  let shape = b.finish().unwrap();
  count.ensure_matches(&shape).unwrap();
  let (registry, counts) = count.registry(3);
  assert_eq!(counts, shape.counts);
  assert_eq!(registry.types()[0].a_0.rows, shape.registry.types()[0].a_0.rows);
  assert_eq!(registry.types()[0].b_0.rows, shape.registry.types()[0].b_0.rows);
  assert_eq!(
    registry.types()[0].io_schema,
    shape.registry.types()[0].io_schema
  );
  let row = OperandResolveRow(input(&gate, &[V::Word(42)], &[Some(0)]));
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  for (nu, locals, operands) in
    [(2, 2, 2), (3, 0, 2), (3, 17, 2), (3, 1, 0), (3, 1, 5)]
  {
    assert!(OperandResolveGate::new(nu, locals, operands).is_err());
  }
}
