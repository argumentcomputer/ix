use super::{
  super::{grammar, scalar_payload_tests},
  *,
};
use crate::{
  ixby::bits::fill_words,
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{circuit::builder::ShapeBuilder, field::F128};

fn config() -> ValueConfig {
  ValueConfig {
    kind: GrammarKind::Input,
    registry: RegistryCapacity::new(2, 2, 2).unwrap(),
    arena: ValueCapacity::new(4, 4, NaturalCapacity::new(127).unwrap())
      .unwrap(),
  }
}
pub(super) fn checked(g: &ValueGate, input: &[F128]) -> Vec<F128> {
  let expected = evaluate::evaluate(g.config, g.op, input);
  assert_eq!(
    crate::ixby::bits::evaluate_words(g.plan(), input, g.output_count()),
    expected,
    "{:?}: {input:?}",
    g.op
  );
  expected
}
fn forest(c: ValueConfig) -> fixtures::Fixture {
  use fixtures::{Scalar as S, Value::*};
  fixtures::encode(
    c.kind,
    c.arena,
    &fixtures::spec(1),
    &[Constructor(1, vec![Pap(0, vec![Scalar(S::Nat(vec![255, 1]))]), Erased])],
  )
}
fn finish_input(c: ValueConfig, f: &fixtures::Fixture) -> Vec<F128> {
  let mut input = vec![F128::ZERO; 33 + c.arena.bank_words()];
  input[0] = F128::new(f.bytes.len() as u64, f.bytes.len() as u64);
  input[1] = fixtures::word(grammar::Phase::Done as u128);
  input[grammar::SEEN] = f.summary[0];
  input[grammar::ENTRY_ARITY] = f.summary[1];
  input[31] = F128::new(if c.kind == GrammarKind::Input { 13 } else { 12 }, 0);
  input[32] = f.summary[0];
  for (i, r) in f.records.iter().enumerate() {
    let at = 33 + i * c.arena.record_words();
    input[at..at + c.arena.record_words()]
      .copy_from_slice(&r[..c.arena.record_words()]);
  }
  input
}
fn sample(c: ValueConfig, op: ValueOp) -> Vec<F128> {
  let a = c.arena;
  let r = a.record_words();
  let f = forest(c);
  match op {
    ValueOp::Link => {
      let mut input = vec![F128::ZERO; LINK_BANK + c.registry.words()];
      input[0] = F128::ONE;
      input[1] = F128::new(9, 0);
      input[2] = F128::ONE;
      let s = fixtures::spec(1);
      for (i, v) in s.constructors[1].iter().enumerate() {
        input[3 + i] = fixtures::word(*v);
      }
      for (i, ctor) in s.constructors.iter().enumerate() {
        let at = LINK_BANK + i * 7;
        input[at] = F128::ONE;
        for (j, v) in ctor.iter().enumerate() {
          input[at + 1 + j] = fixtures::word(*v);
        }
        input[at + 6] = F128::new(1, 2);
      }
      for (i, function) in s.functions.iter().enumerate() {
        let at = LINK_BANK + c.registry.constructors() * 7 + i * 5;
        input[at] = F128::ONE;
        input[at + 1] = fixtures::word(function.arity);
        input[at + 3] = F128::ONE;
        input[at + 4] = F128::new(2, 3);
      }
      input
    },
    ValueOp::Node => {
      let acc = NAT + a.natural.magnitude_words();
      let mut input = vec![F128::ZERO; acc + ACC_WORDS];
      input[0] = F128::new(20, 100);
      input[1] = fixtures::word(grammar::Phase::Natural as u128);
      input[grammar::SEEN] = F128::ONE;
      input[COMMIT] = F128::ONE;
      input[TAG] = F128::new(14, 0);
      input[FIELDS] = F128::new(2, 0);
      input[NEXT] = F128::new(22, 100);
      input[NAT_RANGE] = F128::new(20, 2);
      input[NAT] = F128::new(255, 0);
      input[acc] = F128::ONE;
      input[acc + 1] = F128::new(18, 0);
      input[acc + 3] = F128::new(13, 0);
      input
    },
    ValueOp::Capture => {
      let mut input = vec![F128::ZERO; 2 + r + a.bank_words()];
      input[0] = F128::new(2, 0);
      input[1] = input[0];
      input[2..2 + r].copy_from_slice(&f.records[2][..r]);
      for i in 0..2 {
        input[2 + r + i * r..2 + r + (i + 1) * r]
          .copy_from_slice(&f.records[i][..r]);
      }
      input
    },
    ValueOp::Finish => finish_input(c, &f),
    _ => {
      let mut input = vec![F128::ONE, F128::ZERO, F128::ZERO];
      for rec in f.records {
        input.extend(rec);
      }
      input
    },
  }
}

#[test]
fn value_tables_match_integer_model_for_full_width_controls_and_carried_words()
{
  let c = config();
  for op in ValueOp::ALL {
    let g = ValueGate::new(3, c, op).unwrap();
    let input = sample(c, op);
    assert_eq!(checked(&g, &input).last(), Some(&F128::ZERO));
    for at in 0..input.len() {
      for bit in [0, 63, 100, 127] {
        let mut wrong = input.clone();
        let v = fixtures::word(1u128 << bit);
        wrong[at].lo ^= v.lo;
        wrong[at].hi ^= v.hi;
        checked(&g, &wrong);
      }
    }
    if matches!(op, ValueOp::Link | ValueOp::Node) {
      let controls = if op == ValueOp::Link {
        vec![0, 1, 2]
      } else {
        vec![
          1,
          COMMIT,
          TAG,
          FIELDS,
          NAT + c.arena.natural.magnitude_words(),
          NAT + c.arena.natural.magnitude_words() + 2,
        ]
      };
      for at in controls {
        for byte in 0..=255 {
          let mut wrong = input.clone();
          wrong[at].lo = (wrong[at].lo & !255) | byte;
          checked(&g, &wrong);
        }
      }
    }
  }
}

#[test]
fn constructor_identity_and_partial_application_reads_use_all_reference_bits() {
  let c = config();
  let g = ValueGate::new(3, c, ValueOp::Link).unwrap();
  let input = sample(c, ValueOp::Link);
  for at in 3..7 {
    for bit in 0..128 {
      let mut wrong = input.clone();
      let v = fixtures::word(1u128 << bit);
      wrong[at].lo ^= v.lo;
      wrong[at].hi ^= v.hi;
      assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
    }
  }
  for count in [0, 1, 3, 1u128 << 100] {
    let mut wrong = input.clone();
    wrong[7] = fixtures::word(count);
    assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
  }
  let mut input = input;
  input[2] = F128::new(2, 0);
  input[3..7].fill(F128::ZERO);
  for index in [0, 1, 2, 1u128 << 64, 1u128 << 100, u128::MAX] {
    for children in [0, 1, 2, 3, 1u128 << 100, u128::MAX] {
      input[3] = fixtures::word(index);
      input[7] = fixtures::word(children);
      let valid = if index == 0 {
        children < 3
      } else if index == 1 {
        children < 1
      } else {
        false
      };
      assert_eq!(
        checked(&g, &input).last(),
        Some(&fixtures::word(u128::from(!valid)))
      );
    }
  }
}

#[test]
fn finished_forests_bind_topology_byte_partition_depth_roots_and_scalar_ranges()
{
  let c = config();
  let g = ValueGate::new(3, c, ValueOp::Finish).unwrap();
  let f = forest(c);
  f.check_native(c.arena);
  let input = finish_input(c, &f);
  let mut expected = f.summary.to_vec();
  for r in &f.records {
    expected.extend(r);
  }
  expected.push(F128::ZERO);
  assert_eq!(checked(&g, &input), expected);
  let r = c.arena.record_words();
  for (at, value) in [
    (grammar::ENTRY_ARITY, fixtures::word(2)),
    (grammar::ENTRY_ARITY, fixtures::word(1u128 << 100)),
    (32, fixtures::word(3)),
    (31, fixtures::word(14)),
    (33 + CHILDREN, fixtures::word(3)),
    (33 + 2 * r + CHILDREN, F128::ONE),
    (33 + 2 * r + PAYLOAD, F128::new(1, 2)),
    (33 + 3 * r + SPAN, F128::new(0, f.bytes.len() as u64)),
    (33 + 2 * r + MAGNITUDE, fixtures::word(1u128 << 127)),
    (33 + 3 * r + KIND, F128::ZERO),
  ] {
    let mut wrong = input.clone();
    wrong[at] = value;
    assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE), "word {at}");
  }
  let mut shallow = c;
  shallow.arena = ValueCapacity::new(4, 2, c.arena.natural).unwrap();
  assert_eq!(
    checked(&ValueGate::new(3, shallow, ValueOp::Finish).unwrap(), &input)
      .last(),
    Some(&F128::ONE)
  );
  for natural in [0, 1, 7, 128, 129, 4096] {
    let a =
      ValueCapacity::new(1, 1, NaturalCapacity::new(natural).unwrap()).unwrap();
    let c = ValueConfig { arena: a, ..c };
    let f = fixtures::encode(
      c.kind,
      a,
      &fixtures::spec(1),
      &[fixtures::Value::Scalar(fixtures::Scalar::Nat(vec![0]))],
    );
    assert_eq!(
      checked(
        &ValueGate::new(3, c, ValueOp::Finish).unwrap(),
        &finish_input(c, &f)
      )
      .last(),
      Some(&F128::ZERO)
    );
  }
}

#[test]
fn typed_reads_reject_missing_children_roots_and_noncanonical_disabled_requests()
 {
  let c = config();
  for op in [ValueOp::ReadNode, ValueOp::ReadChild, ValueOp::ReadRoot] {
    let g = ValueGate::new(3, c, op).unwrap();
    let input = sample(c, op);
    for index in [4, 1u128 << 64, 1u128 << 100, u128::MAX] {
      let mut wrong = input.clone();
      wrong[1] = fixtures::word(index);
      assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
    }
    for owner in [4, 1u128 << 64, u128::MAX] {
      let mut wrong = input.clone();
      wrong[2] = fixtures::word(owner);
      assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
    }
    let mut disabled = input.clone();
    disabled[0] = F128::ZERO;
    assert!(checked(&g, &disabled).iter().all(|w| *w == F128::ZERO));
    for at in [1, 2] {
      let mut wrong = disabled.clone();
      wrong[at] = fixtures::word(1u128 << 127);
      assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
    }
    if op == ValueOp::ReadChild {
      let mut leaf = input.clone();
      leaf[2] = F128::new(3, 0);
      assert_eq!(checked(&g, &leaf).last(), Some(&F128::ONE));
    }
    if op == ValueOp::ReadRoot {
      let mut missing = input;
      missing[1] = F128::ONE;
      assert_eq!(checked(&g, &missing).last(), Some(&F128::ONE));
    }
  }
}

#[test]
fn value_outputs_lazy_shapes_and_recycled_padding_are_constrained() {
  let c = config();
  for op in ValueOp::ALL {
    let gate = ValueGate::new(3, c, op).unwrap();
    let mut count = CountingEmitter::new();
    let slot = count.slot(gate.clone());
    let inputs: Vec<_> =
      (0..gate.input_count()).map(|_| count.input()).collect();
    count.gate(slot, &inputs);
    assert!(gate.plan.get().is_none());
    let mut b = ShapeBuilder::new(3);
    let slot = b.slot(gate.clone());
    let inputs: Vec<_> = (0..gate.input_count()).map(|_| b.input()).collect();
    b.gate(slot, &inputs);
    count.ensure_matches(&b.finish().unwrap()).unwrap();
    let input = sample(c, op);
    let out = checked(&gate, &input);
    let r1cs = gate.r1cs();
    let mut bits =
      scalar_payload_tests::checked(gate.plan(), &r1cs, &input, &out);
    super::super::tests::output_bits_are_bound(
      &r1cs,
      &mut bits,
      input.len() * 128,
      out.len() * 128,
    );
    bits[gate.plan().k() - 1] = true;
    assert!(!super::super::tests::satisfies(&r1cs, &bits));
    for n in [0, 1, 5] {
      let rows = vec![ValueRow(input.clone()); n];
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |r, bits| fill_words(&r.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
  for nodes in [0, 9, usize::MAX] {
    assert!(ValueCapacity::new(nodes, 1, c.arena.natural).is_err());
  }
  for depth in [0, 5, usize::MAX] {
    assert!(ValueCapacity::new(4, depth, c.arena.natural).is_err());
  }
  for nu in [0, 2, 21, usize::MAX] {
    assert!(ValueGate::new(nu, c, ValueOp::Finish).is_err());
  }
  assert!(
    ValueGate::new(
      3,
      ValueConfig { kind: GrammarKind::Program, ..c },
      ValueOp::Finish
    )
    .is_err()
  );
  let wide = ValueConfig {
    arena: ValueCapacity::new(8, 8, NaturalCapacity::new(4096).unwrap())
      .unwrap(),
    ..c
  };
  ValueGate::new(3, wide, ValueOp::Finish).unwrap().r1cs();
}
