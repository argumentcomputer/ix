use super::{
  super::{grammar, registry::RegistryOp, scalar_payload_tests},
  *,
};
use crate::{
  ixby::bits::fill_words,
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{circuit::builder::ShapeBuilder, field::F128};
pub(super) fn capacity() -> BodyCapacity {
  BodyCapacity::new(
    RegistryCapacity::new(2, 2, 2).unwrap(),
    NaturalCapacity::new(127).unwrap(),
    3,
  )
  .unwrap()
}
pub(super) fn checked(g: &BodyGate, input: &[F128]) -> Vec<F128> {
  let expected = evaluate::evaluate(g.capacity, g.op, input);
  assert_eq!(
    crate::ixby::bits::evaluate_words(g.plan(), input, g.output_count()),
    expected,
    "{:?}: {input:?}",
    g.op
  );
  expected
}
pub(super) fn fixture(c: BodyCapacity) -> fixtures::Fixture {
  let mut spec = fixtures::base();
  spec.constructors = vec![[1, 2, 3, 4, 0], [1, 2, 3, 5, 1]];
  spec.functions[0].blocks =
    vec![(0, vec![5, 2, 2, 0, 0, 1, 1]), (1, vec![1, 1, 0, 255, 1])];
  spec.functions.push(fixtures::Function {
    arity: 2,
    entry: 1,
    blocks: vec![(2, vec![1, 2]), (2, vec![1, 0, 1])],
  });
  spec.entry = 1;
  fixtures::encode(c, "sample", &spec, false)
}
pub(super) fn finish_input(
  c: BodyCapacity,
  f: &fixtures::Fixture,
) -> Vec<F128> {
  let registry = 28 + c.state_words();
  let bank = registry + c.registry.words();
  let mut input = vec![F128::ZERO; bank + c.bank_words()];
  input[0] =
    F128::new(f.source.bytes.len() as u64, f.source.bytes.len() as u64);
  input[1] = fixtures::word(grammar::Phase::Done as u128);
  for h in &f.source.headers {
    let (at, fields) = match h.kind {
      RegistryOp::Constructor => {
        input[grammar::CTORS].lo += 1;
        (registry + h.index * 7, 5)
      },
      RegistryOp::Function => {
        input[grammar::FUNCTIONS].lo += 1;
        (registry + c.registry.constructors() * 7 + h.index * 5, 3)
      },
      RegistryOp::Block => (registry + c.registry_block(h.owner, h.index), 2),
      _ => unreachable!(),
    };
    input[at] = F128::ONE;
    input[at + 1..at + 1 + fields].copy_from_slice(&h.fields[..fields]);
    input[at + 1 + fields] = h.span;
  }
  input[bank..]
    .copy_from_slice(&f.bank[c.registry.functions() * FUNCTION_WORDS..]);
  input
}
fn sample(c: BodyCapacity, op: BodyOp) -> Vec<F128> {
  let f = fixture(c);
  let r = c.block_words();
  let offset = c.registry.functions() * FUNCTION_WORDS;
  match op {
    BodyOp::Step => {
      let mut input = vec![F128::ZERO; c.state() + c.state_words()];
      let s = c.state();
      let at = s + CONTROL_WORDS;
      let body = &f.bank[offset + r..offset + 2 * r];
      let operand = &body[HEADER_WORDS..HEADER_WORDS + c.operand_words()];
      let start = operand[O_SPAN].lo + 2;
      let end = operand[O_SPAN].hi;
      let len = f.source.bytes.len() as u64;
      input[0] = F128::new(start, len);
      input[1] = fixtures::word(grammar::Phase::Natural as u128);
      input[grammar::FUNCTION_INDEX] = F128::ONE;
      input[grammar::BLOCKS] = F128::new(2, 0);
      input[grammar::LOCALS] = F128::ONE;
      input[COMMITTED] = F128::ONE;
      input[TAG] = F128::new(14, 0);
      input[FIELDS] = F128::new(end - start, 0);
      input[NEXT] = F128::new(end, len);
      input[NEXT_CONTROL] = fixtures::word(grammar::Phase::Function as u128);
      input[NAT_RANGE] = F128::new(start, end - start);
      input[NAT] = F128::new(255, 0);
      input[s + 1] = F128::ONE;
      input[s + 2] = F128::ONE;
      input[s + 3] = F128::new(operand[O_SPAN].lo, 0);
      input[at..].copy_from_slice(body);
      input[at + OPERANDS] = F128::ZERO;
      input[at + SPAN].hi = start;
      input[at + HEADER_WORDS..].fill(F128::ZERO);
      input
    },
    BodyOp::Capture => {
      let mut input = vec![F128::ZERO; 2 + r + c.bank_words()];
      input[1] = F128::ONE;
      input[2..2 + r].copy_from_slice(&f.bank[offset + r..offset + 2 * r]);
      input[2 + r..2 + 2 * r].copy_from_slice(&f.bank[offset..offset + r]);
      input
    },
    BodyOp::Finish => finish_input(c, &f),
    _ => {
      let q = f.queries(c);
      let mut input = match op {
        BodyOp::ReadFunction => vec![q[0], q[1], F128::ZERO, F128::ZERO],
        BodyOp::ReadBlock => vec![q[2], q[3], q[4], F128::ZERO],
        BodyOp::ReadOperand => q[5..9].to_vec(),
        _ => q[9..13].to_vec(),
      };
      input.extend(f.bank);
      input
    },
  }
}
#[test]
fn body_tables_match_integer_model_for_full_width_state_records_and_controls() {
  let c = capacity();
  for op in BodyOp::ALL {
    let g = BodyGate::new(3, c, op).unwrap();
    let input = sample(c, op);
    assert_eq!(checked(&g, &input).last(), Some(&F128::ZERO));
    for at in 0..input.len() {
      for bit in [0, 63, 100, 127] {
        let mut wrong = input.clone();
        let word = fixtures::word(1u128 << bit);
        wrong[at].lo ^= word.lo;
        wrong[at].hi ^= word.hi;
        checked(&g, &wrong);
      }
    }
    if op == BodyOp::Step {
      for at in [1, COMMITTED, TAG, NEXT_CONTROL, c.state() + 2, c.state() + 4]
      {
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
fn completed_bodies_bind_full_spans_ownership_frames_and_exact_operand_order() {
  let c = capacity();
  let f = fixture(c);
  let g = BodyGate::new(3, c, BodyOp::Finish).unwrap();
  let input = finish_input(c, &f);
  let mut expected = f.bank.clone();
  expected.push(F128::ZERO);
  assert_eq!(checked(&g, &input), expected);
  let bank = 28 + c.state_words() + c.registry.words();
  let r = c.block_words();
  let nat = bank + r + HEADER_WORDS;
  for (at, value) in [
    (28, F128::ONE),
    (bank + LOCALS, F128::ONE),
    (bank + INSTRUCTION, fixtures::word(7)),
    (bank + OPERANDS, fixtures::word(2)),
    (bank + ALTERNATIVES, F128::ONE),
    (bank + SPAN, F128::new(0, 1)),
    (bank + HEADER_END, fixtures::word(1u128 << 100)),
    (bank + c.alternatives() + ALT_WORDS + 1, F128::ZERO),
    (nat + O_PAYLOAD, F128::new(0, 2)),
    (nat + O_MAGNITUDE, fixtures::word(1u128 << 127)),
    (bank + 3 * r + HEADER_WORDS + O_LOCAL, fixtures::word(2)),
    (bank + 3 * r + TARGET0, F128::ONE),
  ] {
    let mut wrong = input.clone();
    wrong[at] = value;
    assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE), "word {at}");
  }
  let step = BodyGate::new(3, c, BodyOp::Step).unwrap();
  let row = sample(c, BodyOp::Step);
  let out = checked(&step, &row);
  assert!(out[..c.state_words()].iter().all(|w| *w == F128::ZERO));
  assert_eq!(
    &out[c.state_words() + 2..out.len() - 1],
    &f.bank[c.registry.functions() * FUNCTION_WORDS + r
      ..c.registry.functions() * FUNCTION_WORDS + 2 * r]
  );
  for at in [
    grammar::FUNCTION_INDEX,
    grammar::BLOCKS,
    grammar::BLOCKS_LEFT,
    c.state(),
    c.state() + 1,
    c.state() + 3,
  ] {
    let mut wrong = row.clone();
    wrong[at] = fixtures::word(1u128 << 100);
    assert_eq!(checked(&step, &wrong).last(), Some(&F128::ONE));
  }
}
#[test]
fn body_reads_reject_missing_records_full_width_addresses_and_disabled_advice()
{
  let c = capacity();
  for op in [
    BodyOp::ReadFunction,
    BodyOp::ReadBlock,
    BodyOp::ReadOperand,
    BodyOp::ReadAlternative,
  ] {
    let g = BodyGate::new(3, c, op).unwrap();
    let input = sample(c, op);
    for at in 1..4 {
      for value in [8, 1u128 << 64, 1u128 << 100, u128::MAX] {
        let mut wrong = input.clone();
        wrong[at] = fixtures::word(value);
        assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
      }
    }
    let mut disabled = input;
    disabled[..4].fill(F128::ZERO);
    assert!(checked(&g, &disabled).iter().all(|w| *w == F128::ZERO));
    for at in 1..4 {
      let mut wrong = disabled.clone();
      wrong[at] = fixtures::word(1u128 << 127);
      assert_eq!(checked(&g, &wrong).last(), Some(&F128::ONE));
    }
  }
}
#[test]
fn body_outputs_padding_and_lazy_count_shapes_are_constrained() {
  let c = capacity();
  for op in BodyOp::ALL {
    let g = BodyGate::new(3, c, op).unwrap();
    let mut count = CountingEmitter::new();
    let slot = count.slot(g.clone());
    let input: Vec<_> = (0..g.input_count()).map(|_| count.input()).collect();
    count.gate(slot, &input);
    assert!(g.plan.get().is_none());
    let mut shape = ShapeBuilder::new(3);
    let slot = shape.slot(g.clone());
    let input: Vec<_> = (0..g.input_count()).map(|_| shape.input()).collect();
    shape.gate(slot, &input);
    count.ensure_matches(&shape.finish().unwrap()).unwrap();
    let input = sample(c, op);
    let output = checked(&g, &input);
    let r1cs = g.r1cs();
    let mut bits =
      scalar_payload_tests::checked(g.plan(), &r1cs, &input, &output);
    super::super::tests::output_bits_are_bound(
      &r1cs,
      &mut bits,
      input.len() * 128,
      output.len() * 128,
    );
    bits[g.plan().k() - 1] = true;
    assert!(!super::super::tests::satisfies(&r1cs, &bits));
    for n in [0, 1, 5] {
      let rows = vec![BodyRow(input.clone()); n];
      crate::ixby::test_support::padding(
        g.plan(),
        &rows,
        |r, bits| fill_words(&r.0, bits),
        |dst| g.generate_witness_into(&rows, dst),
      );
    }
  }
  for nu in [0, 2, 21, usize::MAX] {
    assert!(BodyGate::new(nu, c, BodyOp::Step).is_err());
  }
  for operands in [0, 5, usize::MAX] {
    assert!(BodyCapacity::new(c.registry, c.natural, operands).is_err());
  }
  assert!(
    BodyCapacity::new(RegistryCapacity::new(4, 4, 8).unwrap(), c.natural, 1)
      .is_err()
  );
  let widest = BodyCapacity::new(
    RegistryCapacity::new(4, 2, 4).unwrap(),
    NaturalCapacity::new(4096).unwrap(),
    4,
  )
  .unwrap();
  BodyGate::new(3, widest, BodyOp::Finish).unwrap().r1cs();
  for (constructors, functions, blocks) in [(0, 1, 1), (0, 1, 8), (4, 4, 2)] {
    let c = BodyCapacity::new(
      RegistryCapacity::new(constructors, functions, blocks).unwrap(),
      NaturalCapacity::new(0).unwrap(),
      1,
    )
    .unwrap();
    for op in BodyOp::ALL {
      BodyGate::new(3, c, op).unwrap().r1cs();
    }
  }
}
