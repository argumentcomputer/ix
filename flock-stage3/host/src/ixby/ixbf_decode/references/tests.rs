use super::{
  super::{grammar, scalar_payload_tests},
  *,
};
use crate::{
  ixby::bits::fill_words,
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{circuit::builder::ShapeBuilder, field::F128};

fn cap() -> RegistryCapacity {
  RegistryCapacity::new(2, 2, 2).unwrap()
}
fn request(
  phase: grammar::Phase,
  instruction: u128,
  fields: &[u128],
) -> Vec<F128> {
  let mut input = vec![F128::ZERO; REQUEST_INPUTS];
  input[1] = fixtures::word(phase as u128);
  input[grammar::FUNCTION_INDEX] = F128::ONE;
  input[grammar::LOCALS] = F128::new(2, 0);
  input[grammar::LIMITS + 3] = fixtures::word(u128::MAX);
  input[COMMITTED] = F128::ONE;
  input[TAG] = F128::new(
    match phase {
      grammar::Phase::Block => 5,
      grammar::Phase::Operation => 12,
      grammar::Phase::FunctionIndex | grammar::Phase::Target => 2,
      grammar::Phase::OperandCount => 1,
      grammar::Phase::Alternative => 6,
      _ => 13,
    },
    0,
  );
  input[STATE] = fixtures::word(instruction);
  for (at, value) in fields.iter().enumerate() {
    input[FIELDS + at] = fixtures::word(*value);
  }
  input
}
fn samples() -> Vec<Vec<F128>> {
  use grammar::Phase::*;
  let mut samples = vec![
    request(Block, 0, &[2, 0]),
    request(FunctionIndex, 2, &[1]),
    request(OperandCount, 2, &[2]),
    request(OperandCount, 3, &[2]),
  ];
  for op in 0..8 {
    samples.push(request(Operation, 0, &[op, 0, 1, 2]));
  }
  for instruction in [0, 6, 7] {
    for targets in 1..=2 {
      if instruction == 0 && targets == 2 {
        continue;
      }
      let mut r = request(Target, instruction, &[1]);
      r[1].lo |= targets << 32;
      samples.push(r);
    }
  }
  samples.push(request(Alternative, 5, &[1, 1]));
  let mut done = request(Done, 5, &[]);
  done[COMMITTED] = F128::ZERO;
  done[TAG] = F128::new(17, 0);
  samples.push(done);
  samples
}
fn checked(gate: &ReferenceGate, input: &[F128]) -> Vec<F128> {
  let expected = evaluate::evaluate(gate.capacity, gate.op, input);
  assert_eq!(
    crate::ixby::bits::evaluate_words(gate.plan(), input, gate.output_count()),
    expected,
    "{:?}: {input:?}",
    gate.op
  );
  expected
}

#[test]
fn request_matches_integer_model_for_every_control_byte_and_full_width_state() {
  let gate = ReferenceGate::new(3, cap(), ReferenceOp::Request).unwrap();
  for r in samples() {
    assert_eq!(checked(&gate, &r).last(), Some(&F128::ZERO));
    for at in [1, COMMITTED, TAG, FIELDS, STATE, STATE + 2] {
      for byte in 0..=255 {
        let mut wrong = r.clone();
        wrong[at].lo = (wrong[at].lo & !255) | byte;
        checked(&gate, &wrong);
      }
      for bit in [8, 32, 40, 63, 64, 100, 127] {
        let mut wrong = r.clone();
        let v = fixtures::word(1u128 << bit);
        wrong[at].lo ^= v.lo;
        wrong[at].hi ^= v.hi;
        checked(&gate, &wrong);
      }
    }
  }
}

#[test]
fn requests_bind_owner_tail_callee_and_all_duplicate_alternatives() {
  use grammar::Phase::*;
  let gate = ReferenceGate::new(3, cap(), ReferenceOp::Request).unwrap();
  let mut r = request(OperandCount, 2, &[3]);
  r[STATE + 1] = fixtures::word(1u128 << 100);
  assert_eq!(checked(&gate, &r)[STATE_WORDS + FUNCTION_INDEX], r[STATE + 1]);
  let mut r = request(Operation, 0, &[6, 0, 0, 0]);
  r[grammar::FUNCTION_INDEX] = F128::ZERO;
  assert_eq!(checked(&gate, &r).last(), Some(&F128::ONE));
  for index in 0..2 {
    for seen in 0..4 {
      let mut r = request(Alternative, 5, &[index, 0]);
      r[STATE + 2] = F128::new(seen, 0);
      assert_eq!(
        *checked(&gate, &r).last().unwrap(),
        F128::new(u64::from(seen & (1 << index) != 0), 0)
      );
    }
  }
  for index in [2, 1u128 << 64, 1u128 << 100, u128::MAX] {
    let r = request(Alternative, 5, &[index, 0]);
    assert_eq!(checked(&gate, &r).last(), Some(&F128::ONE));
  }
  let mut r = request(Block, 5, &[0, 5]);
  r[STATE + 1] = fixtures::word(u128::MAX);
  r[STATE + 2] = F128::new(3, 0);
  assert_eq!(
    &checked(&gate, &r)[..3],
    &[F128::new(5, 0), F128::ZERO, F128::ZERO]
  );
}

fn check_sample() -> Vec<F128> {
  let mut r = vec![F128::ZERO; CHECK_INPUTS];
  for at in [CTOR_ENABLE, BLOCK_ENABLE, ADD_CTOR] {
    r[at] = F128::ONE;
  }
  r[CTOR + 4] = fixtures::word(1u128 << 100);
  r[LOCALS] = F128::new(2, 0);
  r[BLOCK] = fixtures::word((1u128 << 100) + 2);
  r[LOCAL_LIMIT] = fixtures::word(u128::MAX);
  r
}

#[test]
fn checks_reject_arity_errors_full_width_overflow_and_disabled_advice() {
  let gate = ReferenceGate::new(3, cap(), ReferenceOp::Check).unwrap();
  let r = check_sample();
  assert_eq!(checked(&gate, &r), [F128::ZERO]);
  for at in 0..CHECK_INPUTS {
    for bit in [0, 1, 63, 64, 100, 127] {
      let mut wrong = r.clone();
      let v = fixtures::word(1u128 << bit);
      wrong[at].lo ^= v.lo;
      wrong[at].hi ^= v.hi;
      checked(&gate, &wrong);
    }
  }
  for partial in [false, true] {
    for args in [0, 1, 2, 1u128 << 100, u128::MAX] {
      for arity in [0, 1, 2, 1u128 << 100, u128::MAX] {
        let mut r = vec![F128::ZERO; CHECK_INPUTS];
        r[FUNCTION_ENABLE] = F128::ONE;
        r[PARTIAL] = F128::new(u64::from(partial), 0);
        r[ARGUMENTS] = fixtures::word(args);
        r[FUNCTION] = fixtures::word(arity);
        assert_eq!(
          checked(&gate, &r),
          [F128::new(
            u64::from(if partial { args >= arity } else { args != arity }),
            0
          )]
        );
      }
    }
  }
  for (locals, fields, target, limit, ok) in [
    (u128::MAX, 1, 0, u128::MAX, false),
    (u128::MAX - 1, 1, u128::MAX, u128::MAX, true),
    (0, 1, 1, 0, false),
  ] {
    let mut r = r.clone();
    for (at, v) in [
      (LOCALS, locals),
      (CTOR + 4, fields),
      (BLOCK, target),
      (LOCAL_LIMIT, limit),
    ] {
      r[at] = fixtures::word(v);
    }
    assert_eq!(checked(&gate, &r), [F128::new(u64::from(!ok), 0)]);
  }
  for at in 0..CHECK_INPUTS {
    let mut r = vec![F128::ZERO; CHECK_INPUTS];
    r[at] = fixtures::word(1u128 << 127);
    assert_eq!(checked(&gate, &r), [F128::ONE], "disabled word {at}");
  }
}

#[test]
fn reference_outputs_lazy_shapes_and_recycled_padding_are_constrained() {
  for op in ReferenceOp::ALL {
    let gate = ReferenceGate::new(3, cap(), op).unwrap();
    let mut count = CountingEmitter::new();
    let slot = count.slot(gate.clone());
    let input: Vec<_> =
      (0..gate.input_count()).map(|_| count.input()).collect();
    count.gate(slot, &input);
    assert!(gate.plan.get().is_none());
    let mut b = ShapeBuilder::new(3);
    let slot = b.slot(gate.clone());
    let input: Vec<_> = (0..gate.input_count()).map(|_| b.input()).collect();
    b.gate(slot, &input);
    count.ensure_matches(&b.finish().unwrap()).unwrap();
    let input = if op == ReferenceOp::Request {
      samples().pop().unwrap()
    } else {
      check_sample()
    };
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
      let rows = vec![ReferenceRow(input.clone()); n];
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |r, bits| fill_words(&r.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
  for cap in [
    RegistryCapacity::new(0, 1, 1).unwrap(),
    RegistryCapacity::new(4, 4, 8).unwrap(),
  ] {
    ReferenceGate::new(3, cap, ReferenceOp::Request).unwrap().r1cs();
  }
  for nu in [0, 2, 21, usize::MAX] {
    assert!(ReferenceGate::new(nu, cap(), ReferenceOp::Check).is_err());
  }
}
