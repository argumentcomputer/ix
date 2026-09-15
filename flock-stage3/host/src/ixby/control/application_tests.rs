use super::*;
use crate::{
  ixby::{
    bits::{evaluate_words, fill_words},
    control::ControlStepGate,
    decode::test_support::meta,
    object_value::test_support::check,
    value::{PAP_TAG, word32_words},
  },
  sizing::CountedGate,
};
use flock_prover::{circuit::builder::GateType, field::F128};

const C: ControlCapacities =
  ControlCapacities { locals: 4, continuations: 1, arguments: 2 };
fn over_application() -> Vec<F128> {
  let mut row =
    vec![F128::ZERO; C.state_words() + C.application_action_words()];
  row[0] = meta(3, 9, 0, 0);
  row[1] = meta(0, 0, 2, 0);
  row[2..6].copy_from_slice(&[word32_words(11), word32_words(22)].concat());
  row[C.value_word()] = F128::new(PAP_TAG, 0);
  let action = C.state_words();
  row[action] = meta(9, 0, 0, 7);
  row[action + 1] = meta(3, 1, 1, 0);
  row[action + 4..action + 6].copy_from_slice(&word32_words(11));
  row[action + C.action_words()] = F128::ONE;
  row[action + C.action_words() + 1..action + C.action_words() + 3]
    .copy_from_slice(&word32_words(22));
  row
}

#[test]
fn apply_rest_push_and_pop_preserve_order_kind_and_exact_fuel() {
  let gate = ControlStepGate::new(3, C).unwrap().with_applications();
  let input = over_application();
  let output = evaluate_words(gate.plan(), &input, gate.output_count());
  assert_eq!(output.last(), Some(&F128::ZERO));
  assert_eq!(output[0], meta(0, 8, 1, 0));
  assert_eq!(output[1], meta(7, 3, 1, 0));
  assert_eq!(&output[2..4], word32_words(11));
  let stack = C.stack_word(0);
  assert_eq!(output[stack], meta(0, 0, 1, 1));
  assert_eq!(&output[stack + 1..stack + 3], word32_words(22));
  check(gate.plan(), &input, gate.output_count(), true);
  let mut returning = output[..C.state_words()].to_vec();
  returning[0] = meta(1, 7, 1, 0);
  returning[1..1 + C.frame_words()].fill(F128::ZERO);
  returning[C.value_word()] = F128::new(PAP_TAG, 0);
  returning.resize(gate.input_count(), F128::ZERO);
  let output = evaluate_words(gate.plan(), &returning, gate.output_count());
  assert_eq!(output[0], meta(3, 6, 0, 0));
  assert_eq!(output[1], meta(0, 0, 1, 0));
  assert_eq!(&output[2..4], word32_words(22));
  assert_eq!(output[C.value_word()], F128::new(PAP_TAG, 0));
  assert!(
    output[stack..C.state_words()].iter().all(|word| *word == F128::ZERO)
  );
  check(gate.plan(), &returning, gate.output_count(), true);
}

#[test]
fn application_control_rejects_wide_metadata_padding_and_overflow_after_recomputation()
 {
  let gate = ControlStepGate::new(3, C).unwrap().with_applications();
  let good = over_application();
  let action = C.state_words();
  let mut bads = Vec::new();
  for (word, value) in [
    (0, meta(3, 0, 0, 0)),
    (0, meta(3, 9, u32::MAX, 0)),
    (0, meta(4, 9, 0, 0)),
    (0, meta(3, 9, 0, 1)),
    (1, meta(1, 0, 2, 0)),
    (1, meta(0, 1, 2, 0)),
    (1, meta(0, 0, u32::MAX, 0)),
    (1, meta(0, 0, 2, 1)),
    (action, meta(6, 0, 0, 7)),
    (action, meta(9, 1, 0, 7)),
    (action, meta(9, 0, 1, 7)),
    (action + 1, meta(3, 2, 1, 0)),
    (action + 1, meta(3, 1, 1, 1)),
    (action + 6, F128::ONE),
    (action + C.action_words(), F128::new(1 << 32, 0)),
    (action + C.action_words(), F128::new(u32::MAX as u64, 0)),
  ] {
    let mut input = good.clone();
    input[word] = value;
    bads.push(input);
  }
  let mut overflow = good.clone();
  overflow[0] = meta(3, 9, 1, 0);
  overflow[C.stack_word(0)] = meta(0, 0, 1, 1);
  overflow[C.stack_word(0) + 1..C.stack_word(0) + 3]
    .copy_from_slice(&word32_words(99));
  bads.push(overflow.clone());
  overflow[C.stack_word(0)] = meta(0, 0, 0, 1);
  bads.push(overflow.clone());
  overflow[C.stack_word(0)] = meta(0, 0, 1, 2);
  bads.push(overflow);
  for input in &bads {
    assert_eq!(
      evaluate_words(gate.plan(), input, gate.output_count()).last(),
      Some(&F128::ONE)
    );
  }
  check(gate.plan(), &bads[0], gate.output_count(), false);
  check(gate.plan(), bads.last().unwrap(), gate.output_count(), false);
}

#[test]
fn application_control_outputs_and_recycled_padding_are_constrained() {
  let gate = ControlStepGate::new(3, C).unwrap().with_applications();
  let input = over_application();
  let r1cs = gate.r1cs();
  let mut bits = vec![false; r1cs.n()];
  gate
    .plan()
    .fill_row(&mut bits[..gate.plan().k()], |bits| fill_words(&input, bits));
  assert!(r1cs.satisfies(&bits));
  for word in 0..gate.output_count() {
    for bit in [0, 32, 64, 127] {
      let position = 128 * (gate.input_count() + word) + bit;
      bits[position] ^= true;
      assert!(!r1cs.satisfies(&bits));
      bits[position] ^= true;
    }
  }
  let row = gate.eval(&input, &(), &mut Vec::new());
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(row.inputs(), bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
