use super::*;
use crate::ixby::{
  decode::test_support::meta,
  object_value::test_support::{CONTROL, check, flip, layout},
  value::{ValueWords, WORD32_TAG, word32_words},
};

fn gate() -> PapDispatchGate {
  let mut layout = layout();
  layout.applications = true;
  PapDispatchGate::new(3, layout, CONTROL)
}
fn function_table() -> usize {
  1 + CONTROL.state_words() + 5 + 6
}
fn arena() -> usize {
  function_table() + 2
}
fn function_value() -> usize {
  2 + CONTROL.frame_words()
}
fn pap(index: u32) -> ValueWords {
  [F128::new(PAP_TAG, 0), F128::new(index.into(), 0)]
}
fn row(
  gate: &PapDispatchGate,
  arity: u32,
  captured: usize,
  args: usize,
) -> Vec<F128> {
  let mut input = vec![F128::ZERO; gate.input_count()];
  input[0] = F128::new(gate.layout.input_slots() as u64, 0);
  input[1] = meta(3, 9, 0, 0);
  input[2] = meta(0, 0, args as u32, 0);
  for arg in 0..args {
    input[3 + 2 * arg..5 + 2 * arg]
      .copy_from_slice(&word32_words(10 + arg as u32));
  }
  input[function_value()..function_value() + 2].copy_from_slice(&pap(0));
  input[function_table()] = meta(0, 1, 0, 0);
  input[function_table() + 1] = meta(arity, 0, 1, 0);
  input[arena()] = meta(0, captured as u32, 3, 0);
  for index in 0..captured {
    input[arena() + 1 + 2 * index..arena() + 3 + 2 * index]
      .copy_from_slice(&word32_words(100 + index as u32));
  }
  input
}

#[test]
fn pap_resolution_preserves_capture_argument_order_and_full_rest_vectors() {
  let gate = gate();
  for arity in 1..=2 {
    for captured in 0..arity as usize {
      for args in 0..=2 {
        let input = row(&gate, arity, captured, args);
        let mut out = Vec::new();
        gate.eval(&input, &(), &mut out);
        assert_eq!(out.last(), Some(&F128::ZERO));
        if args == 0 {
          assert_eq!(out[0], meta(0, 14, 0, 0));
          assert_eq!(&out[3..5], pap(0));
        } else if captured + args < arity as usize {
          assert_eq!(out[0], meta(0, 14, 0, 0));
          assert_eq!(&out[3..5], pap(gate.layout.input_slots() as u32));
          assert_eq!(
            out[gate.normalized_words()],
            meta(0, (captured + args) as u32, 3, 0)
          );
        } else {
          assert_eq!(out[0], meta(0, 15, 0, 0));
          assert_eq!(out[1], meta(0, 0, arity, 0));
          let supplied: Vec<_> = (0..captured)
            .map(|i| word32_words(100 + i as u32))
            .chain((0..args).map(|i| word32_words(10 + i as u32)))
            .collect();
          assert_eq!(
            &out[5..5 + 2 * arity as usize],
            supplied[..arity as usize].concat()
          );
          let rest = supplied.len() - arity as usize;
          assert_eq!(out[11], F128::new(rest as u64, 0));
          assert_eq!(
            &out[12..12 + 2 * rest],
            supplied[arity as usize..].concat()
          );
        }
      }
    }
  }
  let input = row(&gate, 2, 1, 2);
  check(gate.plan(), &input, gate.output_count(), true);
}

#[test]
fn pap_headers_function_indices_counts_types_and_new_backedges_are_constrained()
{
  let gate = gate();
  let good = row(&gate, 2, 1, 1);
  let mut bads = Vec::new();
  for value in [
    meta(0, 1, 0, 0),
    meta(0, 1, 1, 0),
    meta(0, 1, 7, 0),
    meta(1, 1, 3, 0),
    meta(1 << 31, 1, 3, 0),
    meta(0, 2, 3, 0),
    meta(0, u32::MAX, 3, 0),
  ] {
    let mut input = good.clone();
    input[arena()] = value;
    bads.push(input);
  }
  for index in [gate.layout.entries() as u64, 1 << 31, u32::MAX as u64, 1 << 32]
  {
    let mut input = good.clone();
    input[function_value() + 1] = F128::new(index, 0);
    bads.push(input);
  }
  for word in [function_value(), function_value() + 1, arena() + 1, arena() + 2]
  {
    let mut input = good.clone();
    flip(&mut input[word], 127);
    bads.push(input);
  }
  let mut padding = good.clone();
  padding[arena() + 3] = F128::new(WORD32_TAG, 0);
  bads.push(padding);
  for value in [word32_words(11), [F128::new(0xff, 0), F128::ZERO]] {
    let mut input = good.clone();
    input[function_value()..function_value() + 2].copy_from_slice(&value);
    bads.push(input);
  }
  let header = 1 + CONTROL.state_words();
  let mut closure = row(&gate, 2, 0, 0);
  closure[1] = meta(0, 9, 0, 0);
  closure[function_value()..function_value() + 2].fill(F128::ZERO);
  closure[header] = meta(0, 11, 1, 0);
  closure[header + 1] = meta(0, 0, 1, 0);
  closure[header + 5..header + 7].copy_from_slice(&pap(0));
  let mut out = Vec::new();
  gate.eval(&closure, &(), &mut out);
  assert_eq!(out.last(), Some(&F128::ZERO));
  for index in [
    gate.layout.input_slots(),
    gate.layout.entries() - 1,
    gate.layout.entries(),
  ] {
    let mut input = closure.clone();
    input[header + 6] = F128::new(index as u64, 0);
    bads.push(input);
  }
  for input in &bads {
    let mut out = Vec::new();
    gate.eval(input, &(), &mut out);
    assert_eq!(
      out.last(),
      Some(&F128::ONE),
      "unrejected PAP metadata {input:?}"
    );
  }
  check(gate.plan(), &bads[0], gate.output_count(), false);
  check(gate.plan(), bads.last().unwrap(), gate.output_count(), false);
}

#[test]
fn pap_outputs_and_recycled_padding_are_constrained() {
  let gate = gate();
  let input = row(&gate, 2, 0, 1);
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
  bits[gate.plan().k() - 1] = true;
  assert!(!r1cs.satisfies(&bits));
  let row = gate.eval(&input, &(), &mut Vec::new());
  for rows in [vec![], vec![row.clone()], vec![row; 3]] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| fill_words(&row.0, bits),
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
}
