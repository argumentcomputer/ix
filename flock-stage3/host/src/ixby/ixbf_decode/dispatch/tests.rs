use super::super::{GrammarKind, scalar_payload_tests};
use super::*;
use crate::{
  ixby::bits::fill_words,
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{GateType, ShapeBuilder},
  field::F128,
};

fn checked(
  gate: &DispatchGate,
  r1cs: &flock_prover::r1cs::BlockR1cs,
  input: &[F128],
) -> Vec<F128> {
  let mut out = Vec::new();
  gate.eval(input, &(), &mut out);
  scalar_payload_tests::checked(gate.plan(), r1cs, input, &out);
  out
}

#[test]
fn controls_match_independent_integer_evaluation_including_reserved_bits_and_underflows()
 {
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    let config = model_tests::config(kind);
    for op in DispatchOp::ALL {
      let gate = DispatchGate::new(3, config, op).unwrap();
      let r1cs = gate.r1cs();
      for tag in 0..=255u64 {
        let mut input: Vec<_> = (0..gate.input_count())
          .map(|i| F128::new(i as u64 * 17 + 1, i as u64 * 31 + 3))
          .collect();
        match op {
          DispatchOp::Initialize => {
            input.fill(F128::ZERO);
            input[0] = F128::new(tag, 0);
          },
          DispatchOp::Request => {
            input[0] = F128::new(12, 1024);
            input[1] = F128::new(tag, 0);
            input[28] = F128::ZERO;
            input[29] = F128::ZERO;
          },
          DispatchOp::Finish => {
            input[61] = F128::new(tag, 0);
            input[58] = F128::new(64, 1024);
            input[60] = input[58];
            input[59] =
              if tag % 2 == 0 { F128::ZERO } else { F128::new(32, 6) };
          },
          _ => input[0] = F128::new(tag, 0),
        }
        checked(&gate, &r1cs, &input);
      }
      let input = vec![F128::ZERO; gate.input_count()];
      for field in 0..input.len() {
        for bit in [0, 7, 31, 40, 63, 64, 65, 127] {
          let mut altered = input.clone();
          if bit < 64 {
            altered[field].lo ^= 1 << bit;
          } else {
            altered[field].hi ^= 1 << (bit - 64);
          }
          checked(&gate, &r1cs, &altered);
        }
      }
    }
    let gate = DispatchGate::new(3, config, DispatchOp::Request).unwrap();
    let r1cs = gate.r1cs();
    for seen in [0u128, 1, u64::MAX as u128, 1u128 << 64, u128::MAX] {
      for limit in [0u128, seen.wrapping_add(1), u128::MAX] {
        let mut input = vec![F128::ZERO; 30];
        input[0] = F128::new(13, 1024);
        input[1] = F128::new(19, 0);
        input[13] = F128::new(seen as u64, (seen >> 64) as u64);
        input[20] = F128::new(limit as u64, (limit >> 64) as u64);
        checked(&gate, &r1cs, &input);
      }
    }
  }
}

#[test]
fn every_natural_terminator_is_derived_and_following_records_are_not_payload_padding()
 {
  let config = model_tests::config(GrammarKind::Program);
  let gate =
    DispatchGate::new(3, config, DispatchOp::NaturalLookahead).unwrap();
  let r1cs = gate.r1cs();
  for at in 0..config.natural.encoded_bytes() {
    let mut bytes = vec![255; config.natural.encoded_words() * 16];
    bytes[at] = 1;
    let mut input = vec![F128::ONE];
    input.extend(
      bytes.as_chunks::<16>().0.iter().map(|w| crate::hash::pack_bytes(w)),
    );
    let output = checked(&gate, &r1cs, &input);
    assert_eq!(output[0], F128::new(at as u64 + 1, 0));
    assert_eq!(output.last(), Some(&F128::ZERO));
    let encoded: Vec<_> = output[1..output.len() - 1]
      .iter()
      .flat_map(|w| w.lo.to_le_bytes().into_iter().chain(w.hi.to_le_bytes()))
      .collect();
    assert_eq!(&encoded[..=at], &bytes[..=at]);
    assert!(encoded[at + 1..].iter().all(|b| *b == 0));
  }
  let mut input = vec![F128::new(u64::MAX, u64::MAX); gate.input_count()];
  input[0] = F128::ONE;
  assert_eq!(checked(&gate, &r1cs, &input).last(), Some(&F128::ONE));
}

#[test]
fn dispatch_output_columns_padding_recycled_buffers_and_lazy_counts_are_bound()
{
  for op in DispatchOp::ALL {
    let gate =
      DispatchGate::new(3, model_tests::config(GrammarKind::Program), op)
        .unwrap();
    let mut count = CountingEmitter::new();
    let slot = count.slot(gate.clone());
    let input: Vec<_> =
      (0..gate.input_count()).map(|_| count.input()).collect();
    count.gate(slot, &input);
    assert!(gate.plan.get().is_none());
    let mut shape = ShapeBuilder::new(3);
    let slot = shape.slot(gate.clone());
    let input: Vec<_> =
      (0..gate.input_count()).map(|_| shape.input()).collect();
    shape.gate(slot, &input);
    let shape = shape.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    let input = vec![F128::ZERO; gate.input_count()];
    let r1cs = gate.r1cs();
    let output = checked(&gate, &r1cs, &input);
    let mut row =
      scalar_payload_tests::checked(gate.plan(), &r1cs, &input, &output);
    super::super::tests::output_bits_are_bound(
      &r1cs,
      &mut row,
      input.len() * 128,
      output.len() * 128,
    );
    row[gate.plan().k() - 1] = true;
    assert!(!super::super::tests::satisfies(&r1cs, &row));
    for count in [0, 1, 5] {
      let rows = vec![DispatchRow(input.clone()); count];
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
    for nu in [2, 21] {
      assert!(DispatchGate::new(nu, gate.config(), op).is_err());
    }
  }
}

#[test]
fn control_plans_build_for_all_kinds_and_natural_capacities() {
  use super::super::{GrammarKind, NaturalCapacity};
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    for bits in [0, 128, 4096] {
      let config =
        DispatchConfig { kind, natural: NaturalCapacity::new(bits).unwrap() };
      for op in DispatchOp::ALL {
        let gate = DispatchGate::new(3, config, op).unwrap();
        eprintln!(
          "dispatch {kind:?}/{bits}/{op:?}: k={} useful={}",
          gate.plan().k(),
          gate.plan().useful_bits()
        );
      }
    }
  }
}
