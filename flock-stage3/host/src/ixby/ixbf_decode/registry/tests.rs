use super::super::{grammar, scalar_payload_tests};
use super::*;
use crate::{
  ixby::bits::fill_words,
  sizing::{CircuitEmitter, CountedGate, CountingEmitter},
};
use flock_prover::{
  circuit::builder::{GateType, ShapeBuilder},
  field::F128,
  r1cs::BlockR1cs,
};

fn w(value: u128) -> F128 {
  F128::new(value as u64, (value >> 64) as u64)
}
fn checked(gate: &RegistryGate, r1cs: &BlockR1cs, input: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  gate.eval(input, &(), &mut out);
  scalar_payload_tests::checked(gate.plan(), r1cs, input, &out);
  out
}
fn cap() -> RegistryCapacity {
  RegistryCapacity::new(2, 2, 2).unwrap()
}
fn bank() -> Vec<F128> {
  let cap = cap();
  let mut bank = vec![F128::ZERO; cap.words()];
  for cell in cap.cells() {
    let fields: Vec<_> = match (cell.kind, cell.owner, cell.index) {
      (RegistryOp::Constructor, _, i) => [
        w(1u128 << 100 | i as u128),
        w(1u128 << 127),
        w(1u128 << 120),
        w(1u128 << 119),
        w(3),
      ]
      .to_vec(),
      (RegistryOp::Function, _, 0) => [w(2), w(1), w(2)].to_vec(),
      (RegistryOp::Function, _, 1) => [w(4), w(0), w(1)].to_vec(),
      (RegistryOp::Block, 0, 0) => [w(3), w(0)].to_vec(),
      (RegistryOp::Block, 0, 1) => [w(2), w(1)].to_vec(),
      (RegistryOp::Block, 1, 0) => [w(4), w(1)].to_vec(),
      (RegistryOp::Block, 1, 1) => continue,
      _ => unreachable!(),
    };
    let (start, end) = match (cell.kind, cell.owner, cell.index) {
      (RegistryOp::Constructor, _, 0) => (20, 59),
      (RegistryOp::Constructor, _, 1) => (60, 105),
      (RegistryOp::Function, _, 0) => (106, 109),
      (RegistryOp::Function, _, 1) => (140, 143),
      (RegistryOp::Block, 0, 0) => (110, 112),
      (RegistryOp::Block, 0, 1) => (130, 132),
      (RegistryOp::Block, 1, 0) => (145, 147),
      _ => unreachable!(),
    };
    bank[cell.offset] = F128::ONE;
    bank[cell.offset + 1..cell.offset + cell.fields + 1]
      .copy_from_slice(&fields);
    bank[cell.offset + cell.fields + 1] = F128::new(start, end);
  }
  bank
}
fn finish_input() -> Vec<F128> {
  let mut input = vec![F128::ZERO; FINISH_BANK];
  input[0] = F128::new(151, 151);
  input[1] = w(grammar::Phase::Done as u128);
  input[grammar::CTORS] = w(2);
  input[grammar::FUNCTIONS] = w(2);
  input[grammar::FUNCTION_INDEX] = w(2);
  input[grammar::BLOCKS] = w(1);
  input[grammar::LOCALS] = w(4);
  input[grammar::ARITY] = w(4);
  input[grammar::LIMITS..grammar::LIMITS + 10].fill(w(u128::MAX));
  input[grammar::ENTRY] = w(1);
  input[grammar::ENTRY_ARITY] = w(4);
  input[grammar::FUEL] = w(1u128 << 100);
  input.extend(bank());
  input
}
fn capture_inputs() -> Vec<Vec<F128>> {
  let cap = cap();
  let final_bank = bank();
  let mut cells = cap.cells();
  cells.retain(|cell| final_bank[cell.offset] == F128::ONE);
  cells.sort_by_key(|cell| final_bank[cell.offset + cell.fields + 1].lo);
  let mut bank = vec![F128::ZERO; cap.words()];
  let mut rows = Vec::new();
  for cell in cells {
    let mut input = vec![F128::ZERO; CAPTURE_BANK];
    let span = final_bank[cell.offset + cell.fields + 1];
    input[0] = F128::new(span.lo, 151);
    input[NEXT] = F128::new(span.hi, 151);
    input[COMMITTED] = F128::ONE;
    input[FIELDS..FIELDS + cell.fields].copy_from_slice(
      &final_bank[cell.offset + 1..cell.offset + cell.fields + 1],
    );
    let (phase, tag) = match cell.kind {
      RegistryOp::Constructor => {
        input[grammar::CTORS] = w(2);
        input[grammar::CTORS_LEFT] = w(2 - cell.index as u128);
        (grammar::Phase::Constructor, 3)
      },
      RegistryOp::Function => {
        input[grammar::FUNCTIONS] = w(2);
        input[grammar::FUNCTIONS_LEFT] = w(2 - cell.index as u128);
        input[grammar::FUNCTION_INDEX] = w(cell.index as u128);
        (grammar::Phase::Function, 4)
      },
      RegistryOp::Block => {
        let function = cap.function(cell.owner);
        input[grammar::FUNCTION_INDEX] = w(cell.owner as u128 + 1);
        input[grammar::BLOCKS] = final_bank[function + 3];
        input[grammar::BLOCKS_LEFT] =
          w(u128::from(final_bank[function + 3].lo) - cell.index as u128);
        input[grammar::ARITY] = final_bank[function + 1];
        (grammar::Phase::Block, 5)
      },
      _ => unreachable!(),
    };
    input[1] = w(phase as u128);
    input[TAG] = w(tag);
    input.extend_from_slice(&bank);
    rows.push(input);
    bank[cell.offset..cell.offset + cell.fields + 2]
      .copy_from_slice(&final_bank[cell.offset..cell.offset + cell.fields + 2]);
  }
  rows
}
fn sample(op: RegistryOp) -> Vec<F128> {
  match op {
    RegistryOp::Capture => capture_inputs().pop().unwrap(),
    RegistryOp::Finish => finish_input(),
    _ => [vec![F128::ONE, F128::ZERO, F128::ZERO], bank()].concat(),
  }
}

#[test]
fn registry_capacities_are_explicit_and_bounded() {
  assert!(RegistryCapacity::new(5, 1, 1).is_err());
  for functions in [0, 5, usize::MAX] {
    assert!(RegistryCapacity::new(0, functions, 1).is_err());
  }
  for blocks in [0, 9, usize::MAX] {
    assert!(RegistryCapacity::new(0, 1, blocks).is_err());
  }
  for cap in [
    RegistryCapacity::new(0, 1, 1).unwrap(),
    RegistryCapacity::new(2, 2, 2).unwrap(),
    RegistryCapacity::new(4, 4, 8).unwrap(),
  ] {
    for op in RegistryOp::ALL {
      let gate = RegistryGate::new(3, cap, op).unwrap();
      eprintln!(
        "registry {cap:?} {op:?}: k={} useful={}",
        gate.plan().k(),
        gate.plan().useful_bits()
      );
      for nu in [2, 21] {
        assert!(RegistryGate::new(nu, cap, op).is_err());
      }
    }
  }
}

#[test]
fn registry_integer_relations_match_every_control_byte_and_full_width_mutations()
 {
  for op in RegistryOp::ALL {
    let gate = RegistryGate::new(3, cap(), op).unwrap();
    let r1cs = gate.r1cs();
    let sample = sample(op);
    assert_eq!(checked(&gate, &r1cs, &sample).last(), Some(&F128::ZERO));
    for byte in 0..=255 {
      let mut input = sample.clone();
      let at = if op == RegistryOp::Capture {
        TAG
      } else if op == RegistryOp::Finish {
        1
      } else {
        0
      };
      input[at] = w(byte);
      checked(&gate, &r1cs, &input);
    }
    for at in 0..sample.len() {
      for bit in [0, 7, 31, 63, 64, 127] {
        let mut input = sample.clone();
        if bit < 64 {
          input[at].lo ^= 1 << bit;
        } else {
          input[at].hi ^= 1 << (bit - 64);
        }
        checked(&gate, &r1cs, &input);
      }
    }
  }
}

#[test]
fn capture_requires_append_order_derived_owner_and_exact_carried_records() {
  let gate = RegistryGate::new(3, cap(), RegistryOp::Capture).unwrap();
  let r1cs = gate.r1cs();
  let inputs = capture_inputs();
  let mut last = Vec::new();
  for input in &inputs {
    if !last.is_empty() {
      assert_eq!(&input[CAPTURE_BANK..], &last[..last.len() - 1]);
    }
    last = checked(&gate, &r1cs, input);
    assert_eq!(last.last(), Some(&F128::ZERO));
    let mut repeated = input.clone();
    repeated[CAPTURE_BANK..].copy_from_slice(&last[..last.len() - 1]);
    assert_eq!(checked(&gate, &r1cs, &repeated).last(), Some(&F128::ONE));
    let mut skipped = input.clone();
    skipped[COMMITTED] = F128::ZERO;
    assert_eq!(checked(&gate, &r1cs, &skipped).last(), Some(&F128::ONE));
    for changed in [0, 1, NEXT] {
      let mut malformed = input.clone();
      malformed[changed] = F128::ZERO;
      // A zero start alone could be a valid component span; reversing it is not.
      if changed == 0 {
        malformed[0].lo = input[NEXT].lo + 1;
      }
      assert_eq!(checked(&gate, &r1cs, &malformed).last(), Some(&F128::ONE));
    }
  }
  assert_eq!(&last[..last.len() - 1], &bank());
  for (position, counter) in [
    (0, grammar::CTORS_LEFT),
    (2, grammar::FUNCTIONS_LEFT),
    (3, grammar::FUNCTION_INDEX),
    (3, grammar::BLOCKS_LEFT),
  ] {
    for number in [0, u64::MAX as u128, 1u128 << 64, u128::MAX] {
      let mut input = inputs[position].clone();
      input[counter] = w(number);
      assert_eq!(checked(&gate, &r1cs, &input).last(), Some(&F128::ONE));
    }
  }
  let mut no_previous = inputs[1].clone();
  no_previous[CAPTURE_BANK..CAPTURE_BANK + 7].fill(F128::ZERO);
  assert_eq!(checked(&gate, &r1cs, &no_previous).last(), Some(&F128::ONE));
  let mut no_owner = inputs[3].clone();
  let at = CAPTURE_BANK + cap().function(0);
  no_owner[at..at + 5].fill(F128::ZERO);
  assert_eq!(checked(&gate, &r1cs, &no_owner).last(), Some(&F128::ONE));
  for field in [grammar::BLOCKS, grammar::ARITY] {
    let mut mismatch = inputs[3].clone();
    mismatch[field].lo ^= 1;
    assert_eq!(checked(&gate, &r1cs, &mismatch).last(), Some(&F128::ONE));
  }
  // Intermediate String chunks and Done are carry rows, not new records.
  for (tag, commit) in [(15, 0), (15, 1), (17, 0)] {
    let mut input = inputs.last().unwrap().clone();
    input[TAG] = w(tag);
    input[COMMITTED] = w(commit);
    let out = checked(&gate, &r1cs, &input);
    assert_eq!(out.last(), Some(&F128::ZERO));
    assert_eq!(&out[..out.len() - 1], &input[CAPTURE_BANK..]);
  }
}

#[test]
fn completion_requires_exact_coverage_unique_full_identities_and_entry_frames()
{
  let gate = RegistryGate::new(3, cap(), RegistryOp::Finish).unwrap();
  let r1cs = gate.r1cs();
  let good = finish_input();
  assert_eq!(checked(&gate, &r1cs, &good), [F128::ZERO]);
  for cell in cap().cells() {
    let mut input = good.clone();
    let at = FINISH_BANK + cell.offset;
    if input[at] == F128::ONE {
      input[at..at + cell.fields + 2].fill(F128::ZERO);
    } else {
      input[at] = F128::ONE;
      input[at + 1] = w(4);
      input[at + 2] = w(1);
      input[at + 3] = F128::new(147, 149);
    }
    assert_eq!(checked(&gate, &r1cs, &input), [F128::ONE]);
  }
  for at in [
    grammar::CTORS,
    grammar::FUNCTIONS,
    grammar::FUNCTION_INDEX,
    grammar::CTORS_LEFT,
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
    grammar::ENTRY_ARITY,
  ] {
    let mut input = good.clone();
    input[at].lo ^= 1;
    assert_eq!(checked(&gate, &r1cs, &input), [F128::ONE]);
  }
  for at in [
    FINISH_BANK + cap().function(0) + 1,
    FINISH_BANK + cap().block(0, 1) + 1,
    FINISH_BANK + cap().block(1, 0) + 1,
  ] {
    let mut input = good.clone();
    input[at].hi ^= 1;
    assert_eq!(checked(&gate, &r1cs, &input), [F128::ONE]);
  }
  let mut wide = good.clone();
  wide[FINISH_BANK + cap().function(0) + 1] = w(u128::MAX);
  wide[FINISH_BANK + cap().block(0, 1) + 1] = w(u128::MAX);
  assert_eq!(checked(&gate, &r1cs, &wide), [F128::ZERO]);
  for limit in [grammar::LIMITS + 3, grammar::LIMITS + 4] {
    let mut input = wide.clone();
    input[limit] = w(u128::MAX - 1);
    assert_eq!(checked(&gate, &r1cs, &input), [F128::ONE]);
  }
  let mut duplicate = good.clone();
  let first = duplicate[FINISH_BANK + 1..FINISH_BANK + 5].to_vec();
  duplicate[FINISH_BANK + 8..FINISH_BANK + 12].copy_from_slice(&first);
  duplicate[FINISH_BANK + 12] = w(2); // changing field count cannot hide a duplicate
  assert_eq!(checked(&gate, &r1cs, &duplicate), [F128::ONE]);
  for bit in 0..512 {
    let mut distinct = duplicate.clone();
    let at = FINISH_BANK + 8 + bit / 128;
    if bit % 128 < 64 {
      distinct[at].lo ^= 1 << (bit % 64);
    } else {
      distinct[at].hi ^= 1 << (bit % 64);
    }
    assert_eq!(checked(&gate, &r1cs, &distinct), [F128::ZERO]);
  }
  for input in [
    {
      let mut i = good.clone();
      i[0].lo -= 1;
      i
    },
    {
      let mut i = good.clone();
      i[0] = F128::new(146, 146);
      i
    },
    {
      let mut i = good.clone();
      i[1] = F128::ZERO;
      i
    },
    {
      let mut i = good.clone();
      i[grammar::ENTRY] = w(2);
      i
    },
  ] {
    assert_eq!(checked(&gate, &r1cs, &input), [F128::ONE]);
  }
}

#[test]
fn registry_reads_reject_absent_full_width_indices_owners_and_noncanonical_padding()
 {
  for op in [RegistryOp::Constructor, RegistryOp::Function, RegistryOp::Block] {
    let gate = RegistryGate::new(3, cap(), op).unwrap();
    let r1cs = gate.r1cs();
    for index in [0, 1, 2, 1u128 << 64, u128::MAX] {
      for owner in [0, 1, 2, 1u128 << 64, u128::MAX] {
        for enabled in [0, 1, 2, 3, 1u128 << 64] {
          let input = [vec![w(enabled), w(index), w(owner)], bank()].concat();
          let found = cap().cells().into_iter().find(|c| {
            c.kind == op
              && c.index as u128 == index
              && c.owner as u128 == owner
              && input[READ_BANK + c.offset] == F128::ONE
          });
          let valid = (enabled == 0 && index == 0 && owner == 0)
            || (enabled == 1 && found.is_some());
          let out = checked(&gate, &r1cs, &input);
          assert_eq!(out.last() == Some(&F128::ZERO), valid);
          if enabled == 0 {
            assert_eq!(out[..6], [F128::ZERO; 6]);
          } else if enabled == 1 && valid {
            let cell = found.unwrap();
            assert_eq!(
              &out[..cell.fields],
              &input[READ_BANK + cell.offset + 1
                ..READ_BANK + cell.offset + cell.fields + 1]
            );
            assert!(out[cell.fields..5].iter().all(|w| *w == F128::ZERO));
            assert_eq!(
              out[5],
              input[READ_BANK + cell.offset + cell.fields + 1]
            );
          }
        }
      }
    }
    let sample = sample(op);
    for cell in cap().cells() {
      let at = READ_BANK + cell.offset;
      for bit in 1..128 {
        let mut malformed = sample.clone();
        if bit < 64 {
          malformed[at].lo ^= 1 << bit;
        } else {
          malformed[at].hi ^= 1 << (bit - 64);
        }
        assert_eq!(checked(&gate, &r1cs, &malformed).last(), Some(&F128::ONE));
      }
    }
    let absent = READ_BANK + cap().block(1, 1);
    for at in absent + 1..absent + 4 {
      for bit in 0..128 {
        let mut malformed = sample.clone();
        if bit < 64 {
          malformed[at].lo ^= 1 << bit;
        } else {
          malformed[at].hi ^= 1 << (bit - 64);
        }
        assert_eq!(checked(&gate, &r1cs, &malformed).last(), Some(&F128::ONE));
      }
    }
  }
}

#[test]
fn registry_outputs_padding_and_lazy_count_shape_are_fully_constrained() {
  for op in RegistryOp::ALL {
    let gate = RegistryGate::new(3, cap(), op).unwrap();
    let mut count = CountingEmitter::new();
    let slot = count.slot(gate.clone());
    let input: Vec<_> =
      (0..gate.input_count()).map(|_| count.input()).collect();
    count.gate(slot, &input);
    assert!(gate.plan.get().is_none());
    let mut builder = ShapeBuilder::new(3);
    let slot = builder.slot(gate.clone());
    let input: Vec<_> =
      (0..gate.input_count()).map(|_| builder.input()).collect();
    builder.gate(slot, &input);
    let shape = builder.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    let input = sample(op);
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
      let rows = vec![RegistryRow(input.clone()); count];
      crate::ixby::test_support::padding(
        gate.plan(),
        &rows,
        |row, bits| fill_words(&row.0, bits),
        |dst| gate.generate_witness_into(&rows, dst),
      );
    }
  }
}
