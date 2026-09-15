use super::*;

fn bits(gate: &Fuel64StepGate, input: [F128; 3]) -> Vec<bool> {
  let mut row = vec![false; gate.plan().k()];
  gate.plan().fill_row(&mut row, |bits| {
    for (word, value) in input.iter().enumerate() {
      write_f128(bits, word * 128, *value);
    }
  });
  let expected = evaluate(&Fuel64StepRow(input));
  let mut outputs = vec![false; 256];
  for (word, value) in expected.iter().enumerate() {
    write_f128(&mut outputs, word * 128, *value);
  }
  assert_eq!(&row[384..640], outputs);
  row
}

fn satisfies(r1cs: &BlockR1cs, bits: &[bool]) -> bool {
  let mut full = vec![false; r1cs.n()];
  full[..bits.len()].copy_from_slice(bits);
  r1cs.satisfies(&full)
}

fn reject(gate: &Fuel64StepGate, input: [F128; 3]) {
  let mut row = bits(gate, input);
  assert!(row[512]);
  assert!(satisfies(&gate.r1cs(), &row));
  row[512] = false;
  assert!(
    !satisfies(&gate.r1cs(), &row),
    "recomputed invalid advice bypassed the zero pin"
  );
}

#[test]
fn full_width_budgets_consumption_and_halted_padding_match_integer_arithmetic()
{
  let gate = Fuel64StepGate::new(3).unwrap();
  let r1cs = gate.r1cs();
  for budget in
    [0, 1, u64::from(u32::MAX), 1 << 32, 16_000_000_000, 1 << 63, u64::MAX]
  {
    for remaining in [0, 1.min(budget), budget / 2, budget] {
      for kind in 0..4 {
        let input = [
          F128::new(remaining, budget - remaining),
          F128::new(kind, 0),
          F128::new(budget, 0),
        ];
        let row = bits(&gate, input);
        assert!(satisfies(&r1cs, &row));
        assert_eq!(row[512], remaining == 0 && kind != 2);
        if kind == 2 {
          assert_eq!(evaluate(&Fuel64StepRow(input))[0], input[0]);
        }
      }
    }
  }
}

#[test]
fn every_output_bit_is_bound_and_invalid_full_width_advice_cannot_wrap() {
  let gate = Fuel64StepGate::new(3).unwrap();
  let budget = 16_000_000_000;
  let input =
    [Fuel64::initial(budget).word(), F128::new(3, 0), F128::new(budget, 0)];
  let good = bits(&gate, input);
  let r1cs = gate.r1cs();
  for bit in 384..640 {
    let mut changed = good.clone();
    changed[bit] ^= true;
    assert!(!satisfies(&r1cs, &changed));
  }
  for invalid in [
    [F128::new(0, 0), F128::ZERO, F128::ZERO],
    [F128::new(1, u64::MAX), F128::ZERO, F128::ZERO],
    [F128::new(1 << 32, 0), F128::ZERO, F128::ZERO],
    [F128::new(budget, 1), F128::ZERO, F128::new(budget, 0)],
    [F128::new(0, u64::MAX), F128::ZERO, F128::new(u64::MAX, 0)],
  ] {
    reject(&gate, invalid);
  }
  for bit in 2..32 {
    let mut changed = input;
    changed[1].lo = 1 << bit;
    reject(&gate, changed);
  }
  for bit in 0..64 {
    let mut changed = input;
    changed[2].hi = 1 << bit;
    reject(&gate, changed);
  }
}

#[test]
fn non_kind_control_metadata_is_left_to_the_separate_control_constraints() {
  let gate = Fuel64StepGate::new(3).unwrap();
  let input = [
    Fuel64::initial(16_000_000_000).word(),
    F128::new(1, 0),
    F128::new(16_000_000_000, 0),
  ];
  let expected = evaluate(&Fuel64StepRow(input));
  for bit in 32..128 {
    let mut changed = input;
    if bit < 64 {
      changed[1].lo |= 1 << bit;
    } else {
      changed[1].hi |= 1 << (bit - 64);
    }
    assert_eq!(evaluate(&Fuel64StepRow(changed)), expected);
    assert!(satisfies(&gate.r1cs(), &bits(&gate, changed)));
  }
}

#[test]
fn wide_fuel_driver_clears_every_unused_row_column_and_constant_stripe() {
  let gate = Fuel64StepGate::new(3).unwrap();
  for rows in [
    vec![],
    vec![Fuel64StepRow([F128::ZERO; 3])],
    vec![
      Fuel64StepRow([
        Fuel64::initial(16_000_000_000).word(),
        F128::ZERO,
        F128::new(16_000_000_000, 0)
      ]);
      5
    ],
  ] {
    crate::ixby::test_support::padding(
      gate.plan(),
      &rows,
      |row, bits| {
        for (word, value) in row.0.iter().enumerate() {
          write_f128(bits, word * 128, *value);
        }
      },
      |dst| gate.generate_witness_into(&rows, dst),
    );
  }
  let mut unused =
    bits(&gate, [Fuel64::initial(3).word(), F128::ZERO, F128::new(3, 0)]);
  unused[gate.plan().k() - 1] = true;
  assert!(!satisfies(&gate.r1cs(), &unused));
}

#[test]
fn counted_and_emitted_ledgers_match_without_budget_or_trace_specialization() {
  use crate::sizing::CountingEmitter;
  use flock_prover::circuit::builder::ShapeBuilder;
  fn emit(b: &mut impl CircuitEmitter, gate: Fuel64StepGate, steps: usize) {
    let slot = Fuel64StepSlot::declare(b, gate);
    let budget = b.public_input();
    let mut fuel = b.public_input();
    for _ in 0..steps {
      let control = b.input();
      fuel = slot.step(b, fuel, control, budget);
    }
    b.publish(fuel);
  }
  for steps in [1, 3, 8, 24] {
    let gate = Fuel64StepGate::new(5).unwrap();
    let mut count = CountingEmitter::new();
    emit(&mut count, gate.clone(), steps);
    assert!(gate.plan.get().is_none());
    let mut real = ShapeBuilder::new(5);
    emit(&mut real, gate, steps);
    let shape = real.finish().unwrap();
    count.ensure_matches(&shape).unwrap();
    assert_eq!(count.registry(5).1, shape.counts);
  }
  assert!(Fuel64StepGate::new(2).is_err());
  assert!(Fuel64StepGate::new(21).is_err());
}
