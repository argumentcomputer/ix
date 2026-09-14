// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use multi_stark::eval::{VarValues, eval_expr};

fn values<'a>(row: &'a [G], next: &'a [G]) -> VarValues<'a, G> {
  VarValues {
    preprocessed: [&[], &[]],
    main: [row, next],
    stage2: [&[], &[]],
    publics: &[],
    is_first_row: G::ONE,
    is_last_row: G::ZERO,
    is_transition: G::ONE,
  }
}

/// Retain the entry singleton and group the nested callees, whose auxiliary
/// and lookup widths differ and whose selectors occupy separate columns.
fn grouped_promotion_toplevel() -> Toplevel {
  let mut top = unconstrained_call_promotion_toplevel();
  top.circuits.truncate(1);
  top.circuits.push(crate::bytecode::Circuit {
    members: vec![1, 2],
    layout: FunctionLayout {
      input_size: 1,
      selectors: 2,
      auxiliaries: 8,
      lookups: 8,
    },
  });
  top
}

#[test]
fn inactive_function_multiplicity_is_constrained_in_every_partition() {
  for mut top in [mul_toplevel(), grouped_promotion_toplevel()] {
    // Generate a concrete active row for each member. Entry visibility is
    // only an executor guard and does not alter these AIR constraints.
    for function in &mut top.functions {
      function.entry = true;
    }
    for (idx, circuit) in top.circuits.iter().enumerate() {
      let (constraints, lookups) = top.build_constraints(idx);
      let mut row = vec![G::ZERO; constraints.width];
      let multiplicity = circuit.layout.input_size + circuit.layout.selectors;
      for nonzero in [G::ONE, -G::ONE, G::from_u8(7)] {
        row[multiplicity] = nonzero;
        assert!(
          constraints
            .zeros
            .iter()
            .any(|c| eval_expr(c, &values(&row, &row)) != G::ZERO),
          "inactive circuit {idx} accepted multiplicity {nonzero}"
        );
        // Every fixture member has one return selector. Activating any
        // member must permit the multiplicity, including the later members
        // of a group. These are local constraint checks; the roundtrip
        // below also checks global lookup balance for an honest execution.
        for &member in &circuit.members {
          assert_eq!(top.functions[member].layout.selectors, 1);
          let mut io_buffer = empty_io_buffer();
          let input = vec![G::ZERO; top.functions[member].layout.input_size];
          let (record, _) = top.execute(member, input, &mut io_buffer).unwrap();
          let widths =
            lookups.iter().map(|lookup| lookup.args.len()).collect::<Vec<_>>();
          let (trace, _, _) =
            top.witness_data(idx, &record, &io_buffer, &widths);
          let mut active = trace.values[..constraints.width].to_vec();
          active[multiplicity] = nonzero;
          assert!(
            constraints
              .zeros
              .iter()
              .all(|c| eval_expr(c, &values(&active, &active)) == G::ZERO),
            "active member {member} rejected multiplicity {nonzero}"
          );
        }
      }
      row[multiplicity] = G::ZERO;
      assert!(
        constraints
          .zeros
          .iter()
          .all(|c| eval_expr(c, &values(&row, &row)) == G::ZERO)
      );
    }
  }
}

#[test]
fn inactive_memory_multiplicity_is_constrained() {
  for width in [1, 4, 8] {
    let (memory, constraints, _) = Memory::build(width);
    let mut row = vec![G::ZERO; memory.width];
    let next = row.clone();
    for nonzero in [G::ONE, -G::ONE, G::from_u8(7)] {
      row[0] = nonzero;
      assert!(
        constraints
          .iter()
          .any(|c| eval_expr(c, &values(&row, &next)) != G::ZERO)
      );
      row[1] = G::ONE;
      assert!(
        constraints
          .iter()
          .all(|c| eval_expr(c, &values(&row, &next)) == G::ZERO)
      );
      row[1] = G::ZERO;
    }
    row[0] = G::ZERO;
    assert!(
      constraints.iter().all(|c| eval_expr(c, &values(&row, &next)) == G::ZERO)
    );
  }
}

#[test]
fn active_grouped_returns_verify() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(grouped_promotion_toplevel(), cp, fp);
  let input = [G::from_u8(3)];
  let (claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
  assert_eq!(
    claim,
    vec![function_channel(), G::ZERO, input[0], input[0] + G::ONE]
  );
  system.verify(&claim, &proof).expect("active grouped returns must verify");
}

/// Exercise the public verifier with supplied trace rows, independently of
/// the execution record. A successful honest execution alone cannot check
/// whether inactive rows are permitted to provide a function result.
#[test]
fn inactive_return_cannot_supply_claim() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let a = G::from_u8(3);
  let b = G::from_u8(5);
  let wrong_result = G::from_u8(16);
  assert_ne!(a * b, wrong_result);
  let claim = vec![function_channel(), G::ZERO, a, b, wrong_result];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(i, shape)| {
      let height = if i == 0 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if i == 0 {
        // Inputs, inactive selector, return multiplicity, three u16 rank limbs,
        // then unconstrained product advice.
        rows[..4].copy_from_slice(&[a, b, G::ZERO, G::ONE]);
        rows[7] = wrong_result;
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "an inactive function row supplied an incorrect public result"
  );
}

/// A function that only calls itself has no finite execution. Its return
/// lookup must not be justified by the same row's recursive call lookup.
#[test]
fn recursive_cycle_cannot_supply_claim() {
  let function = Function {
    body: Block {
      ops: vec![Op::Call(0, vec![0], 1, false)],
      ctrl: Ctrl::Return(0, vec![1]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 8,
      lookups: 8,
    },
    entry: true,
    constrained: true,
  };
  let top = with_singleton_circuits(vec![function], vec![]);
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  let input = G::from_u8(3);
  let output = G::from_u8(7);
  let claim = vec![function_channel(), G::ZERO, input, output];
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(i, shape)| {
      let height = if i == 0 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if i == 0 {
        // One active row provides twice: once to its own recursive call,
        // and once to the public claim. No evaluator is used.
        rows[..3].copy_from_slice(&[input, G::ONE, G::from_u8(2)]);
        rows[6] = output;
      } else if i == system.toplevel.circuits.len() + 1 {
        // Six zero u16 limbs: three for the row rank and three for the
        // call gap. Balance these lookups so rejection tests call order.
        rows[Bytes2::U16_RANGE_CHECK_COLUMN] = G::from_u8(6);
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  let proof = system.system.prove(&system.key, &claim, witness);
  assert!(
    system.verify(&claim, &proof).is_err(),
    "a recursive cycle supplied a public return value without a finite execution"
  );
}
