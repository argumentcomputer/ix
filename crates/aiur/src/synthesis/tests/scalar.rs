// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use multi_stark::eval::{VarValues, eval_expr};
use multi_stark::p3_field::Field;

fn eq_zero_program() -> Toplevel {
  with_singleton_circuits(
    vec![Function {
      body: Block { ops: vec![Op::EqZero(0)], ctrl: Ctrl::Return(0, vec![1]) },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 9,
        lookups: 4,
      },
      entry: true,
      constrained: true,
    }],
    vec![],
  )
}

/// Check the actual emitted expressions over inactive, active and malformed
/// selectors. Inactive rows may carry arbitrary equality-test advice.
#[test]
fn scalar_constraints_extract_boolean_and_eq_zero_semantics() {
  let top = eq_zero_program();
  let (function, _) = top.build_constraints(0);
  let (_, memory, _) = Memory::build(1);
  let inputs = [G::ZERO, G::from_u8(3), -G::ONE];
  let selectors = [G::ZERO, G::ONE, G::from_u8(2), -G::ONE];
  let outputs = [G::ZERO, G::ONE, G::from_u8(2)];
  for input in inputs {
    for selector in selectors {
      for output in outputs {
        for inverse in
          [G::ZERO, G::from_u8(4), input.try_inverse().unwrap_or_default()]
        {
          let mut row = vec![G::ZERO; function.width];
          row[0] = input;
          row[1] = selector;
          row[9] = inverse;
          row[10] = output;
          let values = VarValues {
            preprocessed: [&[], &[]],
            main: [&row, &row],
            stage2: [&[], &[]],
            publics: &[],
            is_first_row: G::ZERO,
            is_last_row: G::ONE,
            is_transition: G::ZERO,
          };
          let satisfied =
            function.zeros.iter().all(|e| eval_expr(e, &values) == G::ZERO);
          let expected = selector == G::ZERO
            || (selector == G::ONE
              && output == G::from_bool(input == G::ZERO)
              && (input == G::ZERO || Some(inverse) == input.try_inverse()));
          assert_eq!(
            satisfied, expected,
            "input {input}, selector {selector}, output {output}, inverse {inverse}"
          );
          // Same selector column in memory. Multiplicity remains zero and
          // this last row has no active transition constraints.
          let memory_row = [G::ZERO, selector, G::from_u8(7), G::from_u8(8)];
          let memory_values =
            VarValues { main: [&memory_row, &memory_row], ..values };
          assert_eq!(
            memory.iter().all(|e| eval_expr(e, &memory_values) == G::ZERO),
            selector == G::ZERO || selector == G::ONE,
            "memory selector {selector}"
          );
        }
      }
    }
  }
}

/// Supply rows independently of the executor, with balanced public/function
/// and rank-byte messages. Forged outputs must fail the native verifier.
#[test]
fn supplied_eq_zero_outputs_are_constrained() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(eq_zero_program(), cp, fp);
  let three = G::from_u8(3);
  let inverse = three.inverse();
  let cases = [
    (G::ZERO, G::from_u8(4), G::ONE, true),
    (three, inverse, G::ZERO, true),
    (G::ZERO, G::from_u8(4), G::ZERO, false),
    (three, G::ZERO, G::ONE, false),
    (three, -inverse, G::from_u8(2), false),
  ];
  for (input, advice, output, accepted) in cases {
    let claim = [function_channel(), G::ZERO, input, output];
    let traces = system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(index, shape)| {
        let height = if index == 0 { 4 } else { shape.preprocessed_height };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if index == 0 {
          rows[0] = input;
          rows[1] = G::ONE;
          rows[2] = G::ONE;
          rows[9] = advice;
          rows[10] = output;
        } else if index == 2 {
          rows[6] = G::from_u8(3);
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect();
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert_eq!(
      system.verify(&claim, &proof).is_ok(),
      accepted,
      "input {input}, inverse advice {advice}, output {output}"
    );
  }
}
