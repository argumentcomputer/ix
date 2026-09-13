// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

fn folded_zero_toplevel() -> Toplevel {
  with_singleton_circuits(
    vec![Function {
      body: Block {
        ops: vec![Op::Const(G::ZERO), Op::Mul(1, 0), Op::EqZero(2)],
        ctrl: Ctrl::Return(0, vec![3]),
      },
      // The compiler and witness builder retain the conservative product
      // degree 1, so EqZero reserves two auxiliary columns.
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

#[test]
fn folded_zero_product_can_be_tested_for_zero() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(folded_zero_toplevel(), cp, fp);
  for input in [G::ZERO, G::ONE, G::from_u64(17), -G::ONE] {
    let (claim, proof) = system.prove(0, &[input], &mut empty_io_buffer());
    assert_eq!(claim, vec![function_channel(), G::ZERO, input, G::ONE]);
    system.verify(&claim, &proof).unwrap();
  }
}
