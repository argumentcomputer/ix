// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::bytecode::{
  Block, CallComponent, Ctrl, Function, FunctionLayout, Op, Toplevel,
};
use crate::{G, unit_counter};
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};

fn function(inputs: usize, ops: Vec<Op>, output: Vec<usize>) -> Function {
  Function {
    body: Block { ops, ctrl: Ctrl::Return(0, output) },
    layout: FunctionLayout {
      input_size: inputs,
      selectors: 1,
      auxiliaries: 32,
      lookups: 16,
    },
    entry: true,
    constrained: true,
  }
}

fn input_counter(step: G) -> Function {
  function(
    1,
    vec![Op::Const(step), Op::Add(0, 1), Op::Call(0, vec![2], 1, false)],
    vec![3],
  )
}

fn output_counter(step: G) -> Function {
  function(
    1,
    vec![Op::Call(0, vec![0], 1, false), Op::Const(step), Op::Add(1, 2)],
    vec![3],
  )
}

fn top(functions: Vec<Function>, ranks: Vec<bool>) -> Toplevel {
  Toplevel {
    functions,
    memory_sizes: vec![],
    circuits: vec![],
    call_components: ranks
      .into_iter()
      .map(|ranked| CallComponent { order: 0, ranked })
      .collect(),
  }
}

#[test]
fn accepts_both_unit_directions_on_inputs_and_outputs() {
  for step in [G::ONE, -G::ONE] {
    assert!(unit_counter::has_unit_counter(0, &input_counter(step)));
    assert!(unit_counter::has_unit_counter(0, &output_counter(step)));
    for f in [input_counter(step), output_counter(step)] {
      assert_eq!(top(vec![f], vec![false]).validate_call_components(), Ok(()));
    }
  }
}

#[test]
fn rejects_zero_nonunit_and_unconstrained_progress() {
  for step in [G::ZERO, G::TWO, -G::TWO, G::from_u32(u32::MAX)] {
    assert!(!unit_counter::has_unit_counter(0, &input_counter(step)));
    assert!(!unit_counter::has_unit_counter(0, &output_counter(step)));
    assert!(
      top(vec![input_counter(step)], vec![false])
        .validate_call_components()
        .is_err()
    );
  }
  let f = function(
    1,
    vec![
      Op::Call(0, vec![0], 1, false),
      Op::Call(0, vec![0], 1, true),
      Op::Const(G::ONE),
      Op::Add(2, 3),
    ],
    vec![4],
  );
  assert!(!unit_counter::has_unit_counter(0, &f));
}

#[test]
fn rejects_mixed_directions_and_bad_defaults() {
  for second in [-G::ONE, G::ZERO, G::TWO] {
    let mut f = input_counter(G::ONE);
    f.body = Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [(G::ZERO, input_counter(G::ONE).body)].into_iter().collect(),
        Some(Box::new(input_counter(second).body)),
      ),
    };
    assert!(!unit_counter::has_unit_counter(0, &f));
    assert!(top(vec![f], vec![false]).validate_call_components().is_err());
  }
}

#[test]
fn output_certificate_checks_every_recursive_call() {
  let f = function(
    1,
    vec![
      Op::Call(0, vec![0], 1, false),
      Op::Call(0, vec![0], 1, false),
      Op::Const(G::ONE),
      Op::Add(1, 3),
    ],
    vec![4],
  );
  assert!(!unit_counter::has_unit_counter(0, &f));
}

#[test]
fn does_not_treat_loads_or_nonlinear_terms_as_counter_equations() {
  let load = function(
    1,
    vec![
      Op::Load(3, 0),
      Op::Const(G::ONE),
      Op::Add(1, 4),
      Op::Call(0, vec![5], 1, false),
    ],
    vec![6],
  );
  let nonlinear = function(
    1,
    vec![
      Op::Mul(0, 0),
      Op::Const(G::ONE),
      Op::Add(1, 2),
      Op::Call(0, vec![3], 1, false),
    ],
    vec![4],
  );
  assert!(!unit_counter::has_unit_counter(0, &load));
  assert!(!unit_counter::has_unit_counter(0, &nonlinear));
}

#[test]
fn malformed_indices_and_result_shapes_do_not_certify() {
  let examples = [
    function(1, vec![Op::Call(0, vec![], 1, false)], vec![1]),
    function(
      1,
      vec![Op::Const(G::ONE), Op::Add(5, 1), Op::Call(0, vec![2], 1, false)],
      vec![3],
    ),
    function(
      1,
      vec![Op::Call(0, vec![0], 0, false), Op::Const(G::ONE), Op::Add(1, 0)],
      vec![2],
    ),
    function(
      1,
      vec![Op::Call(0, vec![0], 1, false), Op::Const(G::ONE), Op::Add(1, 2)],
      vec![99],
    ),
  ];
  for f in examples {
    assert!(!unit_counter::has_unit_counter(0, &f));
  }
}

#[test]
fn shared_continuations_and_excessive_depth_remain_ranked() {
  let mut f = input_counter(G::ONE);
  f.body = Block {
    ops: vec![],
    ctrl: Ctrl::MatchContinue(
      0,
      [(G::ZERO, Block { ops: vec![], ctrl: Ctrl::Yield(0, vec![0]) })]
        .into_iter()
        .collect(),
      None,
      1,
      0,
      0,
      Box::new(input_counter(G::ONE).body),
    ),
  };
  assert!(!unit_counter::has_unit_counter(0, &f));
  assert!(top(vec![f], vec![false]).validate_call_components().is_err());
  let mut f = input_counter(G::ONE);
  for _ in 0..256 {
    f.body = Block {
      ops: vec![],
      ctrl: Ctrl::Match(0, [(G::ZERO, f.body)].into_iter().collect(), None),
    };
  }
  assert!(!unit_counter::has_unit_counter(0, &f));
}

#[test]
fn unit_self_edges_do_not_authorize_mutual_unranked_cycles() {
  let mut f = input_counter(G::ONE);
  f.body.ops[2] = Op::Call(1, vec![2], 1, false);
  let g = input_counter(G::ONE);
  assert!(
    top(vec![f, g], vec![false, false]).validate_call_components().is_err()
  );
}

#[test]
fn independent_graph_oracle_preserves_all_unrecognized_edges() {
  for edges in 0u16..512 {
    for ranks in 0u8..8 {
      let functions = (0..3)
        .map(|i| {
          let ops = (0..3)
            .filter(|j| edges & (1 << (3 * i + j)) != 0)
            .map(|j| Op::Call(j, vec![0], 0, false))
            .collect();
          function(1, ops, vec![0])
        })
        .collect();
      let ranked: Vec<_> = (0..3).map(|i| ranks & (1 << i) != 0).collect();
      let expected = (0..3).all(|i| {
        (0..3)
          .all(|j| edges & (1 << (3 * i + j)) == 0 || (ranked[i] && ranked[j]))
      });
      assert_eq!(
        top(functions, ranked).validate_call_components().is_ok(),
        expected,
        "edges={edges}, ranks={ranks}"
      );
    }
  }
}

#[test]
fn affine_certificates_agree_with_concrete_field_rows_at_boundaries() {
  let constants =
    [G::ZERO, G::ONE, G::TWO, -G::ONE, -G::TWO, G::from_u64(u32::MAX.into())];
  let inputs =
    [G::ZERO, G::ONE, G::from_u8(255), G::from_u64(u32::MAX.into()), -G::ONE];
  for a in constants {
    for b in constants {
      let f = function(
        1,
        vec![
          Op::Const(a),
          Op::Add(0, 1),
          Op::Const(b),
          Op::Sub(2, 3),
          Op::Call(0, vec![4], 1, false),
        ],
        vec![5],
      );
      let expected = a - b == G::ONE || a - b == -G::ONE;
      assert_eq!(unit_counter::has_unit_counter(0, &f), expected);
      for input in inputs {
        let call_arg = (input + a) - b;
        if expected {
          assert!(
            call_arg == input + G::ONE || call_arg == input - G::ONE,
            "input={}, a={}, b={}",
            input.as_canonical_u64(),
            a.as_canonical_u64(),
            b.as_canonical_u64()
          );
        }
      }
    }
  }
}
