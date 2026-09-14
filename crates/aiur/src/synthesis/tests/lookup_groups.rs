// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::bytecode::CallComponent;

/// f(n) = 16*n*n + f(n-1), with sixteen shared calls to g(n) = n*n.
/// Its gated lookup messages benefit from k = 2 at quotient degree 4.
fn wide_recursive_toplevel() -> Toplevel {
  let mut ops: Vec<_> =
    (0..16).map(|_| Op::Call(1, vec![0], 1, false)).collect();
  ops.extend([
    Op::Const(G::ONE),
    Op::Sub(0, 17),
    Op::Call(0, vec![18], 1, false),
  ]);
  let mut sum = 1;
  for value in 2..=16 {
    ops.push(Op::Add(sum, value));
    sum = ops.len();
  }
  ops.push(Op::Add(sum, 19));
  let root = Function {
    body: Block {
      ops: vec![],
      ctrl: Ctrl::Match(
        0,
        [(
          G::ZERO,
          Block {
            ops: vec![Op::Const(G::ZERO)],
            ctrl: Ctrl::Return(0, vec![1]),
          },
        )]
        .into_iter()
        .collect(),
        Some(Box::new(Block { ops, ctrl: Ctrl::Return(1, vec![35]) })),
      ),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 2,
      auxiliaries: 25,
      lookups: 24,
    },
    entry: true,
    constrained: true,
  };
  let leaf = Function {
    body: Block { ops: vec![Op::Mul(0, 0)], ctrl: Ctrl::Return(0, vec![1]) },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 2,
      lookups: 1,
    },
    entry: false,
    constrained: true,
  };
  let mut top = with_singleton_circuits(vec![root, leaf], vec![]);
  top.call_components = vec![
    CallComponent { order: 0, ranked: true },
    CallComponent { order: 1, ranked: false },
  ];
  top
}

fn wide_system(log_blowup: usize) -> AiurSystem {
  let (mut cp, fp) = test_parameters();
  cp.log_blowup = log_blowup;
  AiurSystem::build(wide_recursive_toplevel(), cp, fp)
}

#[test]
fn larger_lookup_groups_verify_and_roundtrip_with_the_degree_budget() {
  for (log_blowup, group, quotient, stage2) in [(1, 1, 2, 48), (2, 2, 4, 24)] {
    let system = wide_system(log_blowup);
    let circuit = &system.system.circuits[0];
    assert_eq!(circuit.lookup_group_size, group);
    assert_eq!(circuit.quotient_degree(), quotient);
    assert_eq!(circuit.stage_2_width, stage2);
    assert!(system.system.circuits.iter().all(|c| {
      c.quotient_degree() <= system.system.config.max_quotient_degree()
    }));
    // Grouping changes accumulator count, never the logical message count
    // used by the characteristic bound on lookup consumers.
    assert_eq!(system.slot_widths[0].len(), 24);
    assert_eq!(
      lookup_query_bound(
        system.slot_widths.iter().map(Vec::len),
        &[true, false, false, false],
        &[3],
      ),
      Some(1 + 24 * 8)
    );
    let bytes = crate::vk_codec::aiur_system_to_bytes(&system).unwrap();
    let (decoded, cp, fp) = crate::vk_codec::from_bytes(&bytes).unwrap();
    assert_eq!(crate::vk_codec::to_bytes(&decoded, cp, fp), bytes);
    let back = &decoded.circuits[0];
    assert_eq!(back.lookup_group_size, group);
    assert_eq!(back.max_constraint_degree, circuit.max_constraint_degree);
    assert_eq!(back.constraint_count, circuit.constraint_count);
    assert_eq!(back.stage_2_width, circuit.stage_2_width);
    for n in [0_u8, 7] {
      let (mut claim, proof) =
        system.prove(0, &[G::from_u8(n)], &mut empty_io_buffer());
      let expected: u64 = (1..=u64::from(n)).map(|i| 16 * i * i).sum();
      assert_eq!(claim.last(), Some(&G::from_u64(expected)));
      system.verify(&claim, &proof).unwrap();
      decoded.verify(&claim, &proof).unwrap();
      *claim.last_mut().unwrap() += G::ONE;
      assert!(system.verify(&claim, &proof).is_err());
      assert!(decoded.verify(&claim, &proof).is_err());
    }
  }
}

/// An opt-in wall-clock check for the quotient-work/FFT tradeoff. Timings
/// exclude construction and verification; both configurations use identical
/// bytecode, commitment parameters and query workloads. No timing assertion.
#[test]
#[ignore = "manual lookup grouping performance comparison"]
fn lookup_group_proving_timings() {
  use std::time::Instant;

  let grouped = wide_system(2);
  let mut legacy = wide_system(2);
  crate::lookup_groups::set_group(&mut legacy.system.circuits[0], 1, 2);
  for n in [7, 32_768, 131_072] {
    for round in 0..3 {
      for pick in 0..2 {
        let (name, system) = if (round + pick) % 2 == 0 {
          ("legacy", &legacy)
        } else {
          ("grouped", &grouped)
        };
        let start = Instant::now();
        let (claim, proof) =
          system.prove(0, &[G::from_u32(n)], &mut empty_io_buffer());
        let elapsed = start.elapsed();
        system.verify(&claim, &proof).unwrap();
        println!("lookup timing: n={n} round={round} {name} {elapsed:?}");
      }
    }
  }
}
