// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::bytecode::{CallComponent, Circuit};
use multi_stark::{
  eval::{VarValues, eval_expr},
  p3_field::PrimeField64,
};

fn comparison_toplevel(grouped: bool, ranked: bool) -> Toplevel {
  let layout = FunctionLayout {
    input_size: 2,
    selectors: 1,
    auxiliaries: 7 + if ranked { 3 } else { 0 },
    lookups: 7 + if ranked { 3 } else { 0 },
  };
  let functions = (0..2)
    .map(|_| Function {
      body: Block {
        ops: vec![Op::U32LessThan(0, 1)],
        ctrl: Ctrl::Return(0, vec![2]),
      },
      layout,
      entry: true,
      constrained: true,
    })
    .collect();
  let mut top = with_singleton_circuits(functions, vec![]);
  if !ranked {
    top.call_components =
      (0..2).map(|order| CallComponent { order, ranked: false }).collect();
  }
  if grouped {
    top.circuits = vec![Circuit {
      members: vec![0, 1],
      layout: FunctionLayout { selectors: 2, ..layout },
    }];
  }
  top
}

fn values<'a>(row: &'a [G], preprocessed: &'a [G]) -> VarValues<'a, G> {
  VarValues {
    preprocessed: [preprocessed, preprocessed],
    main: [row, row],
    stage2: [&[], &[]],
    publics: &[],
    is_first_row: G::ONE,
    is_last_row: G::ZERO,
    is_transition: G::ONE,
  }
}

fn message(lookup: &Lookup<Expr<G>>, row: &[G], pre: &[G]) -> Vec<G> {
  let vars = values(row, pre);
  lookup.args.iter().map(|arg| eval_expr(arg, &vars)).collect()
}

fn honest_row(
  layout: FunctionLayout,
  selector: usize,
  ranked: bool,
  a: u32,
  b: u32,
) -> Vec<G> {
  let mut row = vec![G::ZERO; layout.width()];
  row[0] = G::from_u32(a);
  row[1] = G::from_u32(b);
  row[2 + selector] = G::ONE;
  let aux = 2 + layout.selectors;
  row[aux] = G::ONE;
  let start = aux + 1 + if ranked { 3 } else { 0 };
  let c = b.wrapping_sub(a).wrapping_sub(1);
  for (i, word) in [a, c, b].into_iter().enumerate() {
    row[start + 2 * i] = G::from_u16((word & 0xffff) as u16);
    row[start + 2 * i + 1] = G::from_u16((word >> 16) as u16);
  }
  row
}

#[test]
fn u32_compare_all_six_limbs_match_the_scalar_table_in_both_partitions() {
  let table = Bytes2.preprocessed().unwrap();
  let providers = Bytes2.lookups();
  let table_row = [G::ZERO; 8];
  for grouped in [false, true] {
    let top = comparison_toplevel(grouped, false);
    for member in 0..2 {
      let circuit = if grouped { 0 } else { member };
      let layout = top.circuits[circuit].layout;
      let (constraints, requests) = top.build_constraints(circuit);
      assert_eq!(requests.len(), 7);
      assert_eq!(constraints.width, 9 + layout.selectors);
      let start = 3 + layout.selectors;
      let mut row =
        honest_row(layout, if grouped { member } else { 0 }, false, 0, 0);
      for value in 0..=u16::MAX {
        let field = G::from_u16(value);
        row[start..start + 6].fill(field);
        let pre =
          &table.values[usize::from(value) * table.width..][..table.width];
        let provider =
          message(&providers[Bytes2::U16_RANGE_CHECK_COLUMN], &table_row, pre);
        assert_eq!(provider, [crate::u16_range_check_channel(), field]);
        for request in &requests[1..] {
          assert_eq!(message(request, &row, &[]), provider);
          assert_eq!(
            eval_expr(&request.multiplicity, &values(&row, &[])),
            G::ONE
          );
        }
      }
      for limb in 0..6 {
        for bad in [-G::ONE, G::from_u32(65536), G::from_u64(1 << 32)] {
          row[start + limb] = bad;
          assert_eq!(
            message(&requests[1 + limb], &row, &[]),
            [crate::u16_range_check_channel(), bad]
          );
          assert!(bad.as_canonical_u64() > u64::from(u16::MAX));
        }
      }
    }
  }
}

#[test]
fn u32_compare_constraints_preserve_strictness_bounds_and_inactive_gates() {
  let boundary = [
    0_u32,
    1,
    255,
    256,
    65535,
    65536,
    65537,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_0000,
    0xffff_fffe,
    u32::MAX,
  ];
  for ranked in [false, true] {
    for grouped in [false, true] {
      let top = comparison_toplevel(grouped, ranked);
      for member in 0..2 {
        let circuit = if grouped { 0 } else { member };
        let layout = top.circuits[circuit].layout;
        let (constraints, requests) = top.build_constraints(circuit);
        for a in boundary {
          for b in boundary {
            let row = honest_row(
              layout,
              if grouped { member } else { 0 },
              ranked,
              a,
              b,
            );
            assert!(
              constraints
                .zeros
                .iter()
                .all(|c| eval_expr(c, &values(&row, &[])) == G::ZERO)
            );
            assert_eq!(
              message(&requests[0], &row, &[])[4],
              G::from_bool(a < b)
            );
            // Every decomposition column participates in the compiled
            // equations; wrong in-range advice cannot change the result.
            let start = 3 + layout.selectors + if ranked { 3 } else { 0 };
            for limb in 0..6 {
              let mut changed = row.clone();
              changed[start + limb] += G::ONE;
              assert!(
                constraints
                  .zeros
                  .iter()
                  .any(|c| eval_expr(c, &values(&changed, &[])) != G::ZERO)
              );
            }
            for input in 0..2 {
              let mut changed = row.clone();
              changed[input] += G::from_u64(1 << 32);
              assert!(
                constraints
                  .zeros
                  .iter()
                  .any(|c| eval_expr(c, &values(&changed, &[])) != G::ZERO)
              );
            }
          }
        }
        let mut inactive = vec![-G::ONE; layout.width()];
        inactive[2..3 + layout.selectors].fill(G::ZERO);
        assert!(
          constraints
            .zeros
            .iter()
            .all(|c| eval_expr(c, &values(&inactive, &[])) == G::ZERO)
        );
        assert!(requests.iter().all(|request| eval_expr(
          &request.multiplicity,
          &values(&inactive, &[])
        ) == G::ZERO));
      }
    }
  }
}

#[test]
fn u32_compare_proofs_and_decoded_keys_cover_boundaries_and_rank_modes() {
  for ranked in [false, true] {
    for grouped in [false, true] {
      let (mut cp, fp) = test_parameters();
      cp.log_blowup = 2;
      let system =
        AiurSystem::build(comparison_toplevel(grouped, ranked), cp, fp);
      let encoded = crate::vk_codec::aiur_system_to_bytes(&system).unwrap();
      let (decoded, _, _) = crate::vk_codec::from_bytes(&encoded).unwrap();
      for member in 0..2 {
        for (a, b) in
          [(0, u32::MAX), (u32::MAX, 0), (65535, 65536), (u32::MAX, u32::MAX)]
        {
          let input = [G::from_u32(a), G::from_u32(b)];
          let (record, output) = system
            .toplevel
            .execute(member, input.to_vec(), &mut empty_io_buffer())
            .unwrap();
          assert_eq!(output, [G::from_bool(a < b)]);
          let byte_circuit = system.toplevel.circuits.len() + 1;
          let (table, _) =
            Bytes2.witness_data(&record, &system.slot_arg_widths(byte_circuit));
          let mut expected = vec![G::ZERO; 65_536];
          for word in [a, b.wrapping_sub(a).wrapping_sub(1), b] {
            expected[usize::from((word & 0xffff) as u16)] += G::ONE;
            expected[usize::from((word >> 16) as u16)] += G::ONE;
          }
          for (row, count) in
            table.values.chunks_exact(table.width).zip(expected)
          {
            assert_eq!(row[Bytes2::U16_RANGE_CHECK_COLUMN], count);
            assert!(
              row[..Bytes2::U16_RANGE_CHECK_COLUMN]
                .iter()
                .all(|x| *x == G::ZERO)
            );
          }
          let (claim, proof) =
            system.prove(member, &input, &mut empty_io_buffer());
          assert_eq!(claim.last(), Some(&G::from_bool(a < b)));
          system.verify(&claim, &proof).unwrap();
          decoded.verify(&claim, &proof).unwrap();
          let mut false_claim = claim.clone();
          *false_claim.last_mut().unwrap() = G::from_bool(a >= b);
          assert!(system.verify(&false_claim, &proof).is_err());
        }
        for bad in [G::from_u64(1 << 32), -G::ONE] {
          for input in [[bad, G::ZERO], [G::ZERO, bad]] {
            assert!(matches!(
              system.toplevel.execute(
                member,
                input.to_vec(),
                &mut empty_io_buffer()
              ),
              Err(ExecError::U32OutOfRange(_))
            ));
          }
        }
      }
    }
  }
}

#[test]
fn u32_compare_supplied_out_of_range_limbs_fail_lookup_verification() {
  // These witnesses satisfy every local polynomial, including both carry
  // bits. Each missing u16 bound would admit an invalid input or a false
  // comparison of valid inputs. Supply them directly to bypass execution.
  let cases = [
    (1_u64 << 32, 1_u64, [0_i64, 65536, 0, 0, 1, 0], false),
    (0, 1_u64 << 32, [0, 0, 65535, 65535, 0, 65536], true),
    (1, 2, [1, 0, 0, 65536, 2, 0], false),
    (0, 0, [0, 0, 65535, -1, 0, 0], true),
  ];
  for grouped in [false, true] {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(comparison_toplevel(grouped, false), cp, fp);
    let member = 1;
    let selected = if grouped { 0 } else { member };
    let layout = system.toplevel.circuits[selected].layout;
    let (constraints, requests) = system.toplevel.build_constraints(selected);
    for (a, b, limbs, output) in cases {
      let mut traces = Vec::new();
      for (index, shape) in system.circuit_shapes().iter().enumerate() {
        let height = if shape.preprocessed_height == 0 {
          4
        } else {
          shape.preprocessed_height
        };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if index == selected {
          rows[0] = G::from_u64(a);
          rows[1] = G::from_u64(b);
          rows[2 + if grouped { member } else { 0 }] = G::ONE;
          rows[2 + layout.selectors] = G::ONE;
          for (i, limb) in limbs.into_iter().enumerate() {
            rows[3 + layout.selectors + i] = if limb < 0 {
              -G::ONE
            } else {
              G::from_u64(u64::try_from(limb).unwrap())
            };
          }
          let row = &rows[..shape.main_width];
          assert!(
            constraints
              .zeros
              .iter()
              .all(|c| eval_expr(c, &values(row, &[])) == G::ZERO)
          );
          assert_eq!(message(&requests[0], row, &[])[4], G::from_bool(output));
        } else if index == system.toplevel.circuits.len() + 1 {
          for limb in limbs {
            if let Ok(value) = u16::try_from(limb) {
              rows[usize::from(value) * shape.main_width
                + Bytes2::U16_RANGE_CHECK_COLUMN] += G::ONE;
            }
          }
        }
        traces.push(RowMajorMatrix::new(rows, shape.main_width));
      }
      let claim = [
        function_channel(),
        G::from_usize(member),
        G::from_u64(a),
        G::from_u64(b),
        G::from_bool(output),
      ];
      let witness = SystemWitness::from_stage_1(traces, &system.system);
      let proof = system.system.prove(&system.key, &claim, witness);
      assert!(system.verify(&claim, &proof).is_err());
    }
  }
}

#[test]
fn u32_compare_advice_promotion_records_scalar_queries_once() {
  for grouped in [false, true] {
    let mut top = comparison_toplevel(grouped, false);
    top.functions[0].body = Block {
      ops: vec![
        Op::Call(1, vec![0, 1], 1, true),
        Op::Call(1, vec![0, 1], 1, false),
        Op::AssertEq(vec![2], vec![3], None),
      ],
      ctrl: Ctrl::Return(0, vec![3]),
    };
    top.functions[0].layout.auxiliaries = 3;
    top.functions[0].layout.lookups = 2;
    if !grouped {
      top.circuits[0].layout = top.functions[0].layout;
    }
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(top, cp, fp);
    for input in [[G::from_u32(65535), G::from_u32(65536)], [G::ZERO, G::ZERO]]
    {
      let (record, output) = system
        .toplevel
        .execute(0, input.to_vec(), &mut empty_io_buffer())
        .unwrap();
      assert_eq!(
        output,
        [G::from_bool(
          input[0].as_canonical_u64() < input[1].as_canonical_u64()
        )]
      );
      assert_eq!(record.function_queries[1].len(), 1);
      let table_circuit = system.toplevel.circuits.len() + 1;
      let (table, _) =
        Bytes2.witness_data(&record, &system.slot_arg_widths(table_circuit));
      let count: G = table
        .values
        .chunks_exact(table.width)
        .map(|row| row[Bytes2::U16_RANGE_CHECK_COLUMN])
        .sum();
      assert_eq!(count, G::from_u8(6));
      for row in table.values.chunks_exact(table.width) {
        assert!(
          row[..Bytes2::U16_RANGE_CHECK_COLUMN]
            .iter()
            .all(|value| *value == G::ZERO)
        );
      }
      let (claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
      assert_eq!(claim.last(), output.first());
      system.verify(&claim, &proof).unwrap();
    }
  }
}
