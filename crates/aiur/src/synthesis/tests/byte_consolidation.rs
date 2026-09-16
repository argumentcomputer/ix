// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::{
  execute::{
    QueryRecord, bytes2_and_value, bytes2_less_than_value, bytes2_or_value,
  },
  gadgets::bytes2::Bytes2Op,
};
use multi_stark::eval::{VarValues, eval_expr};

fn byte_toplevel(grouped: bool) -> Toplevel {
  let functions = [Op::U8And(0, 1), Op::U8Or(0, 1), Op::U8LessThan(0, 1)]
    .into_iter()
    .map(|op| Function {
      body: Block { ops: vec![op], ctrl: Ctrl::Return(0, vec![2]) },
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 2,
        lookups: 2,
      },
      entry: true,
      constrained: true,
    })
    .collect();
  let mut top = with_singleton_circuits(functions, vec![]);
  if grouped {
    top.circuits = vec![crate::bytecode::Circuit {
      members: vec![0, 1, 2],
      layout: FunctionLayout {
        input_size: 2,
        selectors: 3,
        auxiliaries: 2,
        lookups: 2,
      },
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

fn message(lookup: &Lookup<Expr<G>>, row: &[G], preprocessed: &[G]) -> Vec<G> {
  let vars = values(row, preprocessed);
  lookup.args.iter().map(|arg| eval_expr(arg, &vars)).collect()
}

#[test]
fn every_byte_pair_matches_the_consolidated_compiled_lookup() {
  let table = Bytes2.preprocessed().unwrap();
  let pulls = Bytes2.lookups();
  let table_row = [G::ZERO; 8];
  assert_eq!(table.width, 11);
  assert_eq!(pulls.len(), 8);

  for grouped in [false, true] {
    let top = byte_toplevel(grouped);
    for member in 0..3 {
      let circuit = if grouped { 0 } else { member };
      let layout = top.circuits[circuit].layout;
      let (constraints, lookups) = top.build_constraints(circuit);
      let pull = if member == 2 { 2 } else { 0 };
      assert_eq!(lookups.len(), 2);
      assert_eq!(constraints.width, 2 + layout.selectors + 2);
      let mut row = vec![G::ZERO; constraints.width];
      row[2 + if grouped { member } else { 0 }] = G::ONE;
      row[2 + layout.selectors] = G::ONE;
      let output_column = 3 + layout.selectors;
      for a in 0..=u8::MAX {
        for b in 0..=u8::MAX {
          let expected = match member {
            0 => G::from_u8(a & b),
            1 => G::from_u8(a | b),
            _ => G::from_bool(a < b),
          };
          row[0] = G::from_u8(a);
          row[1] = G::from_u8(b);
          row[output_column] = expected;
          let preprocessed = &table.values
            [(usize::from(a) * 256 + usize::from(b)) * table.width..]
            [..table.width];
          let provider = message(&pulls[pull], &table_row, preprocessed);
          assert_eq!(message(&lookups[1], &row, &[]), provider);
          assert!(
            constraints
              .zeros
              .iter()
              .all(|c| { eval_expr(c, &values(&row, &[])) == G::ZERO })
          );
          // Test the actual field equations against out-of-range and wrong
          // results, not just host-byte arithmetic. Nonzero coefficients
          // make the correct result the unique solution in the field.
          for wrong in [-G::ONE, G::from_u16(256), expected + G::ONE] {
            row[output_column] = wrong;
            assert_ne!(message(&lookups[1], &row, &[]), provider);
          }
        }
      }
      // Inactive rows, including grouped members, send no requests even
      // when their unused inputs/output contain arbitrary field values.
      row.fill(-G::ONE);
      row[2..3 + layout.selectors].fill(G::ZERO);
      assert!(
        constraints
          .zeros
          .iter()
          .all(|c| { eval_expr(c, &values(&row, &[])) == G::ZERO })
      );
      assert!(lookups.iter().all(|lookup| {
        eval_expr(&lookup.multiplicity, &values(&row, &[])) == G::ZERO
      }));
    }
  }
}

#[test]
fn interpreter_and_generated_helpers_share_table_multiplicities() {
  let top = byte_toplevel(false);
  let mut interpreted = QueryRecord::new(&top);
  let mut generated = QueryRecord::new(&top);
  for a in 0..=u8::MAX {
    for b in 0..=u8::MAX {
      let x = G::from_u8(a);
      let y = G::from_u8(b);
      let expected =
        [G::from_u8(a & b), G::from_u8(a | b), G::from_bool(a < b)];
      let got = [
        bytes2_and_value(x, y, &mut generated),
        bytes2_or_value(x, y, &mut generated),
        bytes2_less_than_value(x, y, &mut generated),
      ];
      assert_eq!(got, expected);
      for (op, expected) in
        [Bytes2Op::And, Bytes2Op::Or, Bytes2Op::LessThan].iter().zip(expected)
      {
        assert_eq!(Bytes2.execute(op, &[x, y], &mut interpreted), [expected]);
      }
    }
  }
  let widths: Vec<_> = Bytes2.lookups().iter().map(|l| l.args.len()).collect();
  let (a, _) = Bytes2.witness_data(&interpreted, &widths);
  let (b, _) = Bytes2.witness_data(&generated, &widths);
  assert_eq!(a.values, b.values);
  for row in a.values.chunks_exact(a.width) {
    assert_eq!(
      row,
      [G::TWO, G::ZERO, G::ONE, G::ZERO, G::ZERO, G::ZERO, G::ZERO, G::ZERO]
    );
  }
}

#[test]
fn consolidated_byte_proofs_verify_in_both_partitions_and_key_codec() {
  for grouped in [false, true] {
    let (mut cp, fp) = test_parameters();
    cp.log_blowup = 2;
    let system = AiurSystem::build(byte_toplevel(grouped), cp, fp);
    let shape = system.circuit_shapes().pop().unwrap();
    assert_eq!(
      (
        shape.main_width,
        shape.stage2_width,
        shape.quotient_degree,
        shape.preprocessed_width,
        shape.preprocessed_height
      ),
      (8, 8, 2, 11, 65_536)
    );
    let bytes = crate::vk_codec::aiur_system_to_bytes(&system).unwrap();
    let (decoded, _, _) = crate::vk_codec::from_bytes(&bytes).unwrap();
    for member in 0..3 {
      for (a, b) in [(0xd3_u8, 0x69_u8), (0, 255)] {
        let input = [G::from_u8(a), G::from_u8(b)];
        let expected = match member {
          0 => G::from_u8(a & b),
          1 => G::from_u8(a | b),
          _ => G::from_bool(a < b),
        };
        let (claim, proof) =
          system.prove(member, &input, &mut empty_io_buffer());
        assert_eq!(claim.last(), Some(&expected));
        system.verify(&claim, &proof).unwrap();
        decoded.verify(&claim, &proof).unwrap();
      }
    }
  }
}

/// Supply the stage-one trace directly after changing the claimed output
/// or a byte input. Local constraints still hold; the fixed lookup table
/// must reject the false relation, including through grouped selectors.
#[test]
fn forged_consolidated_outputs_and_nonbyte_inputs_fail_lookup_verification() {
  for grouped in [false, true] {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(byte_toplevel(grouped), cp, fp);
    let input = [G::from_u8(3), G::from_u8(5)];
    for member in 0..3 {
      let circuit = if grouped { 0 } else { member };
      let layout = system.toplevel.circuits[circuit].layout;
      let (record, output) = system
        .toplevel
        .execute(member, input.to_vec(), &mut empty_io_buffer())
        .unwrap();
      let mut original = Vec::new();
      for i in 0..system.toplevel.circuits.len() {
        let (trace, _) = system.toplevel.witness_data(
          i,
          &record,
          &empty_io_buffer(),
          &system.slot_arg_widths(i),
        );
        original.push(trace);
      }
      original.push(
        Bytes1.witness_data(&record, &system.slot_arg_widths(original.len())).0,
      );
      original.push(
        Bytes2.witness_data(&record, &system.slot_arg_widths(original.len())).0,
      );
      let (constraints, _) = system.toplevel.build_constraints(circuit);
      for (column, claimed_input, claimed_output) in [
        (3 + layout.selectors, input, -G::ONE),
        (0, [G::from_u16(256), input[1]], output[0]),
      ] {
        let mut traces = original.clone();
        traces[circuit].values[column] =
          if column == 0 { claimed_input[0] } else { claimed_output };
        let row = &traces[circuit].values[..layout.width()];
        assert!(
          constraints
            .zeros
            .iter()
            .all(|c| { eval_expr(c, &values(row, &[])) == G::ZERO })
        );
        let claim = vec![
          function_channel(),
          G::from_usize(member),
          claimed_input[0],
          claimed_input[1],
          claimed_output,
        ];
        let witness = SystemWitness::from_stage_1(traces, &system.system);
        let proof = system.system.prove(&system.key, &claim, witness);
        assert!(system.verify(&claim, &proof).is_err());
      }
    }
  }
}

#[test]
fn original_and_consolidated_operations_share_multiplicities_in_one_proof() {
  let function = Function {
    body: Block {
      ops: vec![
        Op::U8And(0, 1),
        Op::U8Or(0, 1),
        Op::U8LessThan(0, 1),
        Op::U8Xor(0, 1),
        Op::U8Sub(0, 1),
      ],
      ctrl: Ctrl::Return(0, vec![2, 3, 4, 5, 6, 7]),
    },
    layout: FunctionLayout {
      input_size: 2,
      selectors: 1,
      auxiliaries: 6,
      lookups: 6,
    },
    entry: true,
    constrained: true,
  };
  let top = with_singleton_circuits(vec![function], vec![]);
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  for (a, b) in [(0_u8, 255_u8), (255, 0), (0xd3, 0x69), (255, 255)] {
    let input = [G::from_u8(a), G::from_u8(b)];
    let mut io = empty_io_buffer();
    let (record, output) =
      system.toplevel.execute(0, input.to_vec(), &mut io).unwrap();
    let (sub, borrow) = a.overflowing_sub(b);
    assert_eq!(
      output,
      [
        G::from_u8(a & b),
        G::from_u8(a | b),
        G::from_bool(a < b),
        G::from_u8(a ^ b),
        G::from_u8(sub),
        G::from_bool(borrow),
      ]
    );
    let (table, _) = Bytes2.witness_data(&record, &system.slot_arg_widths(2));
    let row = &table.values
      [(usize::from(a) * 256 + usize::from(b)) * table.width..][..table.width];
    assert_eq!(
      row,
      [
        G::from_u8(3),
        G::ZERO,
        G::TWO,
        G::ZERO,
        G::ZERO,
        G::ZERO,
        G::ZERO,
        G::ZERO
      ]
    );
    let (claim, proof) =
      system.prove_from_execution(0, &input, &io, record, &output);
    system.verify(&claim, &proof).unwrap();
  }
}
