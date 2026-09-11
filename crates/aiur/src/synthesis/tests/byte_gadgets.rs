// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Export the actual fixed byte-chip rows and evaluated lookup messages for
//! the Lean component gate. No program executor is involved.

use std::{
  fs::File,
  io::{self, BufWriter, Write},
};

use super::{
  AiurSystem, Block, Ctrl, Function, FunctionLayout, Op, RowMajorMatrix,
  SystemWitness, function_channel, test_parameters, with_singleton_circuits,
};
use crate::{
  G,
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
};
use multi_stark::{
  eval::{VarValues, eval_expr},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::Matrix,
};

fn local_values(row: &[G]) -> VarValues<'_, G> {
  VarValues {
    preprocessed: [&[], &[]],
    main: [row, row],
    stage2: [&[], &[]],
    publics: &[],
    is_first_row: G::ONE,
    is_last_row: G::ZERO,
    is_transition: G::ONE,
  }
}

fn write_u64(out: &mut impl Write, value: u64) -> io::Result<()> {
  out.write_all(&value.to_le_bytes())
}

fn export<T: AiurGadget>(gadget: &T, out: &mut impl Write) -> io::Result<()> {
  let preprocessed = gadget.preprocessed().expect("fixed byte chip");
  let lookups = gadget.lookups();
  write_u64(out, preprocessed.height() as u64)?;
  write_u64(out, preprocessed.width() as u64)?;
  write_u64(out, lookups.len() as u64)?;
  for lookup in &lookups {
    write_u64(out, lookup.args.len() as u64)?;
  }
  // Distinct weights also pin the lookup-slot-to-multiplicity-column map.
  let weights: Vec<G> =
    (0..gadget.main_width()).map(|index| G::from_usize(index + 17)).collect();
  for row in preprocessed.values.chunks_exact(preprocessed.width()) {
    for value in row {
      write_u64(out, value.as_canonical_u64())?;
    }
    let values = VarValues {
      preprocessed: [row, row],
      main: [&weights, &weights],
      stage2: [&[], &[]],
      publics: &[],
      is_first_row: G::ZERO,
      is_last_row: G::ZERO,
      is_transition: G::ZERO,
    };
    for lookup in &lookups {
      write_u64(
        out,
        eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
      )?;
      for argument in &lookup.args {
        write_u64(out, eval_expr(argument, &values).as_canonical_u64())?;
      }
    }
  }
  Ok(())
}

#[test]
fn byte_gadget_snapshot() -> io::Result<()> {
  let mut out = Vec::new();
  out.write_all(b"Aiur byte gadgets v1\n")?;
  export(&Bytes1, &mut out)?;
  export(&Bytes2, &mut out)?;
  assert_eq!(out.len(), 34_664_621, "complete row and lookup inventory");
  if let Some(path) = std::env::var_os("IX_BYTE_GADGET_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  Ok(())
}

#[test]
fn emitted_virtual_byte_carries_match_all_input_pairs() {
  for addition in [true, false] {
    let op = if addition { Op::U8Add(0, 1) } else { Op::U8Sub(0, 1) };
    let top = with_singleton_circuits(
      vec![Function {
        body: Block { ops: vec![op], ctrl: Ctrl::Return(0, vec![2, 3]) },
        layout: FunctionLayout {
          input_size: 2,
          selectors: 1,
          auxiliaries: 8,
          lookups: 5,
        },
        entry: true,
        constrained: true,
      }],
      vec![],
    );
    let (constraints, lookups) = top.build_constraints(0);
    assert_eq!(constraints.width, 11);
    let mut row = vec![G::ZERO; constraints.width];
    row[2] = G::ONE;
    row[3] = G::ONE;
    for x in 0..=u8::MAX {
      for y in 0..=u8::MAX {
        let (low, carry) =
          if addition { x.overflowing_add(y) } else { x.overflowing_sub(y) };
        row[0] = G::from_u8(x);
        row[1] = G::from_u8(y);
        row[10] = G::from_u8(low);
        let values = local_values(&row);
        assert_eq!(eval_expr(&lookups[0].args[4], &values), G::from_u8(low));
        assert_eq!(
          eval_expr(&lookups[0].args[5], &values),
          G::from_bool(carry),
          "addition {addition}, x {x}, y {y}"
        );
      }
    }
  }
}

#[test]
fn supplied_u32_comparison_checks_carries_decomposition_and_range() {
  let top = with_singleton_circuits(
    vec![Function {
      body: Block {
        ops: vec![Op::U32LessThan(0, 1)],
        ctrl: Ctrl::Return(0, vec![2]),
      },
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 19,
        lookups: 10,
      },
      entry: true,
      constrained: true,
    }],
    vec![],
  );
  let (constraints, lookups) = top.build_constraints(0);
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  let honest = [
    (0u32, 0u32),
    (0, 1),
    (1, 0),
    (u32::MAX, u32::MAX),
    (u32::MAX, 0),
    (0, u32::MAX),
    (256, 255),
  ];
  // Kind 0 is honest; mutations 1, 2 and 3 isolate carry, decomposition
  // and byte-range constraints while keeping the public return message.
  let cases = honest.into_iter().map(|(x, z)| (x, z, 0)).chain([
    (0, 1, 1),
    (0, 1, 2),
    (0, 1, 3),
  ]);
  for (x, z, mutation) in cases {
    let y = z.wrapping_sub(x).wrapping_sub(1);
    let mut row = vec![G::ZERO; constraints.width];
    row[0] = G::from_u32(x);
    row[1] = G::from_u32(z);
    row[2] = G::ONE;
    row[3] = G::ONE;
    for (slot, byte) in row[10..].iter_mut().zip(
      x.to_le_bytes().into_iter().chain(y.to_le_bytes()).chain(z.to_le_bytes()),
    ) {
      *slot = G::from_u8(byte);
    }
    match mutation {
      1 => row[14] = G::ONE,
      2 => row[0] = G::from_u8(2),
      3 => row[14..18].copy_from_slice(&[
        G::from_u16(256),
        G::from_u8(255),
        G::from_u8(255),
        G::from_u8(255),
      ]),
      _ => (),
    }
    let values = local_values(&row);
    let output = eval_expr(&lookups[0].args[4], &values);
    assert_eq!(
      constraints.zeros.iter().all(|e| eval_expr(e, &values) == G::ZERO),
      mutation == 0 || mutation == 3
    );
    if mutation == 0 {
      assert_eq!(output, G::from_bool(x < z));
    } else if mutation == 2 {
      assert_eq!(output, G::ONE, "forged 2 < 1");
    } else if mutation == 3 {
      assert_eq!(output, G::ZERO, "forged 0 >= 1 with out-of-range byte");
    }
    let claim = [function_channel(), G::ZERO, row[0], row[1], output];
    let traces = system
      .circuit_shapes()
      .iter()
      .enumerate()
      .map(|(index, shape)| {
        let height = if index == 0 { 4 } else { shape.preprocessed_height };
        let mut rows = vec![G::ZERO; height * shape.main_width];
        if index == 0 {
          rows[..row.len()].copy_from_slice(&row);
        } else if index == 2 {
          rows[6] = G::from_u8(3);
          for pair in row[10..].as_chunks::<2>().0 {
            let first = pair[0].as_canonical_u64();
            let second = pair[1].as_canonical_u64();
            if first < 256 && second < 256 {
              let index = usize::try_from(first * 256 + second).unwrap();
              rows[index * shape.main_width + 6] += G::ONE;
            }
          }
        }
        RowMajorMatrix::new(rows, shape.main_width)
      })
      .collect();
    let witness = SystemWitness::from_stage_1(traces, &system.system);
    let proof = system.system.prove(&system.key, &claim, witness);
    assert_eq!(
      system.verify(&claim, &proof).is_ok(),
      mutation == 0,
      "x {x}, z {z}, mutation {mutation}"
    );
  }
}
