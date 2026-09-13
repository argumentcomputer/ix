// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Native key construction from transported function fixtures, memories and
//! both byte tables. Include all native matrix families in the assignments.

use super::{
  block_expressions::write_block,
  circuit_expressions::write_layout,
  circuit_rows::{circuit_layout, fixture_function},
  operation_expressions::write_indices,
  *,
};
use crate::{
  bytecode::Circuit,
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
  synthesis::AiurConfig,
  vk_codec,
};
use multi_stark::{
  system::{CircuitInputs, System},
  types::{CommitmentParameters, FriParameters},
};

fn inputs(top: &Toplevel) -> Vec<CircuitInputs<G>> {
  let mut result = Vec::new();
  for (index, _) in top.circuits.iter().enumerate() {
    let (constraints, lookups) = top.build_constraints(index);
    let lookup_group_size =
      if top.circuit_is_branchless(index) && lookups.len() >= 2 {
        2
      } else {
        1
      };
    result.push(CircuitInputs {
      main_width: constraints.width,
      constraints: constraints.zeros,
      lookups,
      lookup_group_size,
      ..CircuitInputs::default()
    });
  }
  for &width in &top.memory_sizes {
    let (memory, constraints, lookups) = Memory::build(width);
    result.push(CircuitInputs {
      main_width: memory.width,
      constraints,
      lookups,
      lookup_group_size: 1,
      ..CircuitInputs::default()
    });
  }
  result.extend([
    CircuitInputs {
      main_width: Bytes1.main_width(),
      preprocessed: Bytes1.preprocessed(),
      lookups: Bytes1.lookups(),
      lookup_group_size: 2,
      ..CircuitInputs::default()
    },
    CircuitInputs {
      main_width: Bytes2.main_width(),
      preprocessed: Bytes2.preprocessed(),
      lookups: Bytes2.lookups(),
      lookup_group_size: 2,
      ..CircuitInputs::default()
    },
  ]);
  result
}

fn columns(width: usize, seed: usize, family: usize) -> Vec<G> {
  (0..width)
    .map(|index| match seed {
      0 => G::ZERO,
      1 => G::ONE,
      2 => -G::ONE,
      _ => G::from_usize(17 + family * 31 + index * 13),
    })
    .collect()
}

#[test]
fn compiled_key_snapshot() -> io::Result<()> {
  let groups: &[&[usize]] =
    &[&[0], &[1], &[2], &[3], &[0, 1], &[2, 0, 3], &[3, 2, 1, 0], &[]];
  let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 64,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let mut out = b"Aiur compiled keys v1\n".to_vec();
  write_u64(&mut out, 12)?;
  let mut assignments = 0;
  for seed in 0..12 {
    let functions: Vec<_> =
      (0..4).map(|index| fixture_function(seed, index)).collect();
    let circuits = groups
      .iter()
      .map(|members| Circuit {
        members: members.to_vec(),
        layout: circuit_layout(&functions, members),
      })
      .collect();
    let top =
      Toplevel { functions, circuits, memory_sizes: vec![0, 1, 2, 4, 8] };
    write_u64(&mut out, top.functions.len() as u64)?;
    for function in &top.functions {
      write_block(&mut out, &function.body)?;
      write_layout(&mut out, function.layout)?;
      out.extend([u8::from(function.entry), u8::from(function.constrained)]);
    }
    write_u64(&mut out, top.circuits.len() as u64)?;
    for circuit in &top.circuits {
      write_indices(&mut out, &circuit.members)?;
      write_layout(&mut out, circuit.layout)?;
    }
    write_indices(&mut out, &top.memory_sizes)?;
    let inputs = inputs(&top);
    let expressions: Vec<_> = inputs
      .iter()
      .map(|input| (input.constraints.clone(), input.lookups.clone()))
      .collect();
    let system = System::new(AiurConfig::new(cp, fp), inputs).0;
    let key = vk_codec::to_bytes(&system, cp, fp);
    write_u64(&mut out, key.len() as u64)?;
    out.extend(key);
    assert_eq!(system.circuits.len(), 15);
    for (circuit, (constraints, lookups)) in
      system.circuits.iter().zip(expressions)
    {
      write_u64(&mut out, 4)?;
      for pattern in 0..4 {
        let pre = columns(circuit.preprocessed_width, pattern, 0);
        let pre_next = columns(circuit.preprocessed_width, pattern, 1);
        let main = columns(circuit.main_width, pattern, 2);
        let main_next = columns(circuit.main_width, pattern, 3);
        let stage2 = columns(circuit.stage_2_width, pattern, 4);
        let stage2_next = columns(circuit.stage_2_width, pattern, 5);
        let publics = columns(circuit.num_publics, pattern, 6);
        for cols in
          [&pre, &pre_next, &main, &main_next, &stage2, &stage2_next, &publics]
        {
          write_values(&mut out, cols)?;
        }
        let selectors = columns(3, pattern, 7);
        for selector in &selectors {
          write_u64(&mut out, selector.as_canonical_u64())?;
        }
        let values = VarValues {
          preprocessed: [&pre, &pre_next],
          main: [&main, &main_next],
          stage2: [&stage2, &stage2_next],
          publics: &publics,
          is_first_row: selectors[0],
          is_last_row: selectors[1],
          is_transition: selectors[2],
        };
        write_values(
          &mut out,
          &constraints
            .iter()
            .map(|expr| eval_expr(expr, &values))
            .collect::<Vec<_>>(),
        )?;
        write_u64(&mut out, lookups.len() as u64)?;
        for lookup in &lookups {
          write_u64(
            &mut out,
            eval_expr(&lookup.multiplicity, &values).as_canonical_u64(),
          )?;
          write_values(
            &mut out,
            &lookup
              .args
              .iter()
              .map(|expr| eval_expr(expr, &values))
              .collect::<Vec<_>>(),
          )?;
        }
        assignments += 1;
      }
    }
  }
  assert_eq!(assignments, 720);
  if let Some(path) = std::env::var_os("IX_COMPILED_KEY_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "compiled keys: 12 systems, 180 circuits, {assignments} assignments"
  );
  Ok(())
}
