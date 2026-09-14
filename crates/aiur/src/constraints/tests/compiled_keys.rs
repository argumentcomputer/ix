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
  bytecode::{CallComponent, Circuit, Function, FunctionLayout},
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
  synthesis::AiurConfig,
  vk_codec,
};
use multi_stark::{
  config::StarkGenericConfig,
  p3_field::BasedVectorSpace,
  system::{CircuitInputs, System},
  types::{CommitmentParameters, ExtVal, FriParameters},
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

// Exercise the component policy inside branches, defaults and shared
// continuations, preserving the fixture's value indices and return shapes.
fn component_calls(block: &mut Block, parent: usize, cursor: &mut usize) {
  for op in &mut block.ops {
    if let Op::Call(child, _, _, unconstrained) = op {
      *unconstrained = parent == 3;
      *child = if cursor.is_multiple_of(2) {
        match parent {
          0 | 2 => 1,
          1 => 2,
          _ => 3,
        }
      } else {
        3
      };
      *cursor += 1;
    }
  }
  match &mut block.ctrl {
    Ctrl::Return(..) | Ctrl::Yield(..) => {},
    Ctrl::Match(_, cases, fallback) => {
      for branch in cases.values_mut() {
        component_calls(branch, parent, cursor);
      }
      if let Some(branch) = fallback {
        component_calls(branch, parent, cursor);
      }
    },
    Ctrl::MatchContinue(_, cases, fallback, _, _, _, continuation) => {
      for branch in cases.values_mut() {
        component_calls(branch, parent, cursor);
      }
      if let Some(branch) = fallback {
        component_calls(branch, parent, cursor);
      }
      component_calls(continuation, parent, cursor);
    },
  }
}

fn component_layout(
  function: &mut Function,
  index: usize,
  components: &[CallComponent],
) {
  let input_size = function.layout.input_size;
  let selectors = function.layout.selectors;
  let ranked = components[index].ranked;
  let mut measured = ConstraintState {
    function: index,
    call_components: components,
    function_index: G::from_usize(index),
    input_size,
    sel_base: input_size,
    column: input_size + selectors + 1 + if ranked { RANK_BYTES } else { 0 },
    lookup: 1 + if ranked { RANK_LOOKUPS } else { 0 },
    map: (0..input_size).map(|i| (var(i), 1)).collect(),
    lookups: (0..4096).map(|_| empty_lookup()).collect(),
    yield_info: vec![],
    ..state(selectors, false)
  };
  let entry = function.body.get_block_selector(&measured);
  function.body.collect_constraints(entry, &mut measured);
  assert!(measured.yield_info.is_empty());
  function.layout.auxiliaries = measured.column - input_size - selectors;
  function.layout.lookups = measured.lookup;
}

#[test]
fn compiled_key_snapshot() -> io::Result<()> {
  let groups: &[&[usize]] =
    &[&[0], &[1], &[2], &[3], &[0, 1], &[2, 0, 3], &[3, 2, 1, 0], &[]];
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 64,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let mut out = b"Aiur compiled keys v3\n".to_vec();
  write_u64(&mut out, 24)?;
  let mut assignments = 0;
  for seed in 0..24 {
    let cp = CommitmentParameters { log_blowup: 1 + seed % 3, cap_height: 0 };
    let optimized = seed >= 12;
    let call_components = if optimized {
      vec![
        CallComponent { order: 0, ranked: false },
        CallComponent { order: 1, ranked: true },
        CallComponent { order: 1, ranked: true },
        CallComponent { order: 2, ranked: false },
      ]
    } else {
      vec![]
    };
    let mut functions: Vec<_> =
      (0..4).map(|index| fixture_function(seed % 12, index)).collect();
    if optimized {
      for (index, function) in functions.iter_mut().enumerate() {
        component_calls(&mut function.body, index, &mut 0);
        component_layout(function, index, &call_components);
      }
    }
    let circuits = groups
      .iter()
      .map(|members| Circuit {
        members: members.to_vec(),
        layout: if optimized {
          members.iter().fold(
            FunctionLayout {
              input_size: 0,
              selectors: 0,
              auxiliaries: 1,
              lookups: 1,
            },
            |layout, &member| {
              let next = functions[member].layout;
              FunctionLayout {
                input_size: layout.input_size.max(next.input_size),
                selectors: layout.selectors + next.selectors,
                auxiliaries: layout.auxiliaries.max(next.auxiliaries),
                lookups: layout.lookups.max(next.lookups),
              }
            },
          )
        } else {
          circuit_layout(&functions, members)
        },
      })
      .collect();
    let top = Toplevel {
      functions,
      circuits,
      memory_sizes: vec![0, 1, 2, 4, 8],
      call_components,
    };
    assert!(top.validate_call_components().is_ok());
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
    write_u64(&mut out, top.call_components.len() as u64)?;
    for component in &top.call_components {
      write_u64(&mut out, component.order as u64)?;
      out.push(u8::from(component.ranked));
    }
    let inputs = inputs(&top);
    let expressions: Vec<_> = inputs
      .iter()
      .map(|input| (input.constraints.clone(), input.lookups.clone()))
      .collect();
    let mut system = System::new(AiurConfig::new(cp, fp), inputs).0;
    let blowup = system.config.max_quotient_degree();
    for circuit in &mut system.circuits {
      crate::lookup_groups::retune(
        circuit,
        blowup,
        <ExtVal as BasedVectorSpace<G>>::DIMENSION,
      );
    }
    let bytes1 = &system.circuits[system.circuits.len() - 2];
    assert_eq!(bytes1.preprocessed_height, 256);
    assert_eq!(bytes1.lookup_group_size, 1);
    assert_eq!(bytes1.quotient_degree(), 1);
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
  assert_eq!(assignments, 1440);
  if let Some(path) = std::env::var_os("IX_COMPILED_KEY_SNAPSHOT") {
    let mut file = BufWriter::new(File::create(path)?);
    file.write_all(&out)?;
    file.flush()?;
  }
  eprintln!(
    "compiled keys: 24 systems (12 component layouts), 360 circuits, {assignments} assignments"
  );
  Ok(())
}
