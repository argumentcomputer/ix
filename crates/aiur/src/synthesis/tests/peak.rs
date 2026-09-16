// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::bytecode::Circuit;

fn grouped_system() -> AiurSystem {
  let layout =
    FunctionLayout { input_size: 1, selectors: 1, auxiliaries: 1, lookups: 1 };
  let functions = (0..3)
    .map(|_| Function {
      body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) },
      layout,
      entry: true,
      constrained: true,
    })
    .collect();
  let top = Toplevel {
    functions,
    memory_sizes: vec![1],
    circuits: vec![
      Circuit {
        members: vec![2, 0],
        layout: FunctionLayout { selectors: 2, ..layout },
      },
      Circuit { members: vec![1], layout },
    ],
  };
  let (cp, fp) = test_parameters();
  AiurSystem::build(top, cp, fp)
}

fn grouped_record(top: &Toplevel) -> QueryRecord {
  let mut record = QueryRecord::new(top);
  for (i, rows) in [2, 3, 5].into_iter().enumerate() {
    for row in 0..rows {
      let value = G::from_usize(10 * i + row);
      // An advice-only entry in the middle must not shift query indices
      // or selectors of the surrounding active rows.
      let mult = G::from_bool(i != 2 || row != 1);
      record.function_queries[i].insert(&[value], &[value], mult);
    }
  }
  record.memory_queries.get_mut(&1).unwrap().insert(
    &[G::ONE],
    &[G::ZERO],
    G::ONE,
  );
  record
}

#[test]
fn grouped_peak_counts_members_before_splitting_and_keeps_gadget_heights() {
  let system = grouped_system();
  let record = grouped_record(&system.toplevel);
  let types = system.circuit_types();
  for (parts, expected) in
    [(1, vec![7, 3, 1, 256, 65_536]), (4, vec![2, 1, 1, 256, 65_536])]
  {
    let counts: Vec<_> = types
      .iter()
      .enumerate()
      .map(|(i, ct)| raw_of(&system.toplevel, &record, parts)(i, ct))
      .collect();
    assert_eq!(counts, expected);
  }
  let expected = system.peak_prove_bytes_by(
    |i, _| [7, 3, 1, 256, 65_536][i],
    crate::execute::record_retained_bytes(&record),
  );
  assert_eq!(system.peak_prove_bytes(&record).peak, expected.peak);
  assert_eq!(system.suggested_split_parts(&record, expected.peak), 1);
  let half_peak = system.peak_prove_bytes_by(
    |i, _| [4, 2, 1, 256, 65_536][i],
    crate::execute::record_retained_bytes(&record) / 2,
  );
  assert!(half_peak.peak < expected.peak);
  assert_eq!(system.suggested_split_parts(&record, half_peak.peak), 2);
}

#[test]
fn peak_uses_extension_storage_even_when_accumulators_are_grouped() {
  let system = grouped_system();
  let peak = system.peak_prove_bytes_by(|_, _| 8, 0);
  let circuits = &system.system.circuits;
  assert!(circuits.iter().any(|c| c.lookup_group_size > 1));
  // Sum actual payload types: messages and their inverse copy are extension
  // values regardless of how many accumulator columns are committed.
  let expected: usize = circuits
    .iter()
    .zip(&system.slot_widths)
    .map(|(c, widths)| {
      2 * 8 * c.main_width * size_of::<G>()
        + 8 * (c.num_lookups + widths.iter().sum::<usize>()) * size_of::<G>()
        + 2 * 8 * c.num_lookups * size_of::<ExtVal>()
        + 8 * c.stage_2_width * size_of::<G>()
    })
    .sum();
  assert_eq!(peak.phase_stage2, expected + 2 * 32 * 16);
  // FRI retains base-coordinate LDEs plus extension-valued quotients.
  let committed: usize = circuits
    .iter()
    .map(|c| {
      16 * ((c.main_width + c.stage_2_width) * size_of::<G>()
        + c.quotient_degree() * size_of::<ExtVal>())
    })
    .sum();
  assert_eq!(
    peak.phase_open,
    committed + 3 * 2 * 32 * 16 + (2 * 8 + 2 * 32) * 16 * 2 + 11 * 8 * 16
  );
}

#[test]
fn grouped_witness_skips_advice_without_shifting_members() {
  let system = grouped_system();
  let record = grouped_record(&system.toplevel);
  let (trace, _) = system.toplevel.witness_data(
    0,
    &record,
    &empty_io_buffer(),
    &system.slot_widths[0],
  );
  assert_eq!(trace.values.len(), 8 * trace.width);
  for (row, (member, query)) in
    [(2, 0), (2, 2), (2, 3), (2, 4), (0, 0), (0, 1)].into_iter().enumerate()
  {
    let values = &trace.values[row * trace.width..(row + 1) * trace.width];
    assert_eq!(values[0], G::from_usize(10 * member + query));
    assert_eq!(
      &values[1..3],
      &[G::from_bool(member == 2), G::from_bool(member == 0)]
    );
    assert_eq!(values[3], G::ONE);
  }
  assert!(trace.values[6 * trace.width..].iter().all(|&v| v == G::ZERO));
}
