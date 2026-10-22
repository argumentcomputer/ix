// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

/// Run the same fixture in separate processes at the old and new revisions
/// to compare peak RSS. Construction and record allocation are outside the
/// timer; no proof is needed to measure witness generation. No timing pin.
#[test]
#[ignore = "manual witness construction memory and timing measurement"]
fn witness_construction_timings() {
  use std::{hint::black_box, time::Instant};

  let n: usize = std::env::var("AIUR_WITNESS_ROWS")
    .unwrap_or_else(|_| "1048576".into())
    .parse()
    .expect("positive row count");
  assert!(n > 0);
  let function = Function {
    body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 1,
      lookups: 1,
    },
    entry: true,
    constrained: true,
  };
  let top = with_singleton_circuits(vec![function], vec![]);
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(top, cp, fp);
  let mut record = QueryRecord::new(&system.toplevel);
  for value in 0..n {
    let value = G::from_usize(value);
    record.function_queries[0].insert(&[value], &[value], G::ONE).unwrap();
  }
  let start = Instant::now();
  let (trace, lookups) = system.toplevel.witness_data(
    0,
    &record,
    &empty_io_buffer(),
    &system.slot_widths[0],
  );
  let elapsed = start.elapsed();
  assert_eq!(trace.values.len(), n.next_power_of_two() * 3);
  assert_eq!(&trace.values[..3], &[G::ZERO, G::ONE, G::ONE]);
  assert_eq!(trace.values[(n - 1) * 3], G::from_usize(n - 1));
  black_box((&trace, &lookups));
  eprintln!(
    "rows={n} metadata_bytes={} witness_ms={:.3}",
    crate::trace::witness_metadata_bytes(1, n),
    elapsed.as_secs_f64() * 1_000.0
  );
}
