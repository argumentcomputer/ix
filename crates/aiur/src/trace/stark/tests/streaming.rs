use super::*;
use multi_stark::batch::Retention;

fn grouped() -> (CheckedProgram, TraceArtifact) {
  #[derive(serde::Deserialize)]
  struct Package {
    program: Program,
    trace: TraceArtifact,
  }
  let package: Package = serde_json::from_str(include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/grouping.json"
  )))
  .unwrap();
  (package.program.check().unwrap(), package.trace)
}

#[test]
fn incremental_ranges_match_full_grouped_rows_and_proofs() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = host_lookups(&plan);
  let entry = "Grouped::run";
  let record = program.execute(entry, vec![3]).unwrap();
  let full = backend.generate_stage_1(&record, entry, &[3]).unwrap();
  let prepared =
    backend.prepare_incremental(&record, Some((entry, &[3]))).unwrap();
  for rows in [1, 2, 4, 8] {
    let layout = backend.uniform_layout(&record, rows).unwrap();
    for (i, shard) in layout.shards.iter().enumerate() {
      let expected = backend.slice_stage_1(&full, i, rows).unwrap();
      let actual = backend.incremental_witness(&prepared, shard).unwrap();
      for (expected, actual) in expected.iter().zip(actual.traces) {
        let actual = actual.materialize();
        assert_eq!(actual.width, expected.width);
        assert_eq!(actual.values, expected.values, "shard {i}, cap {rows}");
      }
    }
    let control = backend
      .prove_batch_stage_1(
        entry,
        &[3],
        &record.output,
        full.clone(),
        rows,
        Retention::Regenerate,
      )
      .unwrap()
      .to_bytes()
      .unwrap();
    for retention in [Retention::Retain, Retention::Regenerate] {
      let proof = backend
        .prove_incremental(
          &record,
          entry,
          &[3],
          &record.output,
          &layout,
          retention,
        )
        .unwrap();
      assert_eq!(
        proof.to_bytes().unwrap(),
        control,
        "cap {rows}, {retention:?}"
      );
    }
  }
}

#[test]
fn fixed_log_heights_prove_one_all_active_shard() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = host_lookups(&plan);
  let entry = "Grouped::run";
  let record = program.execute(entry, vec![3]).unwrap();
  let rows = backend.record_rows(&record).unwrap();
  let logs: Vec<u8> = rows
    .iter()
    .map(|&n| n.max(1).next_power_of_two().ilog2() as u8 + 1)
    .collect();
  let options = planning::Options {
    fixed_log_heights: Some(logs.clone()),
    max_ram_bytes: Some(1 << 30),
    ..Default::default()
  };
  let planned = backend.plan_record(&record, &options, 0).unwrap();
  assert!(planned.forced_layout);
  let proof = backend
    .prove_incremental(
      &record,
      entry,
      &[3],
      &record.output,
      planned.layout.as_ref().unwrap(),
      planned.retention(),
    )
    .unwrap();
  backend.verify_batch(entry, &[3], &record.output, &proof).unwrap();
  let [header] = proof.preamble.headers.as_slice() else {
    panic!("expected one shard")
  };
  assert!(header.active.iter().all(|&a| a));
  assert_eq!(header.log_degrees, logs);
  let key =
    VerifyingKey::from_bytes(&backend.verifying_key_bytes().unwrap()).unwrap();
  let claims = [backend.claim(entry, &[3], &record.output).unwrap()];
  key.validate_preamble(&claims, &proof.preamble).unwrap();
  key.verify(&claims, &proof).unwrap();
  let ci = rows.iter().position(|&n| n > 2).unwrap();
  let mut small = logs.clone();
  small[ci] = 1;
  assert!(backend.fixed_layout(&record, &small).is_err());
  assert!(backend.fixed_layout(&record, &logs[1..]).is_err());
  let both = planning::Options { layout: planned.layout.clone(), ..options };
  assert!(both.validate().is_err());
}

#[test]
fn packed_layout_proves_and_rejects_missing_or_duplicate_ranges() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  let options = planning::Options {
    max_rows: Some(2),
    max_ram_bytes: Some(1 << 30),
    ..Default::default()
  };
  let planned = backend.plan_record(&record, &options, 0).unwrap();
  assert!(planned.fits);
  let layout = planned.layout.as_ref().unwrap();
  let rows = backend.record_rows(&record).unwrap();
  let proof = backend
    .prove_incremental(
      &record,
      "Grouped::run",
      &[3],
      &record.output,
      layout,
      planned.retention(),
    )
    .unwrap();
  backend.verify_batch("Grouped::run", &[3], &record.output, &proof).unwrap();
  assert!(
    backend.verify_batch("Grouped::run", &[4], &record.output, &proof).is_err()
  );
  let mut bad = layout.clone();
  let ci = bad.shards[0].circuits.iter().position(|s| s.rows > 0).unwrap();
  bad.shards[0].circuits[ci].rows -= 1;
  assert!(backend.validate_layout(&rows, &bad).is_err());
  let mut bad = layout.clone();
  bad.shards.push(bad.shards[0].clone());
  bad.shards.last_mut().unwrap().fixed_counts = false;
  assert!(backend.validate_layout(&rows, &bad).is_err());
  let mut bad = layout.clone();
  bad.memory_intervals.clear();
  assert!(
    backend
      .prove_incremental(
        &record,
        "Grouped::run",
        &[3],
        &record.output,
        &bad,
        Retention::Regenerate
      )
      .is_err()
  );
}

#[test]
fn incremental_fixed_tables_match_both_rounds() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("root", vec![3]).unwrap();
  let fixed_cells: u64 = backend
    .system
    .circuits
    .iter()
    .filter(|c| c.preprocessed_height != 0)
    .map(|c| {
      (c.preprocessed_height
        * (c.main_width + c.stage_2_width + 2 * c.quotient_degree()))
        as u64
    })
    .sum();
  let largest_row = backend
    .system
    .circuits
    .iter()
    .filter(|c| c.preprocessed_height == 0)
    .map(|c| c.main_width + c.stage_2_width + 2 * c.quotient_degree())
    .max()
    .unwrap() as u64;
  let options = planning::Options {
    max_cells: Some(fixed_cells + largest_row),
    max_ram_bytes: Some(1 << 30),
    ..Default::default()
  };
  let batch = backend.plan_record(&record, &options, 0).unwrap();
  let layout = batch.layout.unwrap();
  assert!(layout.shards.len() > 1);
  let prepared =
    backend.prepare_incremental(&record, Some(("root", &[3]))).unwrap();
  for (i, shard) in layout.shards.iter().enumerate() {
    let witness = backend.incremental_witness(&prepared, shard).unwrap();
    for (circuit, trace) in backend.system.circuits.iter().zip(witness.traces) {
      if circuit.preprocessed_height == 0 {
        continue;
      }
      let trace = trace.materialize();
      assert_eq!(trace.height(), circuit.preprocessed_height);
      assert_eq!(trace.values.iter().any(|&x| x != Val::ZERO), i == 0);
    }
  }
  let a = backend
    .prove_incremental(
      &record,
      "root",
      &[3],
      &record.output,
      &layout,
      Retention::Retain,
    )
    .unwrap();
  let b = backend
    .prove_incremental(
      &record,
      "root",
      &[3],
      &record.output,
      &layout,
      Retention::Regenerate,
    )
    .unwrap();
  assert_eq!(a.to_bytes().unwrap(), b.to_bytes().unwrap());
}

#[test]
fn streamed_supplier_rejects_a_changed_second_round() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("root", vec![3]).unwrap();
  let mut calls = 0;
  let result = backend.prove_streamed_stage_1(
    "root",
    &[3],
    &record.output,
    StreamPlan {
      shards: 2,
      memory_intervals: backend.record_shape(&record).unwrap().memory_intervals,
      retention: Retention::Regenerate,
    },
    |_| {
      calls += 1;
      let mut traces = backend.generate_stage_1(&record, "root", &[3])?;
      // Round one supplies shards one and zero; round two regenerates one.
      if calls == 3 {
        traces[0].values[0] += Val::ONE;
      }
      Ok(traces)
    },
  );
  assert!(result.err().unwrap().contains("changed between rounds"));
}

#[test]
fn packing_reduces_sparse_shards_and_checks_protocol_bounds() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let mut backend = host_lookups(&plan);
  let mut rows: Vec<_> = backend
    .system
    .circuits
    .iter()
    .map(
      |c| {
        if c.preprocessed_height != 0 { c.preprocessed_height } else { 64 }
      },
    )
    .collect();
  let last = rows.len() - 1;
  rows[last] = 4096;
  let cost = |ci: usize, height: usize| {
    let c = &backend.system.circuits[ci];
    height as u128
      * (c.main_width + c.stage_2_width + 2 * c.quotient_degree()) as u128
  };
  let limit = rows.iter().enumerate().map(|(ci, &n)| cost(ci, n.min(64))).sum();
  let packed = backend.packed_layout(&rows, &[], limit, None).unwrap();
  assert!(packed.shards.len() < 4096 / 64);
  for shard in &packed.shards {
    assert!(
      shard
        .circuits
        .iter()
        .enumerate()
        .map(|(ci, s)| cost(ci, s.height))
        .sum::<u128>()
        <= limit
    );
  }
  assert_eq!(packed, backend.packed_layout(&rows, &[], limit, None).unwrap());
  assert!(backend.packed_layout(&rows, &[], 1, None).is_err());
  backend.system.circuits[last].num_lookups = (Val::ORDER_U64 / 1024) as usize;
  assert!(backend.packed_layout(&rows, &[], limit, Some(64)).is_err());
}

#[test]
fn malformed_records_are_rejected_before_planning_or_population() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = host_lookups(&plan);
  let mut record = program.execute("root", vec![3]).unwrap();
  let layout = backend.uniform_layout(&record, 1).unwrap();
  record.queries.tables.clear();
  assert!(
    backend
      .plan_record(&record, &planning::Options::default(), 0)
      .unwrap_err()
      .contains("callable count mismatch")
  );
  assert!(backend.uniform_layout(&record, 1).is_err());
  assert!(
    backend
      .prove_incremental(
        &record,
        "root",
        &[3],
        &[9],
        &layout,
        Retention::Regenerate
      )
      .err()
      .unwrap()
      .contains("callable count mismatch")
  );
}

#[test]
fn fixed_table_floor_returns_a_non_fitting_plan() {
  let (program, artifact) = fixture();
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("root", vec![3]).unwrap();
  for packing in [false, true] {
    let rejected = backend
      .plan_record(
        &record,
        &planning::Options {
          packing: Some(packing),
          max_cells: Some(1),
          max_ram_bytes: Some(u64::MAX),
          ..Default::default()
        },
        0,
      )
      .unwrap();
    assert!(!rejected.fits);
    assert!(rejected.shard_cells > 1);
    assert_eq!(rejected.candidates.len(), 1);
  }
}

#[test]
fn option_reading_sets_a_default_budget() {
  let path = std::env::temp_dir()
    .join(format!("aiur-review-options-{}.json", std::process::id()));
  std::fs::write(&path, "{}").unwrap();
  let options = planning::Options::read(
    Some(&path.to_string_lossy().into_owned()),
    None,
    None,
  )
  .unwrap();
  assert!(options.max_ram_bytes.is_some());
  // The option selecting full-trace population no longer exists.
  std::fs::write(&path, "{\"streaming\":true}").unwrap();
  assert!(
    planning::Options::read(
      Some(&path.to_string_lossy().into_owned()),
      None,
      None,
    )
    .is_err()
  );
  std::fs::remove_file(path).unwrap();
}

#[test]
fn incremental_population_errors_keep_function_and_query_context() {
  let (program, mut artifact) = fixture();
  let crate::trace::Action::Call { args, .. } =
    &mut artifact.functions[0].steps[0].action
  else {
    panic!("fixture root must call leaf");
  };
  args[0] = Polynomial::Const(4);
  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("root", vec![3]).unwrap();
  let layout = backend.uniform_layout(&record, 1).unwrap();
  let prepared =
    backend.prepare_incremental(&record, Some(("root", &[3]))).unwrap();
  let error =
    backend.incremental_witness(&prepared, &layout.shards[0]).err().unwrap();
  assert!(error.contains("root query 0:"), "{error}");
}

#[cfg(feature = "cuda")]
#[test]
fn gpu_packed_padding_stops_before_the_next_piece() {
  use multi_stark::witness::TraceSource;
  let (program, mut artifact) = grouped();
  artifact.groups.clear();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  let planned = backend
    .plan_record(
      &record,
      &planning::Options {
        max_rows: Some(1),
        max_ram_bytes: Some(1 << 30),
        ..Default::default()
      },
      0,
    )
    .unwrap();
  let mut layout = planned.layout.unwrap();
  let device = super::super::gpu::DevicePlans::new(&backend);
  let counts = backend.record_rows(&record).unwrap();
  let ci = device
    .circuits
    .iter()
    .enumerate()
    .find(|(ci, on)| **on && counts[*ci] > 1)
    .unwrap()
    .0;
  let si = layout
    .shards
    .iter()
    .position(|s| {
      s.circuits[ci].rows == 1 && s.circuits[ci].first + 1 < counts[ci]
    })
    .unwrap();
  layout.shards[si].circuits[ci].height = 2;
  backend.validate_layout(&counts, &layout).unwrap();
  let prepared =
    backend.prepare_incremental(&record, Some(("Grouped::run", &[3]))).unwrap();
  let expected = backend
    .incremental_witness(&prepared, &layout.shards[si])
    .unwrap()
    .traces
    .into_iter()
    .nth(ci)
    .unwrap()
    .materialize();
  assert!(expected.values[expected.width..].iter().all(|&x| x == Val::ZERO));
  drop(prepared);
  let control = backend
    .prove_incremental(
      &record,
      "Grouped::run",
      &[3],
      &record.output,
      &layout,
      Retention::Regenerate,
    )
    .unwrap()
    .to_bytes()
    .unwrap();
  backend.device_plans = Some(device);
  let prepared =
    backend.prepare_incremental(&record, Some(("Grouped::run", &[3]))).unwrap();
  let actual = backend
    .incremental_witness(&prepared, &layout.shards[si])
    .unwrap()
    .traces
    .into_iter()
    .nth(ci)
    .unwrap();
  assert!(matches!(actual, TraceSource::Generated(_)));
  assert_eq!(actual.materialize().values, expected.values);
  for retention in [Retention::Retain, Retention::Regenerate] {
    let proof = backend
      .prove_incremental(
        &record,
        "Grouped::run",
        &[3],
        &record.output,
        &layout,
        retention,
      )
      .unwrap();
    assert_eq!(proof.to_bytes().unwrap(), control);
  }
}

#[cfg(feature = "cuda")]
#[test]
fn incremental_gpu_population_preserves_proofs_and_reports_placement() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  let options =
    planning::Options { max_ram_bytes: Some(1 << 30), ..Default::default() };
  let host_plan = backend.plan_record(&record, &options, 0).unwrap();
  for rows in [1, 2, 8] {
    let layout = backend.uniform_layout(&record, rows).unwrap();
    backend.device_plans = None;
    let expected = backend
      .prove_incremental(
        &record,
        "Grouped::run",
        &[3],
        &record.output,
        &layout,
        Retention::Regenerate,
      )
      .unwrap()
      .to_bytes()
      .unwrap();
    backend.device_plans = Some(super::super::gpu::DevicePlans::new(&backend));
    for retention in [Retention::Retain, Retention::Regenerate] {
      let actual = backend
        .prove_incremental(
          &record,
          "Grouped::run",
          &[3],
          &record.output,
          &layout,
          retention,
        )
        .unwrap()
        .to_bytes()
        .unwrap();
      assert_eq!(actual, expected);
    }
  }
  let generated = backend.plan_record(&record, &options, 0).unwrap();
  assert_eq!(generated.stage1_cells, host_plan.stage1_cells);
  assert!(generated.host_stage1_cells < host_plan.host_stage1_cells);
  assert!(generated.device_record_bytes > 0);
  assert!(generated.device_peak_bytes > 0);
  let impossible = backend
    .plan_record(
      &record,
      &planning::Options { max_device_bytes: Some(1), ..options },
      0,
    )
    .unwrap();
  assert!(!impossible.fits);
}

fn prove_scheduled(
  backend: &Backend<'_, '_, PrimeField>,
  record: &Execution<PrimeField>,
  layout: &super::super::streaming::BatchLayout,
  retention: Retention,
  pipeline: bool,
) -> (Vec<u8>, super::super::streaming::PopulationReport) {
  let run = backend
    .prove_incremental_timed(
      record,
      "Grouped::run",
      &[3],
      &record.output,
      layout,
      retention,
      pipeline,
    )
    .unwrap();
  (run.proof.to_bytes().unwrap(), run.population)
}

#[test]
fn pipelined_population_matches_serial_proofs() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  for rows in [1, 2, 8] {
    let layout = backend.uniform_layout(&record, rows).unwrap();
    for retention in [Retention::Retain, Retention::Regenerate] {
      let (serial, report) =
        prove_scheduled(&backend, &record, &layout, retention, false);
      assert!(!report.pipelined);
      let (pipelined, report) =
        prove_scheduled(&backend, &record, &layout, retention, true);
      let shards = layout.shards.len();
      // Shard zero's commitment carries over the barrier; the others are
      // supplied again when regenerated.
      let supplies = if matches!(retention, Retention::Retain) {
        shards
      } else {
        2 * shards - 1
      };
      assert_eq!(backend.supply_order(shards, retention).len(), supplies);
      assert_eq!(report.pipelined, supplies > 1);
      assert_eq!(pipelined, serial, "cap {rows}, {retention:?}");
      assert_eq!(report.shards.len(), supplies);
      assert_eq!(report.rounds.len(), if supplies > shards { 2 } else { 1 });
      assert!(!report.top_circuits.is_empty());
    }
  }
}

#[test]
fn pipelined_population_stops_on_a_worker_error() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  let layout = backend.uniform_layout(&record, 1).unwrap();
  assert!(layout.shards.len() > 2);
  let prepared =
    backend.prepare_incremental(&record, Some(("Grouped::run", &[3]))).unwrap();
  let error = backend
    .prove_streamed_scheduled(
      "Grouped::run",
      &[3],
      &record.output,
      StreamPlan {
        shards: layout.shards.len(),
        memory_intervals: layout.memory_intervals.clone(),
        retention: Retention::Regenerate,
      },
      Some(&ShardFeed::new(2).unwrap()),
      |round, shard| {
        if round == 1 && shard == 1 {
          return Err("injected".into());
        }
        backend.incremental_witness(&prepared, &layout.shards[shard])
      },
    )
    .err()
    .unwrap();
  assert_eq!(error, "injected");
}

#[test]
fn planner_charges_the_lookahead_and_accepts_a_fixed_layout() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = host_lookups(&plan);
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  let options = planning::Options {
    max_rows: Some(2),
    max_ram_bytes: Some(1 << 30),
    retention: planning::RetentionPolicy::Regenerate,
    ..Default::default()
  };
  let pipelined = backend.plan_record(&record, &options, 0).unwrap();
  assert!(pipelined.pipelined && pipelined.lookahead_bytes > 0);
  let serial = backend
    .plan_record(
      &record,
      &planning::Options { pipeline: Some(false), ..options.clone() },
      0,
    )
    .unwrap();
  assert!(!serial.pipelined);
  assert_eq!(serial.layout, pipelined.layout);
  assert!(serial.proving_peak_bytes < pipelined.proving_peak_bytes);
  // A budget with room for the serial peak only falls back to serial.
  let tight = backend
    .plan_record(
      &record,
      &planning::Options {
        max_ram_bytes: Some(serial.proving_peak_bytes),
        ..options.clone()
      },
      0,
    )
    .unwrap();
  assert!(tight.fits && !tight.pipelined);

  let layout = backend.uniform_layout(&record, 1).unwrap();
  let path = std::env::temp_dir()
    .join(format!("aiur-forced-layout-{}.json", std::process::id()));
  let report = serde_json::json!({"plan": {"layout": layout}});
  std::fs::write(&path, serde_json::to_vec(&report).unwrap()).unwrap();
  std::fs::write(
    path.with_extension("options.json"),
    serde_json::to_vec(
      &serde_json::json!({"layout_file": path, "max_ram_bytes": 1u64 << 30}),
    )
    .unwrap(),
  )
  .unwrap();
  let read = planning::Options::read(
    Some(&path.with_extension("options.json").to_string_lossy().into_owned()),
    None,
    None,
  )
  .unwrap();
  std::fs::remove_file(&path).unwrap();
  std::fs::remove_file(path.with_extension("options.json")).unwrap();
  assert_eq!(read.layout.as_ref(), Some(&layout));
  let forced = backend.plan_record(&record, &read, 0).unwrap();
  assert!(forced.forced_layout && forced.fits);
  assert_eq!(forced.layout.as_ref(), Some(&layout));
  let mut bad = layout.clone();
  bad.memory_intervals.clear();
  assert!(
    backend
      .plan_record(
        &record,
        &planning::Options { layout: Some(bad), ..options },
        0
      )
      .is_err()
  );
}

#[cfg(feature = "cuda")]
#[test]
fn pipelined_gpu_population_matches_serial_proofs() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  backend.device_plans = Some(super::super::gpu::DevicePlans::new(&backend));
  let record = program.execute("Grouped::run", vec![3]).unwrap();
  for rows in [1, 2] {
    let layout = backend.uniform_layout(&record, rows).unwrap();
    for retention in [Retention::Retain, Retention::Regenerate] {
      let (serial, _) =
        prove_scheduled(&backend, &record, &layout, retention, false);
      let (pipelined, report) =
        prove_scheduled(&backend, &record, &layout, retention, true);
      assert!(report.pipelined || layout.shards.len() == 1);
      assert_eq!(pipelined, serial, "cap {rows}, {retention:?}");
    }
  }
}
