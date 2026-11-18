//! The device interpreter's tiles, workspace pool, release and allowlist.
use super::super::gpu::{DevicePlans, DeviceRecord};
use super::*;
use planning::{HostCause, PopulationProvider};

const ENTRY: &str = "Grouped::run";

fn grouped() -> (CheckedProgram, TraceArtifact) {
  let package = grouping_fixture();
  (package.program.check().unwrap(), package.trace)
}

/// Host rows of every circuit as canonical words.
fn host_words<B: WitnessField>(
  backend: &Backend<'_, '_, B>,
  record: &Execution<B>,
  args: &[B::Element],
) -> Vec<Vec<u64>> {
  backend
    .generate_stage_1(record, ENTRY, args)
    .unwrap()
    .into_iter()
    .map(|m| m.values.iter().map(|v| v.as_canonical_u64()).collect())
    .collect()
}

fn device_circuits(plans: &DevicePlans) -> Vec<usize> {
  plans
    .circuits
    .iter()
    .enumerate()
    .filter(|(_, on)| **on)
    .map(|(ci, _)| ci)
    .collect()
}

/// Tiles start from a garbage-filled buffer, so every word, including the
/// padding rows the device zeroes, is compared before any field conversion.
const GARBAGE: u64 = 0xdead_beef_dead_beef;

#[test]
fn device_tiles_match_host_words_across_pooled_tiles() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let expected = host_words(&backend, &record, &[3]);
  let rows = backend.record_rows(&record).unwrap();
  let plans = DevicePlans::new(&backend);
  let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
  let circuits = device_circuits(&plans);
  assert!(!circuits.is_empty(), "fixture has no device circuit");
  for &ci in &circuits {
    let height = device.height(ci).unwrap();
    let width = backend.system.circuits[ci].main_width;
    let whole =
      device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap();
    assert_eq!(whole, expected[ci], "circuit {ci}");
    // A slice ending one row early zeroes the row it drops.
    let real = rows[ci] - 1;
    let short =
      device.tile_words(ci, None, 0, 0, height, height, real, GARBAGE).unwrap();
    let mut padded = expected[ci].clone();
    padded[real * width..].fill(0);
    assert_eq!(short, padded);
    // One-row tiles, then a lookup halo of `height + 1` rows that wraps.
    for first in 0..height {
      let tile =
        device.tile_words(ci, None, 0, first, 1, height, rows[ci], GARBAGE).unwrap();
      assert_eq!(tile, expected[ci][first * width..(first + 1) * width]);
    }
    let halo = device
      .tile_words(ci, None, 0, 1, height + 1, height, rows[ci], GARBAGE)
      .unwrap();
    let wrapped: Vec<u64> = (0..=height)
      .flat_map(|r| {
        let row = (1 + r) % height;
        expected[ci][row * width..(row + 1) * width].iter().copied()
      })
      .collect();
    assert_eq!(halo, wrapped);
  }
  // Tiles run one at a time here, so one workspace serves all of them.
  assert_eq!(device.pooled_workspaces(), 1);
}

#[test]
fn released_device_record_serves_identical_tiles() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let rows = backend.record_rows(&record).unwrap();
  let plans = DevicePlans::new(&backend);
  let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
  let tiles = |device: &DeviceRecord| -> Vec<Vec<u64>> {
    device_circuits(&plans)
      .into_iter()
      .map(|ci| {
        let height = device.height(ci).unwrap();
        device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap()
      })
      .collect()
  };
  let before = tiles(&device);
  device.release(1);
  assert!(device.is_resident(), "another device's release freed the record");
  for _ in 0..2 {
    device.release(0);
    assert!(!device.is_resident());
    assert_eq!(device.pooled_workspaces(), 0);
    assert_eq!(tiles(&device), before);
    assert!(device.is_resident());
  }
  drop(record);
  device.release(0);
  assert_eq!(tiles(&device), before, "host copy outlives the record");
}

/// A device record lent its execution record releases without a host copy
/// and re-uploads the same tiles from the record; once the loan ends, a
/// release copies again.
#[test]
fn attached_device_record_releases_without_a_host_copy() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let other = program.execute(ENTRY, vec![3]).unwrap();
  let rows = backend.record_rows(&record).unwrap();
  let plans = DevicePlans::new(&backend);
  let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
  let tiles = |device: &DeviceRecord| -> Vec<Vec<u64>> {
    device_circuits(&plans)
      .into_iter()
      .map(|ci| {
        let height = device.height(ci).unwrap();
        device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap()
      })
      .collect()
  };
  let before = tiles(&device);
  // SAFETY: the guards are dropped within this scope, before the records.
  assert!(unsafe { device.attach(&other) }.is_err());
  {
    let _attached = unsafe { device.attach(&record) }.unwrap();
    for _ in 0..2 {
      device.release(0);
      assert!(!device.is_resident());
      assert!(!device.has_host_copy());
      assert_eq!(tiles(&device), before);
    }
  }
  device.release(0);
  assert!(device.has_host_copy());
  assert_eq!(tiles(&device), before);
}

/// Tiles requested at once on a small pool after a release: one re-uploads
/// the record under the state lock while the others wait for it, so the
/// re-upload, from the lent record or from a host copy, must not run queued
/// tile jobs on its own thread.
#[cfg(feature = "parallel")]
#[test]
fn concurrent_tiles_restore_a_released_record_once() {
  use rayon::prelude::*;
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let rows = backend.record_rows(&record).unwrap();
  let plans = DevicePlans::new(&backend);
  let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
  let circuits = device_circuits(&plans);
  let tile = |ci: usize| {
    let height = device.height(ci).unwrap();
    device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap()
  };
  let before: Vec<_> = circuits.iter().map(|&ci| tile(ci)).collect();
  let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
  // SAFETY: the guard is dropped halfway through, before the record.
  let mut attached = Some(unsafe { device.attach(&record) }.unwrap());
  for round in 0..8 {
    // Restored from the lent record, then from a host copy.
    if round == 4 {
      attached = None;
    }
    device.release(0);
    assert_eq!(device.has_host_copy(), attached.is_none());
    assert!(!device.is_resident());
    let jobs: Vec<_> = circuits.iter().cycle().take(16).copied().collect();
    let tiles: Vec<_> =
      pool.install(|| jobs.par_iter().map(|&ci| tile(ci)).collect());
    for (ci, words) in jobs.iter().zip(tiles) {
      let index = circuits.iter().position(|c| c == ci).unwrap();
      assert_eq!(words, before[index]);
    }
    assert!(device.is_resident());
  }
}

#[test]
fn allowlist_selects_circuits_and_reports_causes() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let options =
    planning::Options { max_ram_bytes: Some(1 << 30), ..Default::default() };
  let report = |backend: &Backend<'_, '_, _>| {
    backend.plan_record(&record, &options, 0).unwrap().population
  };
  let index =
    |name: &str| backend.names.iter().position(|n| n == name).unwrap();
  let grouped = index("arithmetic_and_memory");

  let host = report(&backend);
  assert!(host.iter().all(|p| p.provider == PopulationProvider::Cpu));
  assert_eq!(host[grouped].host_causes, [HostCause::DeviceDisabled]);
  let fixed = backend.members.len();
  if fixed < host.len() {
    assert!(matches!(
      host[fixed].host_causes[..],
      [HostCause::FixedTable] | [HostCause::Rom]
    ));
  }

  let all = DevicePlans::new(&backend);
  let on = device_circuits(&all);
  assert!(on.contains(&grouped), "stores and loads run on the device");
  let all_bytes = all.record_bytes(&backend, &record).unwrap();
  backend.device_plans = Some(all);
  let full = report(&backend);
  for &ci in &on {
    assert_eq!(full[ci].provider, PopulationProvider::GpuInterpreter);
    assert!(full[ci].host_causes.is_empty());
  }

  // One circuit by name: the others report it, and the upload shrinks.
  let chosen = on[0];
  let name = backend.names[chosen].clone();
  let one = DevicePlans::select(&backend, Some(&[name])).unwrap();
  assert_eq!(device_circuits(&one), [chosen]);
  let one_bytes = one.record_bytes(&backend, &record).unwrap();
  assert!(one_bytes <= all_bytes);
  backend.device_plans = Some(one);
  let selected = report(&backend);
  for &ci in &on {
    let expected: &[HostCause] =
      if ci == chosen { &[] } else { &[HostCause::NotSelected] };
    assert_eq!(selected[ci].host_causes, expected);
  }

  // A member function name selects its circuit; an ineligible one selects
  // nothing, and unknown names are rejected.
  let member = &plan.artifact.functions[backend.members[chosen][0]].name;
  let by_member =
    DevicePlans::select(&backend, Some(std::slice::from_ref(member))).unwrap();
  assert!(by_member.circuits[chosen]);
  assert!(DevicePlans::select(&backend, Some(&["Nope".into()])).is_err());
  let unchosen = on.iter().copied().find(|&ci| ci != chosen).unwrap();
  backend.device_plans = Some(by_member);
  let none = report(&backend);
  assert_eq!(none[unchosen].host_causes, [HostCause::NotSelected]);
}

/// A circuit whose plan reads a hint channel the device does not implement
/// stays on the host and reports it, also when selected by name.
#[test]
fn unsupported_hints_stay_on_the_host() {
  use super::{f, step, v, writes};
  let program: Program = serde_json::from_value(json!({
    "version":1,"modulus":Val::ORDER_U64,"enums":[],"maps":[],"tables":[],
    "functions":[{"name":"root","params":[f()],"result":f(),"registers":2,"code":[
      {"op":"hint","channel":"half","type":f(),"key_type":f(),"key":[0],"dest":[1]},
      {"op":"ret","value":[0]}]}],
    "entries":[{"name":"root","function":0,"inputs":[f()],"output":f()}]
  }))
  .unwrap();
  let program = program.check().unwrap();
  let artifact = crate::trace::tests::activate(
    crate::trace::tests::raw_artifact(json!({
      "version":1,"modulus":Val::ORDER_U64,
      "functions":[{"name":"root","chip":"root","witnesses":2,"inputs":[0],"output":[0],
        "steps":[step(json!({"op":"hint","channel":"half","instruction":0,
          "type":f(),"key_type":f(),"key":[v(0)],"dest":[1]}))],
        "writes":writes(2)}],
      "chips":[{"name":"root","width":2,"inputs":[0],"output":[v(0)],
        "constraints":[],"sends":[],"memory":[]}]
    })),
  );
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let hints: Vec<crate::hints::HintEntry> = serde_json::from_value(json!([
    {"channel":"half","type":f(),"key_type":f(),"key":[4],"output":[2]}]))
  .unwrap();
  let record = program.execute_with_hints("root", vec![4], &hints).unwrap();
  let options =
    planning::Options { max_ram_bytes: Some(1 << 30), ..Default::default() };
  let root = backend.names.iter().position(|n| n == "root").unwrap();
  for allowlist in [None, Some(vec!["root".to_owned()])] {
    let plans = DevicePlans::select(&backend, allowlist.as_deref()).unwrap();
    // A record's byte model covers circuits that stay on the host.
    let model = plans.record_model(&backend, &record).unwrap();
    assert_eq!(
      model.bytes(&plans.circuits),
      plans.record_bytes(&backend, &record).unwrap()
    );
    backend.device_plans = Some(plans);
    let report = backend.plan_record(&record, &options, 0).unwrap().population;
    assert_eq!(report[root].host_causes, [HostCause::UnsupportedHint]);
    assert!(report[root].reason.contains("root (hint half)"));
    let json = serde_json::to_value(&report[root]).unwrap();
    assert_eq!(json["provider"], "cpu");
    assert_eq!(json["host_causes"], json!(["unsupported_hint"]));
  }
}

/// ROM stores and loads fill on the device to the host's words, whole and
/// in wrapped one-row tiles, and prove the host's bytes: cells of widths 0,
/// 1 and 2 shared across types, an unused width, and the grouped fixture's
/// memory circuit.
#[test]
fn rom_circuits_fill_on_the_device() {
  use multi_stark::batch::Retention;
  let mixed = super::mixed_memory();
  let mixed = (mixed.0, crate::trace::tests::activate(mixed.1));
  let grouping = grouped();
  for ((program, artifact), entry, args) in
    [(mixed, "root", vec![3, 0, 7]), (grouping, ENTRY, vec![3])]
  {
    let plan = TracePlan::new(&program, artifact).unwrap();
    let mut backend =
      Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
        .unwrap();
    let record = program.execute(entry, args.clone()).unwrap();
    let expected: Vec<Vec<u64>> = backend
      .generate_stage_1(&record, entry, &args)
      .unwrap()
      .into_iter()
      .map(|m| m.values.iter().map(|v| v.as_canonical_u64()).collect())
      .collect();
    let rows = backend.record_rows(&record).unwrap();
    let plans = DevicePlans::new(&backend);
    let rom: Vec<usize> = (0..backend.members.len())
      .filter(|&ci| {
        backend.members[ci].iter().any(|&f| {
          plan.artifact.functions[f].steps.iter().any(|s| {
            matches!(
              s.action,
              crate::trace::Action::Store { .. }
                | crate::trace::Action::Load { .. }
            )
          })
        })
      })
      .collect();
    assert!(!rom.is_empty());
    let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
    for &ci in &rom {
      assert!(plans.circuits[ci], "{} stays on the host", backend.names[ci]);
      let height = device.height(ci).unwrap();
      let width = backend.system.circuits[ci].main_width;
      let whole =
        device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap();
      assert_eq!(whole, expected[ci], "{}", backend.names[ci]);
      for first in 0..height {
        let tile = device
          .tile_words(ci, None, 0, first, 1, height, rows[ci], GARBAGE)
          .unwrap();
        assert_eq!(tile, expected[ci][first * width..(first + 1) * width]);
      }
    }
    // Released and rebuilt from the host copy, the ROM reads the same.
    device.release(0);
    for &ci in &rom {
      let height = device.height(ci).unwrap();
      let whole =
        device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap();
      assert_eq!(whole, expected[ci], "{} after release", backend.names[ci]);
    }
    let layout = backend.uniform_layout(&record, 2).unwrap();
    let prove = |backend: &Backend<'_, '_, _>| {
      backend
        .prove_incremental(
          &record,
          entry,
          &args,
          &record.output,
          &layout,
          Retention::Regenerate,
        )
        .unwrap()
        .to_bytes()
        .unwrap()
    };
    backend.device_plans = None;
    let host = prove(&backend);
    backend.device_plans = Some(plans);
    assert_eq!(prove(&backend), host, "{entry}");
  }
}

/// Restricting device population to one circuit proves the same bytes as
/// host population.
#[test]
fn allowlisted_population_proves_identically() {
  use multi_stark::batch::Retention;
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let layout = backend.uniform_layout(&record, 2).unwrap();
  let prove = |backend: &Backend<'_, '_, _>| {
    backend
      .prove_incremental(
        &record,
        ENTRY,
        &[3],
        &record.output,
        &layout,
        Retention::Regenerate,
      )
      .unwrap()
      .to_bytes()
      .unwrap()
  };
  let expected = prove(&backend);
  let all = DevicePlans::new(&backend);
  for ci in device_circuits(&all) {
    let name = backend.names[ci].clone();
    backend.device_plans =
      Some(DevicePlans::select(&backend, Some(&[name])).unwrap());
    assert_eq!(prove(&backend), expected, "circuit {ci}");
  }
}

/// The planner charges what concurrent population calls can hold: a minimal
/// workspace per concurrent writer and a scratch workspace of the widest
/// interpreted circuit's size per concurrent interpreted writer, each of
/// them what commitment admission reserves for a generated trace.
#[test]
fn planned_scratch_covers_concurrent_writers() {
  use super::super::gpu::DeviceTrace;
  use multi_stark::witness::TraceGenerator;
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let rows = backend.record_rows(&record).unwrap();
  let plans = DevicePlans::new(&backend);
  let device = std::sync::Arc::new(
    DeviceRecord::upload(&backend, &plans, &record, 0).unwrap(),
  );
  let traces: Vec<_> = device_circuits(&plans)
    .into_iter()
    .map(|ci| DeviceTrace {
      record: std::sync::Arc::clone(&device),
      circuit: ci,
      base: 0,
      height: device.height(ci).unwrap(),
      real_rows: rows[ci],
      rows: None,
    })
    .collect();
  assert!(!traces.is_empty());
  let bytes: Vec<u64> =
    traces.iter().map(|t| t.device_workspace_bytes() as u64).collect();
  let minimal = super::super::gpu::workspace_bytes(0);
  let scratch: Vec<u64> =
    bytes.iter().copied().filter(|&b| b > minimal).collect();
  assert!(!scratch.is_empty(), "fixture has no interpreted scratch");
  let limit = multi_stark::cuda::MAX_CONCURRENT_LDES;
  assert_eq!(
    plans.scratch_bytes(&backend.members, &plans.circuits),
    scratch.iter().max().unwrap() * scratch.len().min(limit) as u64
      + minimal * bytes.len().min(limit) as u64
  );
  // The record is the state a release frees and the next tile restores.
  for trace in &traces {
    assert!(trace.device_state_resident());
    assert_eq!(
      trace.device_state_bytes() > 0,
      super::super::gpu::release_enabled()
    );
  }
}

/// The device record is charged beside the stage-one and stage-two LDEs it
/// populates, and, when releasable, not beside the quotient peak.
#[test]
fn device_peak_charges_the_record_while_populating() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  backend.device_plans = Some(DevicePlans::new(&backend));
  let record: u64 = 3 << 30;
  let population = 1u128 << 28;
  // Population dominates: the record adds at least its own bytes.
  assert!(
    backend.device_peak(population, population, record, 1 << 10)
      >= backend.device_peak(population, population, 0, 1 << 10)
        + u128::from(record)
  );
  // The quotient phase dominates: a releasable record adds nothing.
  let committed = population * 64;
  if !super::super::gpu::release_enabled() {
    return;
  }
  assert_eq!(
    backend.device_peak(committed, population, record, 1 << 10),
    backend.device_peak(committed, population, 0, 1 << 10)
  );
}

/// Device population plans the layout host population gets, and keeps a
/// record on the host when its device plan does not fit there.
#[test]
fn device_population_keeps_the_host_layout() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let options = |max_device_bytes| planning::Options {
    max_device_bytes: Some(max_device_bytes),
    ..Default::default()
  };
  let generated = |plan: &planning::BatchPlan| {
    plan.population.iter().filter(|c| c.generated).count()
  };
  let host = backend.plan_record(&record, &options(1 << 40), 0).unwrap();
  assert_eq!(generated(&host), 0);
  backend.device_plans = Some(DevicePlans::new(&backend));
  let device = backend.plan_record(&record, &options(1 << 40), 0).unwrap();
  assert!(device.fits);
  assert!(generated(&device) > 0);
  assert_eq!(device.layout, host.layout);
  assert!(device.device_peak_bytes > host.device_peak_bytes);
  // A budget the host layout meets but its device population does not.
  let tight =
    backend.plan_record(&record, &options(host.device_peak_bytes), 0).unwrap();
  assert!(tight.fits);
  assert_eq!(tight.layout, host.layout);
  assert_eq!(generated(&tight), 0);
  assert!(record.host_population.get());
  assert!(
    tight.population.iter().any(|c| c.host_causes == [HostCause::DeviceLayout])
  );
}

/// A record host population cannot prove gets the device plan instead of a
/// host plan that does not fit: whether host planning found no layout at
/// all, or only a layout over the device budget.
#[test]
fn device_population_plans_records_host_population_cannot_prove() {
  let (program, artifact) = grouped();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let host_backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  backend.device_plans = Some(DevicePlans::new(&backend));
  let record = program.execute(ENTRY, vec![3]).unwrap();
  let options = |max_ram_bytes, max_device_bytes| planning::Options {
    max_ram_bytes: Some(max_ram_bytes),
    max_device_bytes: Some(max_device_bytes),
    ..Default::default()
  };
  let generated = |plan: &planning::BatchPlan| {
    plan.population.iter().filter(|c| c.generated).count()
  };
  let check = |options: &planning::Options| {
    let device = backend.plan_record(&record, options, 0).unwrap();
    assert!(!record.host_population.get(), "{options:?}");
    assert!(generated(&device) > 0, "{options:?}");
    device
  };
  // No layout: the host floor already exceeds the RAM budget.
  let starved = options(1, 1 << 40);
  let host = host_backend.plan_record(&record, &starved, 0).unwrap();
  assert!(host.layout.is_none() && !host.fits);
  check(&starved);
  // A layout over the device budget, the last one the search tried: a
  // budget the floor meets but no packing does.
  let small = (10..40)
    .flat_map(|log| (0..8).map(move |step| (8u64 + step) << (log - 3)))
    .map(|budget| options(1 << 40, budget))
    .find(|options| {
      let host = host_backend.plan_record(&record, options, 0).unwrap();
      host.layout.is_some() && !host.fits
    })
    .expect("no device budget leaves host population an unfit layout");
  check(&small);
  // A fitting host layout still decides.
  let ample = options(1 << 40, 1 << 40);
  let host = host_backend.plan_record(&record, &ample, 0).unwrap();
  let device = check(&ample);
  assert!(host.fits && device.fits);
  assert_eq!(device.layout, host.layout);
}

/// Depth circuits (exact, gap and external slots) fill on the device to the
/// host's words, and the upload's range counts are the host's: proving with
/// them commits the same fixed range tables.
#[test]
fn depth_circuits_fill_on_the_device() {
  let (program, artifact) = depth::depth_fixture();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let entry = "Depth::run";
  let record = program.execute(entry, vec![12]).unwrap();
  let expected: Vec<Vec<u64>> = backend
    .generate_stage_1(&record, entry, &[12])
    .unwrap()
    .into_iter()
    .map(|m| m.values.iter().map(|v| v.as_canonical_u64()).collect())
    .collect();
  let rows = backend.record_rows(&record).unwrap();
  let plans = DevicePlans::new(&backend);
  let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
  let depth: Vec<usize> = (0..backend.members.len())
    .filter(|&ci| super::super::gpu::circuit_has_depth(&backend, ci))
    .collect();
  assert!(!depth.is_empty(), "fixture has no depth circuit");
  for &ci in &depth {
    assert!(plans.circuits[ci], "{} stays on the host", backend.names[ci]);
    let height = device.height(ci).unwrap();
    let tile =
      device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap();
    assert_eq!(tile, expected[ci], "{}", backend.names[ci]);
  }
  let gaps: u64 = device.ranges().table(0).iter().sum();
  assert!(gaps > 0, "fib's gap slots were not counted");
  // Released and rebuilt, the record still reads the recorded heights.
  device.release(0);
  for &ci in &depth {
    let height = device.height(ci).unwrap();
    let tile =
      device.tile_words(ci, None, 0, 0, height, height, rows[ci], GARBAGE).unwrap();
    assert_eq!(tile, expected[ci], "{} after release", backend.names[ci]);
  }
}

/// A budget the whole device record misses but part of it meets admits the
/// circuits that save the most host population per uploaded byte, keeps the
/// host layout, uploads only what they read and proves the host's bytes.
#[test]
fn device_population_admits_what_fits() {
  use multi_stark::batch::Retention;
  let (program, artifact) = depth::depth_fixture();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let entry = "Depth::run";
  let record = program.execute(entry, vec![12]).unwrap();
  let options = |max_device_bytes| planning::Options {
    max_device_bytes: Some(max_device_bytes),
    ..Default::default()
  };
  let generated = |plan: &planning::BatchPlan| {
    plan.population.iter().filter(|c| c.generated).count()
  };
  let host = backend.plan_record(&record, &options(1 << 40), 0).unwrap();
  backend.device_plans = Some(DevicePlans::new(&backend));
  let full = backend.plan_record(&record, &options(1 << 40), 0).unwrap();
  let all = generated(&full);
  assert!(all > 1);
  let partial = backend
    .plan_record(&record, &options(full.device_peak_bytes - 1), 0)
    .unwrap();
  assert!(partial.fits);
  assert_eq!(partial.layout, host.layout);
  let some = generated(&partial);
  assert!(0 < some && some < all, "{some} of {all}");
  assert!(partial.device_record_bytes < full.device_record_bytes);
  for stats in partial.population.iter().filter(|c| !c.generated) {
    if full.population.iter().any(|f| f.circuit == stats.circuit && f.generated)
    {
      assert_eq!(stats.host_causes, [HostCause::DeviceLayout]);
    }
  }
  let device = DeviceRecord::upload(
    &backend,
    backend.device_plans.as_ref().unwrap(),
    &record,
    0,
  )
  .unwrap();
  let on = (0..backend.members.len())
    .filter(|&ci| device.height(ci).is_some())
    .count();
  assert_eq!(on, some);
  let layout = partial.layout.clone().unwrap();
  let prove = |backend: &Backend<'_, '_, _>| {
    backend
      .prove_incremental(
        &record,
        entry,
        &[12],
        &record.output,
        &layout,
        Retention::Regenerate,
      )
      .unwrap()
      .to_bytes()
      .unwrap()
  };
  let mixed = prove(&backend);
  let plans = backend.device_plans.take();
  assert_eq!(mixed, prove(&backend));
  backend.device_plans = plans;
}

/// Device population holds no host bytes beyond the record, so a RAM
/// budget that just keeps the host plan pipelined admits every device
/// circuit, at the host layout, and plans a lower host peak.
#[test]
fn device_population_keeps_pipelining() {
  let (program, artifact) = depth::depth_fixture();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute("Depth::run", vec![12]).unwrap();
  let options = |max_ram_bytes| planning::Options {
    max_rows: Some(4),
    max_ram_bytes: Some(max_ram_bytes),
    max_device_bytes: Some(1 << 40),
    ..Default::default()
  };
  let host = backend.plan_record(&record, &options(1 << 40), 0).unwrap();
  assert!(host.pipelined && host.shards > 1);
  let tight = host.proving_peak_bytes;
  let host = backend.plan_record(&record, &options(tight), 0).unwrap();
  assert!(host.fits && host.pipelined);
  backend.device_plans = Some(DevicePlans::new(&backend));
  let roomy = backend.plan_record(&record, &options(1 << 40), 0).unwrap();
  assert!(roomy.pipelined);
  let device = backend.plan_record(&record, &options(tight), 0).unwrap();
  assert!(device.fits && device.pipelined);
  assert_eq!(device.layout, host.layout);
  let generated = |plan: &planning::BatchPlan| {
    plan.population.iter().filter(|c| c.generated).count()
  };
  assert!(generated(&device) > 0);
  assert_eq!(generated(&device), generated(&roomy));
  assert!(device.proving_peak_bytes < host.proving_peak_bytes);
}

/// The planner's byte model of a record equals the record's device bytes
/// for every admitted set, and planning a record again under the same
/// inputs reuses its search.
#[test]
fn record_model_matches_record_bytes() {
  let (program, artifact) = depth::depth_fixture();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let record = program.execute("Depth::run", vec![12]).unwrap();
  let plans = DevicePlans::new(&backend);
  let model = plans.record_model(&backend, &record).unwrap();
  let device: Vec<usize> = device_circuits(&plans);
  assert!(device.len() > 2);
  for bits in 0u32..(1 << device.len()) {
    let mut admitted = vec![false; plans.circuits.len()];
    for (i, &ci) in device.iter().enumerate() {
      admitted[ci] = bits & (1 << i) != 0;
    }
    record.host_population.set_circuits(Some(admitted.clone()));
    assert_eq!(
      model.bytes(&admitted),
      plans.record_bytes(&backend, &record).unwrap(),
      "{admitted:?}"
    );
  }
  record.host_population.set_circuits(None);
  backend.device_plans = Some(plans);
  let full =
    backend.plan_record(&record, &planning::Options::default(), 0).unwrap();
  let options = planning::Options {
    max_device_bytes: Some(full.device_peak_bytes - 1),
    ..Default::default()
  };
  let first = backend.plan_record(&record, &options, 0).unwrap();
  let admitted = record.host_population.circuits();
  assert!(admitted.is_some());
  let again = backend.plan_record(&record, &options, 0).unwrap();
  assert_eq!(record.host_population.circuits(), admitted);
  assert_eq!(again.device_record_bytes, first.device_record_bytes);
  assert_eq!(again.layout, first.layout);
}

/// With recorded row references, the device record is uploaded one shard
/// image at a time: every shard's tiles read the host's words from the rows
/// its image gathered, the shard-by-shard range counts are the whole
/// record's, and proving with shard images makes the host's proof bytes.
#[test]
fn shard_images_match_host_words_and_proofs() {
  use multi_stark::batch::Retention;
  let mixed = super::mixed_memory();
  let mixed = (mixed.0, crate::trace::tests::activate(mixed.1));
  for ((mut program, artifact), entry, args) in [
    (mixed, "root", vec![3, 0, 7]),
    (grouped(), ENTRY, vec![3]),
    (depth::depth_fixture(), "Depth::run", vec![12]),
  ] {
    program.record_refs(|_| true, &crate::trace::lookup_aliases(&artifact));
    let plan = TracePlan::new(&program, artifact).unwrap();
    let mut backend =
      Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
        .unwrap();
    let record = program.execute(entry, args.clone()).unwrap();
    let expected: Vec<Vec<u64>> = backend
      .generate_stage_1(&record, entry, &args)
      .unwrap()
      .into_iter()
      .map(|m| m.values.iter().map(|v| v.as_canonical_u64()).collect())
      .collect();
    let plans = DevicePlans::new(&backend);
    let whole = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
    for rows in [1, 2, 4] {
      let layout = backend.uniform_layout(&record, rows).unwrap();
      backend.device_plans = Some(DevicePlans::new(&backend));
      let report = backend.shard_image_report(&record, &layout).unwrap();
      for shard in report["shards"].as_array().unwrap() {
        assert!(
          shard["gathered_bytes"].as_u64() <= shard["bound_bytes"].as_u64(),
          "{entry}: the planned bound misses a gathered image: {shard}"
        );
      }
      let device =
        DeviceRecord::upload_sharded(&backend, &plans, &record, 0, &layout)
          .unwrap();
      assert_eq!(device.ranges(), whole.ranges(), "{entry} range counts");
      let _attached = unsafe { device.attach(&record) }.unwrap();
      for shard in &layout.shards {
        let image = device.shard_rows(&record, shard).unwrap();
        assert!(image.is_some(), "{entry}: no shard image");
        for ci in device_circuits(&plans) {
          let slice = shard.circuits[ci];
          if slice.height == 0 {
            continue;
          }
          let width = backend.system.circuits[ci].main_width;
          let tile = device
            .tile_words(
              ci,
              image.as_ref(),
              slice.first,
              0,
              slice.height,
              slice.height,
              slice.rows,
              GARBAGE,
            )
            .unwrap();
          let mut want =
            expected[ci][slice.first * width..(slice.first + slice.rows) * width]
              .to_vec();
          want.resize(slice.height * width, 0);
          assert_eq!(tile, want, "{entry}: {} at {slice:?}", backend.names[ci]);
        }
      }
      let prove = |backend: &Backend<'_, '_, _>| {
        backend
          .prove_incremental(
            &record,
            entry,
            &args,
            &record.output,
            &layout,
            Retention::Regenerate,
          )
          .unwrap()
          .to_bytes()
          .unwrap()
      };
      backend.device_plans = None;
      let host = prove(&backend);
      backend.device_plans = Some(DevicePlans::new(&backend));
      record.host_population.set_sharded(true);
      assert_eq!(prove(&backend), host, "{entry} with {rows}-row shards");
      record.host_population.set_sharded(false);
    }
  }
}

/// A program reading one value and a pair from stream advice through two
/// read channels, with the trace artifact of its single function.
fn arena_reader() -> (CheckedProgram, TraceArtifact) {
  use super::{step, v, writes};
  let pair = json!({"kind":"tuple","items":[f(),f()]});
  let program: Program = serde_json::from_value(json!({
    "version":1,"modulus":Val::ORDER_U64,"enums":[],"maps":[],"tables":[],
    "functions":[{"name":"root","params":[f(),f()],"result":f(),"registers":5,"code":[
      {"op":"hint","channel":"read1","type":f(),"key_type":pair,"key":[0,1],"dest":[2]},
      {"op":"hint","channel":"read2","type":pair,"key_type":pair,"key":[0,1],"dest":[3,4]},
      {"op":"ret","value":[2]}]}],
    "entries":[{"name":"root","function":0,"inputs":[f(),f()],"output":f()}]
  }))
  .unwrap();
  let artifact = activate(raw_artifact(json!({
    "version":1,"modulus":Val::ORDER_U64,
    "functions":[{"name":"root","chip":"root","witnesses":5,"inputs":[0,1],"output":[2],
      "steps":[
        step(json!({"op":"hint","channel":"read1","instruction":0,
          "type":f(),"key_type":pair,"key":[v(0),v(1)],"dest":[2]})),
        step(json!({"op":"hint","channel":"read2","instruction":1,
          "type":pair,"key_type":pair,"key":[v(0),v(1)],"dest":[3,4]}))],
      "writes":writes(5)}],
    "chips":[{"name":"root","width":5,"inputs":[0,1],"output":[v(2)],
      "constraints":[],"sends":[],"memory":[]}]
  })));
  (program.check().unwrap(), artifact)
}

/// Advice with a byte arena (channel 0), an empty channel 1, and a word
/// arena (channel 2) holding a non-byte value.
fn reader_advice(
  program: &CheckedProgram,
) -> crate::library::advice::Advice<PrimeField> {
  use crate::library::advice::{Advice, Entry, Payload};
  Advice::from_entries(
    program.field(),
    [
      Entry { channel: 0, key: &[1], payload: Payload::Bytes(&[7, 0, 255, 9]) },
      Entry { channel: 2, key: &[2], payload: Payload::Bytes(&[3]) },
      Entry {
        channel: 2,
        key: &[3],
        payload: Payload::Words(&[Val::ORDER_U64 - 1, 1 << 40]),
      },
    ],
  )
  .unwrap()
}

/// Reads of stream advice fill on the device to the host's words, byte
/// and word arenas alike, and again after a release re-uploads the arenas.
#[test]
fn arena_reads_match_host_words() {
  use crate::library::io::StreamAdvice;
  let (program, artifact) = arena_reader();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let advice = reader_advice(&program);
  let mut channels = crate::hints::HintChannels::new();
  advice.register_read::<1>("read1", true, &mut channels).unwrap();
  advice.register_read::<2>("read2", false, &mut channels).unwrap();
  let hints = program.prepare_hint_channels(&[], &channels).unwrap();
  let plans = DevicePlans::new(&backend);
  let root = backend.names.iter().position(|n| n == "root").unwrap();
  assert!(plans.circuits[root], "arena reads are device-encodable");
  // Every in-range read of one value and of a pair: byte arena, its last
  // byte, the word arena and the byte read before it widened.
  for args in [vec![0, 0], vec![0, 1], vec![0, 2], vec![2, 0], vec![2, 1]] {
    let record = hints.execute("root", args.clone()).unwrap();
    assert!(plans.supports(&record, root));
    let expected = backend
      .generate_stage_1(&record, "root", &args)
      .unwrap()
      .into_iter()
      .map(|m| {
        m.values.iter().map(|v| v.as_canonical_u64()).collect::<Vec<_>>()
      })
      .collect::<Vec<_>>();
    let rows = backend.record_rows(&record).unwrap();
    let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
    let height = device.height(root).unwrap();
    let tile = |device: &DeviceRecord| {
      device
        .tile_words(root, None, 0, 0, height, height, rows[root], GARBAGE)
        .unwrap()
    };
    assert_eq!(tile(&device), expected[root], "read at {args:?}");
    device.release(0);
    assert_eq!(tile(&device), expected[root], "read at {args:?} after release");
  }
}

/// Arena data a device reads, shorter than what its channel's provider
/// answers from: the device must reject the reads the data lacks.
struct Truncated(Vec<u8>);

impl crate::hints::DeviceArenas for Truncated {
  fn arenas(&self) -> Vec<crate::hints::ArenaData<'_>> {
    vec![
      crate::hints::ArenaData::Bytes(&self.0),
      crate::hints::ArenaData::Bytes(&[]),
    ]
  }
  fn identity(&self) -> *const () {
    self.0.as_ptr().cast()
  }
}

/// The device fails a read past its arena's end, of a pair straddling the
/// end, from an empty arena and from an arena past the last, as the host
/// provider fails reads its data lacks.
#[test]
fn arena_reads_out_of_range_fail_on_the_device() {
  let (program, artifact) = arena_reader();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let pair = Type::Tuple { items: vec![Type::Field; 2] };
  let mut channels = crate::hints::HintChannels::new();
  channels
    .insert_fixed::<2, 1>("read1", pair.clone(), Type::Field, |[_, o]| Ok([o]))
    .unwrap();
  channels
    .insert_fixed::<2, 2>("read2", pair.clone(), pair, |[_, o]| Ok([o, o]))
    .unwrap();
  let data: std::sync::Arc<dyn crate::hints::DeviceArenas> =
    std::sync::Arc::new(Truncated(vec![0, 1, 2]));
  channels.set_device_arenas("read1", data.clone()).unwrap();
  channels.set_device_arenas("read2", data).unwrap();
  let hints = program.prepare_hint_channels(&[], &channels).unwrap();
  let plans = DevicePlans::new(&backend);
  let root = backend.names.iter().position(|n| n == "root").unwrap();
  for (args, ok) in [
    (vec![0, 1], true),
    (vec![0, 2], false),
    (vec![0, 3], false),
    (vec![0, Val::ORDER_U64 - 1], false),
    (vec![1, 0], false),
    (vec![2, 0], false),
    (vec![Val::ORDER_U64 - 1, 0], false),
  ] {
    let record = hints.execute("root", args.clone()).unwrap();
    let rows = backend.record_rows(&record).unwrap();
    let device = DeviceRecord::upload(&backend, &plans, &record, 0).unwrap();
    let height = device.height(root).unwrap();
    let tile =
      device.tile_words(root, None, 0, 0, height, height, rows[root], GARBAGE);
    match tile {
      Ok(_) => assert!(ok, "read at {args:?} passed"),
      Err(error) => {
        assert!(!ok, "read at {args:?}: {error}");
        assert!(error.contains("invalid hint input"), "{error}");
      },
    }
  }
}

/// A record whose reads are bound to hint data rather than device arenas
/// keeps the reading circuit on the host, with the cause reported.
#[test]
fn arena_reads_without_device_data_stay_on_the_host() {
  let (program, artifact) = arena_reader();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let mut backend =
    Backend::build_with_lookup_policy(&plan, parameters(), true, None, true)
      .unwrap();
  let entries: Vec<crate::hints::HintEntry> = serde_json::from_value(json!([
    {"channel":"read1","type":f(),"key_type":{"kind":"tuple","items":[f(),f()]},
     "key":[0,0],"output":[5]},
    {"channel":"read2","type":{"kind":"tuple","items":[f(),f()]},
     "key_type":{"kind":"tuple","items":[f(),f()]},"key":[0,0],"output":[5,6]}]))
  .unwrap();
  let record =
    program.execute_with_hints("root", vec![0, 0], &entries).unwrap();
  let plans = DevicePlans::new(&backend);
  let root = backend.names.iter().position(|n| n == "root").unwrap();
  assert!(plans.circuits[root]);
  assert!(!plans.supports(&record, root));
  assert!(!plans.enabled(&record)[root]);
  backend.device_plans = Some(plans);
  let options =
    planning::Options { max_ram_bytes: Some(1 << 30), ..Default::default() };
  let report = backend.plan_record(&record, &options, 0).unwrap().population;
  assert_eq!(report[root].host_causes, [HostCause::UnsupportedHint]);
  assert!(!report[root].generated);
}
