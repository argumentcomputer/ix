//! The device interpreter's tiles, workspace pool, release and allowlist.
use super::super::gpu::{DevicePlans, DeviceRecord};
use super::*;
use planning::{HostCause, PopulationProvider};

const ENTRY: &str = "Grouped::run";

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
      device.tile_words(ci, 0, 0, height, height, rows[ci], GARBAGE).unwrap();
    assert_eq!(whole, expected[ci], "circuit {ci}");
    // A slice ending one row early zeroes the row it drops.
    let real = rows[ci] - 1;
    let short =
      device.tile_words(ci, 0, 0, height, height, real, GARBAGE).unwrap();
    let mut padded = expected[ci].clone();
    padded[real * width..].fill(0);
    assert_eq!(short, padded);
    // One-row tiles, then a lookup halo of `height + 1` rows that wraps.
    for first in 0..height {
      let tile =
        device.tile_words(ci, 0, first, 1, height, rows[ci], GARBAGE).unwrap();
      assert_eq!(tile, expected[ci][first * width..(first + 1) * width]);
    }
    let halo = device
      .tile_words(ci, 0, 1, height + 1, height, rows[ci], GARBAGE)
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
        device.tile_words(ci, 0, 0, height, height, rows[ci], GARBAGE).unwrap()
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
  assert!(!on.contains(&grouped));
  let all_bytes = all.record_bytes(&backend, &record).unwrap();
  backend.device_plans = Some(all);
  let full = report(&backend);
  for &ci in &on {
    assert_eq!(full[ci].provider, PopulationProvider::GpuInterpreter);
    assert!(full[ci].host_causes.is_empty());
  }
  assert_eq!(
    full[grouped].host_causes,
    [HostCause::Store, HostCause::Load, HostCause::IneligibleGroup]
  );
  assert!(full[grouped].reason.contains("Grouped::memory (store, load)"));
  let json = serde_json::to_value(&full[grouped]).unwrap();
  assert_eq!(json["provider"], "cpu");
  assert_eq!(json["host_causes"], json!(["store", "load", "ineligible_group"]));

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
  let none =
    DevicePlans::select(&backend, Some(&["Grouped::left".into()])).unwrap();
  assert!(device_circuits(&none).is_empty());
  assert!(DevicePlans::select(&backend, Some(&["Nope".into()])).is_err());
  backend.device_plans = Some(none);
  let none = report(&backend);
  assert_eq!(none[chosen].host_causes, [HostCause::NotSelected]);
  assert_eq!(
    none[grouped].host_causes,
    [HostCause::Store, HostCause::Load, HostCause::IneligibleGroup],
    "a selected but ineligible circuit reports its plans",
  );
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
