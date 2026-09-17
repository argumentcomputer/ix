//! Opt-in count-only quota sweep over independently executed native traces.
//! Candidate shapes never enter the production class parser or verifier.
use super::*;
use crate::{
  ixby::{
    auth_memory::MemoryDepth,
    execution_order::StateChainSlots,
    ixbf::DecodeLimits,
    memory_log::{MemoryBatch, MemoryLogSlots, shared_parent_count},
  },
  sizing::CountingEmitter,
};
use batch::BatchShape;
use flock_prover::union::UnionInstance;
use std::{collections::BTreeSet, path::Path, time::Instant};

#[test]
fn every_named_execution_class_fits_its_exact_emission() {
  let mut names = BTreeSet::new();
  let mut domains = BTreeSet::new();
  for class in BatchClass::ALL {
    assert!(names.insert(class.name()));
    assert!(domains.insert(class.transcript_domain()));
    assert_eq!(BatchClass::from_name(class.name()).unwrap(), class);
    let mut count = CountingEmitter::new();
    emit_batch(&mut count, class).unwrap();
    let required = count.required_nu(3).unwrap();
    assert!(
      required <= class.nu(),
      "{class:?} needs nu {required}, has {}",
      class.nu()
    );
  }
  assert!(BatchClass::from_name("unapproved-quota-shape").is_err());
}

/// Only addresses and fuel are needed for quota counting. This deliberately
/// omits values and full states and cannot serve as execution proof advice.
pub(super) struct CountedRow {
  pub chip: Chip,
  pub logical_before: u64,
  pub logical_after: u64,
  pub addresses: Vec<u64>,
}
impl From<&RowAdvice> for CountedRow {
  fn from(row: &RowAdvice) -> Self {
    Self {
      chip: row.chip,
      logical_before: row.before[FUEL].hi,
      logical_after: row.after[FUEL].hi,
      addresses: row.accesses.iter().map(|a| a.address).collect(),
    }
  }
}
pub(super) struct Trace {
  pub name: String,
  pub rows: Vec<CountedRow>,
  pub counts: [usize; 31],
  pub halted: bool,
}
fn trace(name: &str, directory: &Path, skip: usize, limit: usize) -> Trace {
  let program = std::fs::read(directory.join("program.ixby")).unwrap();
  let input = std::fs::read(directory.join("input.ixbi")).unwrap();
  let started = Instant::now();
  let mut image =
    NativeImage::load(&program, &input, DecodeLimits::default()).unwrap();
  let mut machine = image.machine().unwrap();
  machine.compare_native_advice = false;
  let mut memory = MemoryBatch::new(&mut image.memory);
  for _ in 0..skip {
    machine.step(&mut memory).expect("holdout starts before halt");
    memory.discard_profile_accesses();
  }
  let initial_clock = machine.clock;
  let initial_fuel = machine.state[FUEL].hi;
  let mut rows = Vec::new();
  let mut counts = [0; 31];
  while rows.len() < limit && machine.next_chip().unwrap().is_some() {
    let row = machine.step(&mut memory).unwrap();
    counts[row.chip as usize] += 1;
    rows.push(CountedRow::from(&row));
    memory.discard_profile_accesses();
  }
  assert!(!rows.is_empty());
  eprintln!(
    "quota_trace,{name},{},{},{:.9},{counts:?},{},{}",
    rows.len(),
    machine.state[FUEL].hi,
    started.elapsed().as_secs_f64(),
    blake3::hash(&program),
    blake3::hash(&input)
  );
  eprintln!(
    "quota_source_range,{name},{initial_clock},{},{initial_fuel},{}",
    machine.clock, machine.state[FUEL].hi
  );
  let halted = machine.next_chip().unwrap().is_none();
  Trace { name: name.into(), rows, counts, halted }
}

/// Keep a positive fallback quota for every family. A class may suspend an
/// instruction, but it must always admit its next microstep in a fresh leaf.
pub(super) fn candidate_quotas(
  counts: [usize; 31],
  fetch: usize,
) -> [usize; 31] {
  let scale = fetch.div_ceil(1024);
  let floor = fetch.div_ceil(128);
  let mut quotas = [floor; 31];
  quotas[0] = fetch;
  let target: Vec<_> = counts[1..]
    .iter()
    .map(|&n| (n * fetch).div_ceil(counts[0].max(1)).max(floor))
    .collect();
  let available = 8192 * scale - 1 - fetch - 30 * floor;
  let wanted: usize = target.iter().map(|&n| n - floor).sum();
  for (quota, n) in quotas[1..].iter_mut().zip(target) {
    *quota = floor + (n - floor) * available.min(wanted) / wanted.max(1);
  }
  assert!(quotas.iter().all(|&n| n > 0));
  assert!(quotas.iter().sum::<usize>() < 8192 * scale);
  quotas
}

fn sample(
  trace: &Trace,
  shape: BatchShape,
  complete: Option<BatchClass>,
) -> (usize, u64) {
  let mut at = 0;
  let mut batches = 0;
  let mut complete_rows = 0;
  let mut complete_logical = 0;
  let mut complete_fetch = 0;
  let mut stops = [0; 33]; // 31 chip families, distinct cells, parents.
  let mut max_cells = 0;
  let mut max_parents = 0;
  while at < trace.rows.len() {
    let first = at;
    let mut counts = [0; 31];
    let mut addresses = BTreeSet::new();
    let mut parents = 0;
    while let Some(row) = trace.rows.get(at) {
      if counts[row.chip as usize] == shape.quotas[row.chip as usize] {
        stops[row.chip as usize] += 1;
        break;
      }
      let added: Vec<_> = row
        .addresses
        .iter()
        .copied()
        .filter(|a| !addresses.contains(a))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
      if addresses.len() + added.len() > shape.cells {
        stops[31] += 1;
        break;
      }
      if !added.is_empty() {
        let next = shared_parent_count(
          MemoryDepth::new(40).unwrap(),
          addresses.iter().copied().chain(added.iter().copied()).collect(),
          shape.cells,
        )
        .unwrap();
        if next > shape.parents.unwrap() {
          stops[32] += 1;
          break;
        }
        parents = next;
        addresses.extend(added);
      }
      counts[row.chip as usize] += 1;
      at += 1;
    }
    assert!(at > first, "candidate cannot make progress");
    max_cells = max_cells.max(addresses.len());
    max_parents = max_parents.max(parents);
    // Exclude truncated trace tails from occupancy averages. Complete-run
    // leaf counts include the last, potentially partly occupied, leaf.
    if at < trace.rows.len() || complete.is_some() {
      if let Some(class) = complete {
        eprintln!(
          "full_execution_batch,{},{},{batches},{first},{at},{},{}",
          trace.name,
          class.name(),
          trace.rows[first].logical_before,
          trace.rows[at - 1].logical_after
        );
      }
      batches += 1;
      complete_rows += at - first;
      complete_fetch += counts[Chip::Fetch as usize];
      complete_logical +=
        trace.rows[at - 1].logical_after - trace.rows[first].logical_before;
    }
  }
  eprintln!(
    "quota_sample,{},{batches},{complete_rows},{complete_logical},{complete_fetch},{max_cells},{max_parents},{stops:?}",
    trace.name
  );
  (batches, complete_logical)
}

pub(super) fn census(name: &str, shape: BatchShape, traces: &[Trace]) {
  let started = Instant::now();
  let mut count = CountingEmitter::new();
  batch::emit_shape(&mut count, BatchClass::SharedLinked1024, shape).unwrap();
  let required_nu = count.required_nu(3).unwrap();
  if required_nu > shape.nu {
    eprintln!("quota_capacity_mismatch,{name},{},{required_nu}", shape.nu);
    for (table, rows) in count.table_rows() {
      eprintln!("quota_table,{name},{table},{rows}");
    }
  }
  let (registry, counts) = count.registry(required_nu);
  let union = UnionInstance::new(&registry, counts);
  let state = StateChainSlots::linked_plan(shape.transitions()).unwrap();
  let memory = MemoryLogSlots::plan(shape.accesses(), shape.cells).unwrap();
  let tree = shape.shared_memory().unwrap().plan();
  eprintln!(
    "quota_shape,{name},{},{},{},{},{required_nu},{},{},{},{},{},{},{},{:.9},{:?}",
    shape.transitions(),
    shape.accesses(),
    shape.cells,
    shape.parents.unwrap(),
    state.lanes(),
    memory.lanes(),
    tree.lanes(),
    union.dense_m(),
    union.dense_words(),
    union.committed_words(),
    state.switches() + memory.switches() + tree.switches(),
    started.elapsed().as_secs_f64(),
    shape.quotas
  );
  for trace in traces {
    sample(trace, shape, None);
  }
}

#[test]
#[ignore = "complete independent fixtures; native execution and exact leaf/join counts, no proofs"]
fn physical_batch_complete_counts() {
  let root = std::env::var_os("IXBY_QUOTA_FIXTURES").unwrap();
  let root = Path::new(&root);
  for (name, classes) in [
    (
      "arithmetic",
      vec![
        BatchClass::SharedLinked1024,
        BatchClass::Arithmetic768,
        BatchClass::Arithmetic3072,
        BatchClass::Arithmetic4096,
      ],
    ),
    ("arrays", vec![BatchClass::SharedLinked1024, BatchClass::Arrays768]),
    ("bytes", vec![BatchClass::SharedLinked1024, BatchClass::Builders768]),
  ] {
    let trace = trace(name, &root.join(name), 0, 1_000_000);
    assert!(trace.halted, "fixture did not halt within census bound");
    for class in classes {
      let (leaves, logical) =
        sample(&trace, BatchShape::from_class(class), Some(class));
      assert_eq!(
        logical,
        trace.rows.last().unwrap().logical_after
          - trace.rows.first().unwrap().logical_before
      );
      eprintln!(
        "full_execution_count,{name},{},{},{leaves},{logical},{}",
        class.name(),
        trace.rows.len(),
        leaves - 1
      );
    }
  }
}

#[test]
#[ignore = "requires independent fixtures; exact emission census and native quota/padding sweep, no proofs"]
fn physical_batch_quota_sweep() {
  let root = std::env::var_os("IXBY_QUOTA_FIXTURES").unwrap();
  let root = Path::new(&root);
  let limit = std::env::var("IXBY_QUOTA_MICROSTEPS")
    .map_or(100_000, |s| s.parse::<usize>().unwrap());
  assert!((1_000..=1_000_000).contains(&limit));
  let skip = std::env::var("IXBY_QUOTA_SKIP_MICROSTEPS")
    .map_or(0, |s| s.parse::<usize>().unwrap());
  assert!(skip <= 1_000_000);
  let mut traces: Vec<_> = ["arithmetic", "arrays", "bytes"]
    .into_iter()
    .map(|name| trace(name, &root.join(name), skip, limit))
    .collect();
  if let Some(directory) = std::env::var_os("IXBY_QUOTA_RETAINED") {
    traces.push(trace("retained", Path::new(&directory), skip, limit));
  }
  if std::env::var_os("IXBY_QUOTA_NAMED_ONLY").is_some() {
    for class in BatchClass::ALL.into_iter().filter(|class| {
      *class == BatchClass::SharedLinked1024 || tuning::shape(*class).is_some()
    }) {
      census(class.name(), BatchShape::from_class(class), &traces);
    }
    return;
  }
  census(
    "baseline",
    BatchShape::from_class(BatchClass::SharedLinked1024),
    &traces,
  );
  let fetch_counts = std::env::var("IXBY_QUOTA_FETCH")
    .unwrap_or_else(|_| "1024,4096".into())
    .split(',')
    .map(|s| s.parse::<usize>().unwrap())
    .collect::<Vec<_>>();
  assert!(fetch_counts.iter().all(|n| (256..=4096).contains(n)));
  for fetch in fetch_counts {
    let scale = fetch.div_ceil(1024);
    for trace in &traces {
      let quotas = candidate_quotas(trace.counts, fetch);
      for cells in [512, 1024, 2048].map(|n| n * scale) {
        for parents in [1024, 2048, 4096, 8192].map(|n| n * scale - 1) {
          if parents < cells + 64 {
            continue;
          }
          census(
            &format!("{}-{fetch}-{cells}-{parents}", trace.name),
            BatchShape { quotas, cells, parents: Some(parents), nu: 19 },
            &traces,
          );
        }
      }
    }
  }
}
