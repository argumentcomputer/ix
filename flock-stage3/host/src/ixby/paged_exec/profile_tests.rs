//! Streaming native census and bounded address-only windows for quota tuning.
//! These records omit witness values and do not establish execution proofs.
use super::*;
use crate::ixby::{
  ixbf::{self, DecodeLimits, Scalar, ValueKind},
  memory_log::MemoryBatch,
  paged_frame::Phase,
};
use anyhow::{Context, Result, ensure};
use quota_tests::{CountedRow, Trace};
use std::{
  fs::{File, OpenOptions},
  io::{BufReader, BufWriter, Read, Write},
  path::{Path, PathBuf},
  time::Instant,
};

const MAGIC: &[u8; 8] = b"IXQP0001";

fn option(name: &str, default: u64, low: u64, high: u64) -> u64 {
  let value = std::env::var(name)
    .map_or(default, |s| s.parse().expect("unsigned profile option"));
  assert!((low..=high).contains(&value), "{name} outside profile bounds");
  value
}

fn write_window(
  directory: &Path,
  sources: [[u8; 32]; 2],
  clock: u64,
  rows: &[CountedRow],
) -> Result<()> {
  ensure!(!rows.is_empty(), "empty quota window");
  let name = format!("window-{clock:012}.ixqp");
  let file = OpenOptions::new()
    .write(true)
    .create_new(true)
    .open(directory.join(&name))?;
  let mut out = BufWriter::new(file);
  out.write_all(MAGIC)?;
  for digest in sources {
    out.write_all(&digest)?;
  }
  for n in [clock, rows[0].logical_before, rows.len() as u64] {
    out.write_all(&n.to_le_bytes())?;
  }
  let mut logical = rows[0].logical_before;
  for row in rows {
    ensure!(row.logical_before == logical, "window fuel discontinuity");
    let charged =
      row.logical_after.checked_sub(logical).context("fuel decreased")?;
    ensure!(charged <= 1, "more than one logical step in a microstep");
    ensure!(row.addresses.len() == row.chip.accesses(), "window access width");
    out.write_all(&[
      row.chip as u8,
      charged as u8,
      row.addresses.len() as u8,
    ])?;
    for address in &row.addresses {
      out.write_all(&address.to_le_bytes())?;
    }
    logical = row.logical_after;
  }
  out.flush()?;
  eprintln!(
    "native_profile_window,{name},{clock},{},{},{logical}",
    clock + rows.len() as u64,
    rows[0].logical_before
  );
  Ok(())
}

pub(super) fn read_window(
  path: &Path,
  sources: [[u8; 32]; 2],
) -> Result<(u64, Trace)> {
  let mut input = BufReader::new(File::open(path)?);
  let mut magic = [0; 8];
  input.read_exact(&mut magic)?;
  ensure!(&magic == MAGIC, "quota window version");
  for expected in sources {
    let mut actual = [0; 32];
    input.read_exact(&mut actual)?;
    ensure!(actual == expected, "quota window artifact binding");
  }
  let mut number = || -> Result<u64> {
    let mut bytes = [0; 8];
    input.read_exact(&mut bytes)?;
    Ok(u64::from_le_bytes(bytes))
  };
  let clock = number()?;
  let mut logical = number()?;
  let length = number()?;
  ensure!((1..=1_000_000).contains(&length), "quota window row bound");
  ensure!(clock < (1 << 59) - length, "quota window clock domain");
  let mut rows = Vec::with_capacity(length as usize);
  let mut counts = [0; 31];
  for _ in 0..length {
    let mut header = [0; 3];
    input.read_exact(&mut header)?;
    let chip =
      *Chip::ALL.get(header[0] as usize).context("quota window chip")?;
    ensure!(header[1] <= 1, "quota window fuel charge");
    ensure!(header[2] as usize == chip.accesses(), "quota window accesses");
    let mut addresses = Vec::with_capacity(chip.accesses());
    for _ in 0..chip.accesses() {
      let mut bytes = [0; 8];
      input.read_exact(&mut bytes)?;
      let address = u64::from_le_bytes(bytes);
      ensure!(address < 1 << 40, "quota window address domain");
      addresses.push(address);
    }
    let after = logical
      .checked_add(u64::from(header[1]))
      .context("window fuel overflow")?;
    rows.push(CountedRow {
      chip,
      logical_before: logical,
      logical_after: after,
      addresses,
    });
    logical = after;
    counts[chip as usize] += 1;
  }
  ensure!(input.read(&mut [0])? == 0, "trailing quota window bytes");
  let name = format!("window-{clock:012}");
  Ok((clock, Trace { name, rows, counts, halted: false }))
}

#[derive(Default)]
struct FunctionCounts {
  chips: [u64; 31],
  reads: u64,
  writes: u64,
  zero_accesses: u64,
  heap_cells: u64,
  byte_cells: u64,
  first_clock: Option<u64>,
}
impl FunctionCounts {
  fn observe(&mut self, row: &RowAdvice) {
    self.first_clock.get_or_insert(row.clock);
    self.chips[row.chip as usize] += 1;
    self.reads += row.accesses.iter().filter(|a| !a.write).count() as u64;
    self.writes += row.accesses.iter().filter(|a| a.write).count() as u64;
    self.zero_accesses +=
      row.accesses.iter().filter(|a| a.address == 0).count() as u64;
    self.heap_cells += row.after[HEAP_COUNT].lo - row.before[HEAP_COUNT].lo;
    self.byte_cells += row.after[BYTE_COUNT].lo - row.before[BYTE_COUNT].lo;
  }
}

fn expected_bytes<'a>(
  program: &ixbf::Artifact<'_>,
  output: &'a [u8],
) -> Result<&'a [u8]> {
  let decoded = ixbf::decode_output(program, output, DecodeLimits::default())?;
  let forest = decoded.values();
  ensure!(forest.roots().len() == 1, "profile requires one output root");
  match forest.nodes()[forest.roots()[0]].kind {
    ValueKind::Scalar(Scalar::Bytes(bytes)) => Ok(bytes),
    _ => anyhow::bail!("profile output comparison currently requires Bytes"),
  }
}

fn check_output(
  machine: &NativeMachine,
  memory: &MemoryBatch<'_>,
  expected: &[u8],
) -> Result<()> {
  ensure!(
    machine.state[0] == F128::new(Phase::Halted as u64, 0),
    "profile did not halt"
  );
  ensure!(machine.state[2] == F128::new(6, 0), "profile result is not Bytes");
  let value = machine.state[3];
  ensure!(value.hi == expected.len() as u64, "profile output length mismatch");
  for (i, &expected) in expected.iter().enumerate() {
    let pointer =
      value.lo.checked_add(i as u64).context("output pointer overflow")?;
    let cell = memory.value(pointer >> 5)?;
    let words = [cell[0].lo, cell[0].hi, cell[1].lo, cell[1].hi];
    let actual =
      (words[((pointer & 31) >> 3) as usize] >> ((pointer & 7) * 8)) as u8;
    ensure!(actual == expected, "profile output differs at byte {i}");
  }
  Ok(())
}

#[test]
#[ignore = "streaming native census over caller-supplied original artifacts; no proofs"]
fn streaming_native_execution_profile() -> Result<()> {
  let directory = PathBuf::from(
    std::env::var_os("IXBY_PROFILE_FIXTURE").context("profile fixture")?,
  );
  let out = PathBuf::from(
    std::env::var_os("IXBY_PROFILE_OUT").context("profile output directory")?,
  );
  std::fs::create_dir(&out)?;
  let limit =
    option("IXBY_PROFILE_MICROSTEP_LIMIT", 16_000_000_000, 1, 16_000_000_000);
  let stride =
    option("IXBY_PROFILE_WINDOW_STRIDE", 5_000_000, 1_000, 1_000_000_000);
  let sample_rows =
    option("IXBY_PROFILE_WINDOW_ROWS", 100_000, 1_000, 1_000_000).min(stride);
  let progress_stride =
    option("IXBY_PROFILE_PROGRESS", 1_000_000, 1_000, 100_000_000);
  let program = std::fs::read(directory.join("program.ixby"))?;
  let input = std::fs::read(directory.join("input.ixbi"))?;
  let output = std::fs::read(directory.join("output.ixbo"))?;
  let sources = [&program, &input].map(|b| *blake3::hash(b).as_bytes());
  let artifact = ixbf::decode_program(&program, DecodeLimits::default())?;
  let expected = expected_bytes(&artifact, &output)?;
  let mut blocks = artifact
    .functions()
    .iter()
    .map(|f| vec![0u64; f.blocks.len()])
    .collect::<Vec<_>>();
  let mut functions =
    (0..=blocks.len()).map(|_| FunctionCounts::default()).collect::<Vec<_>>();
  let started = Instant::now();
  let mut image = NativeImage::load(&program, &input, DecodeLimits::default())?;
  let mut machine = image.machine()?;
  machine.compare_native_advice =
    std::env::var_os("IXBY_PROFILE_COMPARE").is_some();
  let mut memory = MemoryBatch::new(&mut image.memory);
  let mut counts = [0u64; 31];
  let timed = std::env::var_os("IXBY_PROFILE_TIME_CHIPS").is_some();
  let mut nanoseconds = [0u64; 31];
  let mut phases = [0u64; 5];
  let mut sample = Vec::with_capacity(sample_rows as usize);
  eprintln!(
    "native_profile_source,{},{},{},{},{}",
    blake3::hash(&program),
    blake3::hash(&input),
    blake3::hash(&output),
    image.cell_count,
    blocks.len()
  );
  while machine.clock < limit && machine.next_chip()?.is_some() {
    let step_started = timed.then(Instant::now);
    let row = machine.step(&mut memory).with_context(|| {
      format!(
        "profile microstep {} logical {}",
        machine.clock, machine.state[FUEL].hi
      )
    })?;
    if let Some(started) = step_started {
      nanoseconds[row.chip as usize] += started.elapsed().as_nanos() as u64;
    }
    memory.discard_profile_accesses();
    counts[row.chip as usize] += 1;
    let phase = row.before[0].lo as u8;
    let function = if phase == Phase::Eval as u8 || phase == Phase::Copy as u8 {
      ((row.before[0].lo >> 8) & 65535) as usize
    } else {
      blocks.len()
    };
    ensure!(function <= blocks.len(), "profile function domain");
    functions[function].observe(&row);
    if row.chip == Chip::Fetch {
      let block = ((row.before[0].lo >> 24) & 255) as usize;
      *blocks
        .get_mut(function)
        .and_then(|f| f.get_mut(block))
        .context("profile block domain")? += 1;
    }
    let charged = row.after[FUEL].hi - row.before[FUEL].hi;
    ensure!(
      charged <= 1 && (phase as usize) < phases.len(),
      "profile fuel/phase domain"
    );
    phases[phase as usize] += charged;
    if row.clock % stride < sample_rows {
      sample.push(CountedRow::from(&row));
      if sample.len() == sample_rows as usize {
        write_window(&out, sources, row.clock + 1 - sample_rows, &sample)?;
        sample.clear();
      }
    }
    if machine.clock.is_multiple_of(progress_stride) {
      eprintln!(
        "native_profile_progress,{},{},{},{},{},{:.9},{counts:?}",
        machine.clock,
        machine.state[FUEL].hi,
        machine.state[HEAP_COUNT].lo,
        machine.state[BYTE_COUNT].lo,
        memory.profile_cells(),
        started.elapsed().as_secs_f64()
      );
      if timed {
        eprintln!("native_profile_timing,{},{nanoseconds:?}", machine.clock);
      }
    }
  }
  if !sample.is_empty() {
    write_window(&out, sources, machine.clock - sample.len() as u64, &sample)?;
  }
  let halted = machine.next_chip()?.is_none();
  if halted {
    check_output(&machine, &memory, expected)?;
    if let Ok(steps) = std::env::var("IXBY_PROFILE_EXPECTED_STEPS") {
      ensure!(
        machine.state[FUEL].hi == steps.parse::<u64>()?,
        "reference transition mismatch"
      );
    }
  }
  for (i, function) in functions.iter().enumerate() {
    eprintln!(
      "native_profile_function,{i},{},{},{},{},{},{},{:?}",
      function.first_clock.map_or_else(|| "none".into(), |n| n.to_string()),
      function.reads,
      function.writes,
      function.zero_accesses,
      function.heap_cells,
      function.byte_cells,
      function.chips
    );
  }
  for (i, counts) in blocks.iter().enumerate() {
    eprintln!("native_profile_blocks,{i},{counts:?}");
  }
  eprintln!(
    "native_profile_complete,{halted},{},{},{},{},{},{:.9},{phases:?},{counts:?}",
    machine.clock,
    machine.state[FUEL].hi,
    machine.state[HEAP_COUNT].lo,
    machine.state[BYTE_COUNT].lo,
    memory.profile_cells(),
    started.elapsed().as_secs_f64()
  );
  if timed {
    eprintln!("native_profile_timing,{},{nanoseconds:?}", machine.clock);
  }
  Ok(())
}

#[test]
#[ignore = "replay bounded address-only windows into exact quota and circuit counters; no proofs"]
fn captured_window_quota_census() -> Result<()> {
  let fixture = PathBuf::from(
    std::env::var_os("IXBY_PROFILE_FIXTURE").context("profile fixture")?,
  );
  let directory = PathBuf::from(
    std::env::var_os("IXBY_PROFILE_OUT").context("profile output directory")?,
  );
  let sources = ["program.ixby", "input.ixbi"]
    .map(|name| std::fs::read(fixture.join(name)))
    .into_iter()
    .collect::<std::io::Result<Vec<_>>>()?;
  let sources: [[u8; 32]; 2] = sources
    .iter()
    .map(|b| *blake3::hash(b).as_bytes())
    .collect::<Vec<_>>()
    .try_into()
    .unwrap();
  let starts = std::env::var("IXBY_PROFILE_WINDOW_STARTS")
    .context("comma-separated window starts")?;
  let starts = starts
    .split(',')
    .map(|s| s.parse::<u64>())
    .collect::<std::result::Result<Vec<_>, _>>()?;
  ensure!((1..=64).contains(&starts.len()), "quota window selection bound");
  let mut traces = Vec::new();
  for clock in starts {
    let (actual, trace) = read_window(
      &directory.join(format!("window-{clock:012}.ixqp")),
      sources,
    )?;
    ensure!(actual == clock, "quota window clock binding");
    let last = trace.rows.last().unwrap();
    eprintln!(
      "quota_trace,{},{},{},0.0,{:?},{},{}",
      trace.name,
      trace.rows.len(),
      last.logical_after,
      trace.counts,
      blake3::Hash::from(sources[0]),
      blake3::Hash::from(sources[1])
    );
    eprintln!(
      "quota_source_range,{},{},{},{},{}",
      trace.name,
      clock,
      clock + trace.rows.len() as u64,
      trace.rows[0].logical_before,
      last.logical_after
    );
    traces.push(trace);
  }
  for class in BatchClass::ALL.into_iter().filter(|class| {
    *class == BatchClass::SharedLinked1024
      || (!class.fused() && tuning::shape(*class).is_some())
  }) {
    quota_tests::census(
      class.name(),
      batch::BatchShape::from_class(class),
      &traces,
    );
  }
  if std::env::var_os("IXBY_QUOTA_NAMED_ONLY").is_some() {
    return Ok(());
  }
  let training = std::env::var("IXBY_QUOTA_TRAINING_STARTS").ok();
  let training = training.as_ref().map(|s| {
    s.split(',')
      .map(|v| v.parse::<u64>().expect("training clock"))
      .collect::<Vec<_>>()
  });
  let counts = if let Some(starts) = &training {
    ensure!(!starts.is_empty(), "empty training set");
    let mut counts = [0; 31];
    counts[0] = 1_000_000;
    for clock in starts {
      let name = format!("window-{clock:012}");
      let trace = traces
        .iter()
        .find(|t| t.name == name)
        .context("training window not selected")?;
      ensure!(
        trace.counts[0] > 0,
        "training window needs an instruction fetch"
      );
      for (total, n) in counts.iter_mut().zip(trace.counts) {
        *total = (*total).max((n * 1_000_000).div_ceil(trace.counts[0]));
      }
    }
    vec![("training".to_owned(), counts)]
  } else {
    traces.iter().map(|t| (t.name.clone(), t.counts)).collect()
  };
  for fetch in [1024, 2048, 3072] {
    for (name, counts) in &counts {
      let mut quotas = quota_tests::candidate_quotas(*counts, fetch);
      let bulk = std::env::var_os("IXBY_QUOTA_BULK").is_some();
      if bulk {
        for (chip, quota) in [
          (Chip::BuilderNode, fetch / 8),
          (Chip::BuilderCopy, 3 * fetch / 8),
          (Chip::BuilderEmit, 3 * fetch / 8),
          (Chip::HashBlock, fetch / 32),
          (Chip::ByteEq, fetch / 32),
        ] {
          quotas[chip as usize] = quotas[chip as usize].max(quota);
        }
      }
      for cells in [1024, 1536, 2048] {
        for parents in [4095, 6143, 8191] {
          quota_tests::census(
            &format!(
              "{name}{}-{fetch}-{cells}-{parents}",
              if bulk { "-bulk" } else { "" }
            ),
            batch::BatchShape {
              quotas,
              fused: [0; Chip::FUSED.len()],
              cells,
              parents: Some(parents),
              nu: 19,
            },
            &traces,
          );
        }
      }
    }
  }
  Ok(())
}
