//! Explicit circuit ranges and bounded population from an immutable record.
use super::*;
use multi_stark::{
  batch::Retention,
  witness::{PreparedWitness, TraceSource},
};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

const MAX_SHARDS: usize = 65_536;

/// One population thread's reusable buffers.
struct Scratch<F> {
  scratch: Vec<F>,
  buffer: Vec<F>,
  /// A depth circuit's own row, before placement.
  source: Vec<F>,
  /// Gap limb counts of rows whose counts were already taken.
  ranges: RangeCounts,
}

impl<F> Default for Scratch<F> {
  fn default() -> Self {
    Self {
      scratch: Vec::new(),
      buffer: Vec::new(),
      source: Vec::new(),
      ranges: RangeCounts::default(),
    }
  }
}
/// Circuits listed by name in a [`PopulationReport`].
const TOP_CIRCUITS: usize = 15;

#[derive(
  Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize,
)]
pub struct CircuitSlice {
  pub first: usize,
  pub rows: usize,
  pub height: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ShardLayout {
  pub circuits: Vec<CircuitSlice>,
  pub fixed_counts: bool,
}

/// What planning a layout needs that does not depend on which circuits the
/// device populates ([`Backend::layout_terms`]).
pub(super) struct LayoutTerms {
  metadata: u128,
  shards: Vec<ShardTerms>,
}

struct ShardTerms {
  /// Main-trace cells of each circuit with rows in the shard.
  main: Vec<(usize, u128)>,
  committed: u128,
  population: u128,
  tallest: usize,
  max_rows: usize,
  cpu: u128,
  saved: u128,
  prep: u128,
  lookup: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchLayout {
  pub version: u32,
  pub shards: Vec<ShardLayout>,
  pub memory_intervals: Vec<(u64, u64, u64)>,
}

/// Host population time of one circuit of one shard, in thread-seconds of
/// its own work. Allocation requests a zeroed matrix; large ones come from
/// fresh zero pages, so most of their zeroing is paid on first touch: by
/// filling for real rows, and by the prover for padding rows that nothing
/// writes.
#[derive(Clone, Copy, Debug, Default)]
struct CircuitTime {
  allocation: Duration,
  fill: Duration,
}

/// Population time of one shard witness.
#[derive(Clone, Debug, Default)]
struct ShardTime {
  circuits: Vec<CircuitTime>,
  lookups: Duration,
  wall: Duration,
}

/// Where host population time went in an incremental proof. Shard and
/// round `wall_seconds` are elapsed time; allocation and fill seconds are
/// thread-seconds summed over circuits that populate concurrently.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PopulationReport {
  /// Whether witnesses were built one shard ahead of the prover.
  pub pipelined: bool,
  pub preparation_seconds: f64,
  /// Wall time of every shard witness build.
  pub population_seconds: f64,
  /// Time the prover waited for a witness: all of population when serial,
  /// the part proving did not hide when pipelined.
  pub stall_seconds: f64,
  pub rounds: Vec<PopulationTotals>,
  pub shards: Vec<PopulationTotals>,
  /// The slowest circuits, summed over shards and rounds.
  pub top_circuits: Vec<CircuitPopulation>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct PopulationTotals {
  pub round: usize,
  /// Absent from round totals.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub shard: Option<usize>,
  pub wall_seconds: f64,
  pub allocation_seconds: f64,
  pub fill_seconds: f64,
  pub lookup_seconds: f64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CircuitPopulation {
  pub circuit: String,
  pub seconds: f64,
  pub allocation_seconds: f64,
  pub fill_seconds: f64,
  /// Seconds in the first and, when regenerated, second proving round.
  pub round_seconds: Vec<f64>,
  /// Shards holding rows of this circuit.
  pub shards: usize,
  pub real_rows: u64,
  pub padded_cells: u64,
}

/// A proof from [`Backend::prove_incremental_timed`] and its timing.
pub struct IncrementalRun {
  pub proof: BatchProof,
  /// Preparation plus every witness build.
  pub trace_seconds: f64,
  /// Proving wall time, less the time it waited for witnesses.
  pub proving_seconds: f64,
  pub population: PopulationReport,
}

#[derive(Clone)]
struct Member {
  function: usize,
  first: usize,
  end: usize,
}

/// Named phase times, for the `AIUR_POPULATION_REPORT` preparation line.
struct Phases {
  clock: Instant,
  done: Vec<(&'static str, f64)>,
}

impl Default for Phases {
  fn default() -> Self {
    Self { clock: Instant::now(), done: Vec::new() }
  }
}

impl Phases {
  fn lap(&mut self, name: &'static str) {
    self.done.push((name, self.clock.elapsed().as_secs_f64()));
    self.clock = Instant::now();
  }
}

/// What preparing a record needs from the host alone. Counts and spans
/// only: its size depends on the trace plan's tables, not the record's rows.
struct HostParts {
  /// The trace plan these parts were prepared on.
  plan: usize,
  /// The circuits the device was to populate, whose depth range uses
  /// `counts` leaves out.
  generated: Vec<bool>,
  counts: Vec<Vec<u64>>,
  members: Vec<Vec<Member>>,
  rows: Vec<usize>,
  phases: Vec<(&'static str, f64)>,
}

impl HostParts {
  fn retained_bytes(&self) -> usize {
    size_of::<Self>()
      + self.generated.len()
      + self
        .counts
        .iter()
        .map(|c| size_of::<Vec<u64>>() + size_of::<u64>() * c.len())
        .sum::<usize>()
      + self
        .members
        .iter()
        .map(|m| size_of::<Vec<Member>>() + size_of::<Member>() * m.len())
        .sum::<usize>()
      + size_of::<usize>() * self.rows.len()
      + size_of::<(&str, f64)>() * self.phases.len()
  }
}

/// A record and the host-only part of its preparation for one root call,
/// from [`Backend::prepare_host`].
pub struct HostPrepared<B: WitnessField> {
  record: Execution<B>,
  entry: String,
  args: Vec<B::Element>,
  parts: HostParts,
}

impl<B: WitnessField> HostPrepared<B> {
  pub fn record(&self) -> &Execution<B> {
    &self.record
  }

  pub fn into_record(self) -> Execution<B> {
    self.record
  }

  pub fn entry(&self) -> &str {
    &self.entry
  }

  pub fn args(&self) -> &[B::Element] {
    &self.args
  }

  /// Host bytes held beside the record.
  pub fn retained_bytes(&self) -> usize {
    self.parts.retained_bytes()
      + self.entry.len()
      + size_of_val(self.args.as_slice())
  }
}

/// An execution validated once for one backend; every shard supply reuses it
/// without revalidating the record.
pub struct PreparedRecord<'r, B: WitnessField> {
  record: &'r Execution<B>,
  backend_identity: std::sync::Arc<()>,
  counts: Vec<Vec<u64>>,
  members: Vec<Vec<Member>>,
  rows: Vec<usize>,
  #[cfg(feature = "cuda")]
  device: Option<std::sync::Arc<gpu::DeviceRecord>>,
}

fn ram_budget(options: &planning::Options) -> u64 {
  options
    .max_ram_bytes
    .or_else(planning::default_budget)
    .unwrap_or(8 << 30)
    .max(1)
}

fn padded(rows: usize) -> Result<usize, String> {
  if rows == 0 {
    Ok(0)
  } else {
    rows
      .checked_next_power_of_two()
      .ok_or_else(|| "trace height overflow".into())
  }
}

impl<B: WitnessField> Backend<'_, '_, B> {
  fn fixed_circuit(&self, ci: usize) -> bool {
    (self.members.len()..self.members.len() + self.tables.len()).contains(&ci)
  }

  /// Whether circuit `ci` is a fixed table, whose height never changes.
  pub fn is_fixed_table(&self, ci: usize) -> bool {
    self.fixed_circuit(ci)
  }

  pub fn record_rows(
    &self,
    record: &Execution<B>,
  ) -> Result<Vec<usize>, String> {
    self.plan.validate_record_shape(record)?;
    self.validated_record_rows(record)
  }

  /// [`Self::record_rows`] of a record whose shape is already validated.
  fn validated_record_rows(
    &self,
    record: &Execution<B>,
  ) -> Result<Vec<usize>, String> {
    let mut rows = self
      .members
      .iter()
      .map(|members| {
        members.iter().try_fold(0usize, |n, &f| {
          n.checked_add(record.queries.tables[f].len())
            .ok_or("circuit row count overflow")
        })
      })
      .collect::<Result<Vec<_>, _>>()?;
    rows.extend(
      self
        .system
        .circuits
        .iter()
        .skip(rows.len())
        .take(self.tables.len())
        .map(|c| c.preprocessed_height),
    );
    rows.extend(self.rom.widths.iter().map(|&width| {
      self
        .rom
        .row_count_for_entries(width, record.memory.width_cells(width).len())
    }));
    Ok(rows)
  }

  /// Preserve every padded slice of the common-row-cap producer.
  pub fn uniform_layout(
    &self,
    record: &Execution<B>,
    max_rows: usize,
  ) -> Result<BatchLayout, String> {
    if max_rows == 0 || !max_rows.is_power_of_two() {
      return Err("shard rows must be a positive power of two".into());
    }
    let rows = self.record_rows(record)?;
    let heights =
      rows.iter().map(|&n| padded(n)).collect::<Result<Vec<_>, _>>()?;
    let count = heights
      .iter()
      .enumerate()
      .filter(|(ci, _)| !self.fixed_circuit(*ci))
      .map(|(_, &h)| h.div_ceil(max_rows))
      .max()
      .unwrap_or(1)
      .max(1);
    if count > MAX_SHARDS {
      return Err("too many trace shards".into());
    }
    let mut shards = Vec::new();
    for i in 0..count {
      let first = i.checked_mul(max_rows).ok_or("shard offset overflow")?;
      let circuits = rows
        .iter()
        .zip(&heights)
        .enumerate()
        .map(|(ci, (&n, &h))| {
          if self.fixed_circuit(ci) {
            CircuitSlice { first: 0, rows: n, height: h }
          } else {
            CircuitSlice {
              first: first.min(n),
              rows: n.saturating_sub(first).min(max_rows),
              height: h.saturating_sub(first).min(max_rows),
            }
          }
        })
        .collect();
      shards.push(ShardLayout { circuits, fixed_counts: i == 0 });
    }
    let layout = BatchLayout {
      version: 1,
      shards,
      memory_intervals: self.record_shape(record)?.memory_intervals,
    };
    self.validate_layout(&rows, &layout)?;
    Ok(layout)
  }

  /// One trace shard with every circuit active at the log2 heights `logs`,
  /// in system circuit order. Fixed tables must keep their own heights.
  pub fn fixed_layout(
    &self,
    record: &Execution<B>,
    logs: &[u8],
  ) -> Result<BatchLayout, String> {
    let rows = self.record_rows(record)?;
    if logs.len() != rows.len() {
      return Err("fixed layouts need one log-height per circuit".into());
    }
    let circuits = rows
      .iter()
      .zip(logs)
      .enumerate()
      .map(|(ci, (&n, &log))| {
        let height = (log < 32)
          .then(|| 1usize << log)
          .ok_or("fixed log-height exceeds the Goldilocks domain")?;
        if self.fixed_circuit(ci) && height != n {
          return Err(format!(
            "circuit {ci} is a fixed table of {n} rows, not {height}"
          ));
        }
        if n > height {
          return Err(format!(
            "circuit {ci} needs {n} rows; the fixed layout allows {height}"
          ));
        }
        Ok(CircuitSlice { first: 0, rows: n, height })
      })
      .collect::<Result<Vec<_>, String>>()?;
    let layout = BatchLayout {
      version: 1,
      shards: vec![ShardLayout { circuits, fixed_counts: true }],
      memory_intervals: self.record_shape(record)?.memory_intervals,
    };
    self.validate_layout(&rows, &layout)?;
    Ok(layout)
  }

  fn committed_width(&self, ci: usize) -> u128 {
    let c = &self.system.circuits[ci];
    c.main_width as u128
      + c.stage_2_width as u128
      + 3 * c.quotient_degree() as u128
  }

  pub(super) fn packed_layout(
    &self,
    rows: &[usize],
    intervals: &[(u64, u64, u64)],
    cells: u128,
    max_rows: Option<usize>,
  ) -> Result<BatchLayout, String> {
    let fixed: u128 = rows
      .iter()
      .enumerate()
      .filter(|(ci, _)| self.fixed_circuit(*ci))
      .map(|(ci, &n)| n as u128 * self.committed_width(ci))
      .sum();
    let room =
      cells.checked_sub(fixed).ok_or("fixed tables exceed the cell budget")?;
    let domain_log = 32usize
      .checked_sub(self.parameters.log_blowup)
      .ok_or("invalid commitment blowup")?;
    let domain_rows = u32::try_from(domain_log)
      .ok()
      .and_then(|log| 1usize.checked_shl(log))
      .ok_or("trace domain overflow")?;
    let mut pieces = Vec::new();
    for (ci, &n) in rows.iter().enumerate() {
      if self.fixed_circuit(ci) || n == 0 {
        continue;
      }
      let fit = (room / self.committed_width(ci))
        .min(max_rows.unwrap_or(domain_rows).min(domain_rows) as u128)
        .min(usize::MAX as u128) as usize;
      if fit == 0 {
        return Err("one circuit row exceeds the cell budget".into());
      }
      let piece_rows = 1usize << fit.ilog2();
      if n.div_ceil(piece_rows) > MAX_SHARDS {
        return Err("too many trace shards".into());
      }
      let mut first = 0;
      while first < n {
        let len = (n - first).min(piece_rows);
        let slice = CircuitSlice { first, rows: len, height: padded(len)? };
        pieces.push((
          slice.height as u128 * self.committed_width(ci),
          ci,
          slice,
        ));
        first += len;
      }
    }
    pieces.sort_by_key(|&(cost, ci, slice)| {
      (std::cmp::Reverse(cost), ci, slice.first)
    });
    let mut shards: Vec<ShardLayout> = Vec::new();
    let mut loads: Vec<u128> = Vec::new();
    for (cost, ci, slice) in pieces {
      let index = shards
        .iter()
        .enumerate()
        .find_map(|(i, shard)| {
          (shard.circuits[ci].height == 0 && loads[i] + cost <= room)
            .then_some(i)
        })
        .unwrap_or(shards.len());
      if index == shards.len() {
        if index == MAX_SHARDS {
          return Err("too many trace shards".into());
        }
        shards.push(ShardLayout {
          circuits: vec![CircuitSlice::default(); rows.len()],
          fixed_counts: index == 0,
        });
        loads.push(0);
      }
      shards[index].circuits[ci] = slice;
      loads[index] += cost;
    }
    if shards.is_empty() {
      shards.push(ShardLayout {
        circuits: vec![CircuitSlice::default(); rows.len()],
        fixed_counts: true,
      });
    }
    for shard in &mut shards {
      for (ci, &n) in rows.iter().enumerate() {
        if self.fixed_circuit(ci) {
          shard.circuits[ci] = CircuitSlice { first: 0, rows: n, height: n };
        }
      }
    }
    let layout =
      BatchLayout { version: 1, shards, memory_intervals: intervals.to_vec() };
    self.validate_layout(rows, &layout)?;
    Ok(layout)
  }

  pub fn validate_layout(
    &self,
    rows: &[usize],
    layout: &BatchLayout,
  ) -> Result<(), String> {
    if layout.version != 1
      || rows.len() != self.system.circuits.len()
      || !(1..=MAX_SHARDS).contains(&layout.shards.len())
      || !layout.shards[0].fixed_counts
      || layout.shards.iter().filter(|s| s.fixed_counts).count() != 1
    {
      return Err("invalid batch layout".into());
    }
    let mut coverage = vec![Vec::new(); rows.len()];
    let mut lookup_budget = 1u128;
    for shard in &layout.shards {
      if shard.circuits.len() != rows.len() {
        return Err("wrong layout circuit count".into());
      }
      let mut active = Vec::new();
      let mut degrees = Vec::new();
      for (ci, (&slice, &n)) in shard.circuits.iter().zip(rows).enumerate() {
        let end =
          slice.first.checked_add(slice.rows).ok_or("slice end overflow")?;
        if end > n
          || slice.rows > slice.height
          || (slice.height != 0 && !slice.height.is_power_of_two())
        {
          return Err("invalid circuit slice".into());
        }
        if self.fixed_circuit(ci) {
          if slice != (CircuitSlice { first: 0, rows: n, height: n }) {
            return Err("fixed table slice changed".into());
          }
        } else if slice.rows != 0 {
          coverage[ci].push((slice.first, end));
        }
        active.push(slice.height != 0);
        if slice.height != 0 {
          degrees.push(
            u8::try_from(slice.height.ilog2())
              .map_err(|e| format!("trace height: {e}"))?,
          );
        }
        lookup_budget += slice.height as u128
          * self.system.circuits[ci].num_lookups.max(1) as u128;
      }
      self.check_shape(&active, &degrees)?;
    }
    if lookup_budget >= u128::from(Val::ORDER_U64) {
      return Err("batch height/lookup budget exceeds field".into());
    }
    for (ci, ranges) in coverage.iter_mut().enumerate() {
      if self.fixed_circuit(ci) {
        continue;
      }
      ranges.sort_unstable();
      let mut next = 0;
      for &(start, end) in ranges.iter() {
        if start != next {
          return Err("overlapping or missing circuit rows".into());
        }
        next = end;
      }
      if next != rows[ci] {
        return Err("missing circuit rows".into());
      }
    }
    Ok(())
  }

  /// Fill function `function`'s query `query` into its depth circuit's own
  /// row `source`, depth columns included, counting its gap limbs in
  /// `ranges`. Depth columns are computed from the circuit's own columns,
  /// so the row is built here and placed by the caller.
  pub(super) fn fill_depth_source(
    &self,
    record: &Execution<B>,
    function: usize,
    query: usize,
    (scratch, buffer): (&mut Vec<B::Element>, &mut Vec<B::Element>),
    source: &mut Vec<B::Element>,
    ranges: &mut RangeCounts,
  ) -> Result<(), String> {
    let table = &record.queries.tables[function];
    let chip = self.plan.members[function];
    let field = self.plan.program.field;
    let activation = self.plan.artifact.chips[chip].activation;
    source.clear();
    source.resize(activation + 1, field.zero());
    source[activation] = field.one();
    self.plan.fills[function].fill(
      record,
      (table, query),
      scratch,
      buffer,
      source,
    )?;
    self.plan.depth.fill(
      chip,
      record,
      table.depth(query),
      source,
      field,
      buffer,
      ranges,
    )
  }

  /// The depth range tables' uses over the whole record: the gap limbs of
  /// every row of a circuit with gap slots. Fixed tables are committed in
  /// the first shard, before the rows that use them are populated, so their
  /// counts come from this pass over the record. Circuits for which
  /// `skip(ci)` holds are left out: the device counts their rows at upload.
  fn depth_ranges(
    &self,
    record: &Execution<B>,
    skip: impl Fn(usize) -> bool,
  ) -> Result<RangeCounts, String> {
    let gapped: Vec<usize> = (0..self.plan.artifact.functions.len())
      .filter(|&f| {
        let chip = self.plan.members[f];
        !skip(self.placements[chip].circuit)
          && self.plan.depth.fills[chip]
            .slots
            .iter()
            .any(|slot| matches!(slot.kind, crate::trace::depth::Kind::Gap(_)))
      })
      .collect();
    // Counts are sums, so rows are counted in chunks across threads rather
    // than one function per thread: the largest gap circuit holds tens of
    // millions of rows and would otherwise bound the pass on its own.
    const CHUNK: usize = 1 << 14;
    let chunks: Vec<(usize, usize)> = gapped
      .iter()
      .flat_map(|&function| {
        let rows = record.queries.tables[function].len();
        (0..rows).step_by(CHUNK).map(move |first| (function, first))
      })
      .collect();
    let count =
      |(mut ranges, mut scratch): (RangeCounts, Scratch<B::Element>),
       &(function, first): &(usize, usize)| {
        let rows = record.queries.tables[function].len();
        let name = &self.plan.artifact.functions[function].name;
        for query in first..rows.min(first + CHUNK) {
          self
            .fill_depth_source(
              record,
              function,
              query,
              (&mut scratch.scratch, &mut scratch.buffer),
              &mut scratch.source,
              &mut ranges,
            )
            .map_err(|error| format!("{name} query {query}: {error}"))?;
        }
        Ok::<_, String>((ranges, scratch))
      };
    #[cfg(feature = "parallel")]
    let ranges = chunks
      .par_iter()
      .try_fold(|| (RangeCounts::default(), Scratch::default()), count)
      .map(|folded| folded.map(|(ranges, _)| ranges))
      .try_reduce(RangeCounts::default, |a, b| Ok(a.merge(b)))?;
    #[cfg(not(feature = "parallel"))]
    let ranges = chunks
      .iter()
      .try_fold((RangeCounts::default(), Scratch::default()), count)?
      .0;
    Ok(ranges)
  }

  /// The host-only part of preparing `record`: validation, the root check,
  /// member spans, circuit rows and fixed-table counts with the depth range
  /// uses of every circuit the device will not populate. Which circuits the
  /// device populates is decided here from the record as it stands; the
  /// device part recounts on the host if planning later decides otherwise.
  fn prepare_host_parts(
    &self,
    record: &Execution<B>,
    root: Option<(&str, &[B::Element])>,
  ) -> Result<HostParts, String> {
    let mut phases = Phases::default();
    self.plan.validate_record(record)?;
    phases.lap("validate");
    if let Some((entry, args)) = root {
      self.plan.root(record, entry, args)?;
    }
    phases.lap("root");
    let mut members = Vec::new();
    for group in &self.members {
      let mut first = 0usize;
      let mut spans = Vec::new();
      for &function in group {
        let end = first
          .checked_add(record.queries.tables[function].len())
          .ok_or("member offset overflow")?;
        spans.push(Member { function, first, end });
        first = end;
      }
      members.push(spans);
    }
    let rows = self.validated_record_rows(record)?;
    phases.lap("rows");
    let generated: Vec<bool> = (0..self.system.circuits.len())
      .map(|ci| self.generated_circuit(record, ci))
      .collect();
    let ranges = self.depth_ranges(record, |ci| generated[ci])?;
    phases.lap("depth ranges");
    let counts = self.auxiliary_counts(record, &ranges)?;
    phases.lap("auxiliary counts");
    Ok(HostParts {
      plan: self.plan_identity(),
      generated,
      counts,
      members,
      rows,
      phases: phases.done,
    })
  }

  /// Completes `host`, prepared from `record` by [`Self::prepare_host_parts`]
  /// on this backend's plan: uploads the device circuits' record and adds
  /// their depth range uses, counted at upload, to the host's counts.
  /// With `layout`, the device record is uploaded one shard image at a time
  /// when the record's references allow it (`gpu::DeviceRecord::
  /// upload_sharded`).
  fn prepare_device_parts<'r>(
    &self,
    record: &'r Execution<B>,
    host: &HostParts,
    #[cfg_attr(not(feature = "cuda"), allow(unused_variables))] layout: Option<
      &BatchLayout,
    >,
  ) -> Result<PreparedRecord<'r, B>, String> {
    if host.plan != self.plan_identity()
      || host.members.len() != self.members.len()
      || host.members.iter().zip(&self.members).any(|(spans, group)| {
        !spans.iter().map(|m| m.function).eq(group.iter().copied())
      })
    {
      return Err("record prepared for another trace plan".into());
    }
    let mut phases = Phases::default();
    #[cfg(feature = "cuda")]
    let device = self
      .device_plans_for(record)
      .map(|plans| {
        match layout {
          Some(layout) => gpu::DeviceRecord::upload_sharded(
            self,
            plans,
            record,
            self.device,
            layout,
          ),
          None => gpu::DeviceRecord::upload(self, plans, record, self.device),
        }
        .map(std::sync::Arc::new)
      })
      .transpose()?;
    phases.lap("upload");
    #[cfg(feature = "cuda")]
    let generated: Vec<bool> = (0..self.system.circuits.len())
      .map(|ci| device.as_ref().is_some_and(|d| d.height(ci).is_some()))
      .collect();
    #[cfg(not(feature = "cuda"))]
    let generated = vec![false; self.system.circuits.len()];
    #[cfg_attr(not(feature = "cuda"), allow(unused_mut))]
    let mut counts = if generated == host.generated {
      host.counts.clone()
    } else {
      // The device populates other circuits than the host assumed (the
      // device record did not fit, say): count every circuit it leaves.
      let ranges = self.depth_ranges(record, |ci| generated[ci])?;
      phases.lap("host depth ranges again");
      self.auxiliary_counts(record, &ranges)?
    };
    #[cfg(feature = "cuda")]
    if let Some(device) = &device {
      self.add_range_counts(&mut counts, device.ranges())?;
    }
    phases.lap("merge");
    if std::env::var_os("AIUR_POPULATION_REPORT").is_some() {
      let list = |phases: &[(&str, f64)]| {
        phases
          .iter()
          .map(|(name, secs)| format!("{name} {secs:.2}s"))
          .collect::<Vec<_>>()
          .join(", ")
      };
      eprintln!(
        "[aiur] preparation: host {}; device {}",
        list(&host.phases),
        list(&phases.done)
      );
    }
    Ok(PreparedRecord {
      record,
      backend_identity: std::sync::Arc::clone(&self.preparation_identity),
      counts,
      members: host.members.clone(),
      rows: host.rows.clone(),
      #[cfg(feature = "cuda")]
      device,
    })
  }

  fn plan_identity(&self) -> usize {
    (&*self.plan as *const TracePlan<'_, B>).cast::<()>() as usize
  }

  pub fn prepare_incremental<'r>(
    &self,
    record: &'r Execution<B>,
    root: Option<(&str, &[B::Element])>,
  ) -> Result<PreparedRecord<'r, B>, String> {
    let host = self.prepare_host_parts(record, root)?;
    self.prepare_device_parts(record, &host, None)
  }

  /// Per shard of `layout`: the device image bound planning charges and the
  /// image the gather builds when every device circuit is populated from
  /// per-shard images, in bytes, with the gather's seconds, beside the
  /// whole device record's bytes; `null` without device plans or usable
  /// row references. Gathered bytes never exceed the bound.
  #[cfg(feature = "cuda")]
  pub fn shard_image_report(
    &self,
    record: &Execution<B>,
    layout: &BatchLayout,
  ) -> Result<serde_json::Value, String> {
    let Some(plans) = self.device_plans.as_ref() else {
      return Ok(serde_json::Value::Null);
    };
    let Some((shards, whole)) =
      plans.shard_image_sizes(self, record, layout)?
    else {
      return Ok(serde_json::Value::Null);
    };
    let shards: Vec<_> = shards
      .iter()
      .map(|&(bound, gathered, seconds)| {
        serde_json::json!({"bound_bytes": bound, "gathered_bytes": gathered,
          "gather_seconds": seconds})
      })
      .collect();
    Ok(serde_json::json!({"whole_record_bytes": whole, "shards": shards}))
  }

  /// Takes `record` with the host-only part of its preparation for proving
  /// `entry(args)`, which needs neither the device nor the lane: run it
  /// where the record was executed, and [`Self::prove_prepared`] on the
  /// lane, with a backend over the same trace plan.
  pub fn prepare_host(
    &self,
    record: Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<HostPrepared<B>, String> {
    let parts = self.prepare_host_parts(&record, Some((entry, args)))?;
    Ok(HostPrepared {
      record,
      entry: entry.to_owned(),
      args: args.to_vec(),
      parts,
    })
  }

  /// [`Self::prove_incremental_fed`] of a record whose host part
  /// [`Self::prepare_host`] already prepared.
  pub fn prove_prepared(
    &self,
    prepared: &HostPrepared<B>,
    output: &[B::Element],
    layout: &BatchLayout,
    retention: Retention,
    feed: Option<&ShardFeed>,
  ) -> Result<IncrementalRun, String> {
    let preparation = Instant::now();
    self.prove_from_parts(
      &prepared.record,
      &prepared.parts,
      (&prepared.entry, &prepared.args, output),
      layout,
      retention,
      feed,
      preparation,
    )
  }

  pub fn incremental_witness(
    &self,
    prepared: &PreparedRecord<'_, B>,
    shard: &ShardLayout,
  ) -> Result<PreparedWitness<Val>, String> {
    self.timed_witness(prepared, shard).map(|(witness, _)| witness)
  }

  fn timed_witness(
    &self,
    prepared: &PreparedRecord<'_, B>,
    shard: &ShardLayout,
  ) -> Result<(PreparedWitness<Val>, ShardTime), String> {
    let start = Instant::now();
    if !std::sync::Arc::ptr_eq(
      &prepared.backend_identity,
      &self.preparation_identity,
    ) {
      return Err("prepared record belongs to another prover backend".into());
    }
    if shard.circuits.len() != self.system.circuits.len() {
      return Err("wrong shard circuit count".into());
    }
    #[cfg(feature = "cuda")]
    let rows = match &prepared.device {
      Some(device) => {
        let rows = device.shard_rows(prepared.record, shard)?;
        if let Some(rows) = &rows {
          device.prefetch(rows);
        }
        rows
      },
      None => None,
    };
    #[cfg(not(feature = "cuda"))]
    let rows = None::<()>;
    let populate = |(ci, slice)| {
      let mut time = CircuitTime::default();
      let trace = self.populate_slice(
        prepared,
        shard,
        rows.as_ref(),
        ci,
        slice,
        &mut time,
      )?;
      Ok::<_, String>((trace, time))
    };
    #[cfg(feature = "parallel")]
    let populated = shard
      .circuits
      .par_iter()
      .copied()
      .enumerate()
      .map(populate)
      .collect::<Result<Vec<_>, _>>()?;
    #[cfg(not(feature = "parallel"))]
    let populated = shard
      .circuits
      .iter()
      .copied()
      .enumerate()
      .map(populate)
      .collect::<Result<Vec<_>, _>>()?;
    let (traces, circuits): (Vec<_>, Vec<_>) = populated.into_iter().unzip();
    let lookups = Instant::now();
    let witness = if self.gpu_lookup_only {
      let lookups = traces
        .iter()
        .zip(&self.system.circuits)
        .map(|(trace, circuit)| {
          let widths: Vec<_> =
            circuit.graph.lookups.iter().map(|l| l.args.len()).collect();
          multi_stark::lookup::LookupValues::shape_only(trace.height(), &widths)
        })
        .collect();
      PreparedWitness { traces, lookups }
    } else {
      self
        .witness_from_main(
          traces.into_iter().map(TraceSource::materialize).collect(),
        )
        .into()
    };
    let time =
      ShardTime { circuits, lookups: lookups.elapsed(), wall: start.elapsed() };
    Ok((witness, time))
  }

  fn populate_slice(
    &self,
    prepared: &PreparedRecord<'_, B>,
    shard: &ShardLayout,
    #[cfg(feature = "cuda")] rows: Option<&std::sync::Arc<gpu::ShardRows>>,
    #[cfg(not(feature = "cuda"))] _rows: Option<&()>,
    ci: usize,
    slice: CircuitSlice,
    time: &mut CircuitTime,
  ) -> Result<TraceSource<Val>, String> {
    let circuit = &self.system.circuits[ci];
    let width = circuit.main_width;
    let available =
      *prepared.rows.get(ci).ok_or("prepared record circuit count mismatch")?;
    if slice.rows > slice.height
      || slice.first.checked_add(slice.rows).is_none_or(|end| end > available)
      || (slice.height != 0 && !slice.height.is_power_of_two())
    {
      return Err("invalid circuit slice".into());
    }
    #[cfg(feature = "cuda")]
    if slice.height != 0
      && let Some(device) = &prepared.device
      && device.height(ci).is_some()
    {
      return Ok(TraceSource::Generated(std::sync::Arc::new(
        gpu::DeviceTrace {
          record: device.clone(),
          circuit: ci,
          base: slice.first,
          height: slice.height,
          real_rows: slice.rows,
          rows: rows.cloned(),
        },
      )));
    }
    if self.fixed_circuit(ci) {
      if slice.height != circuit.preprocessed_height
        || slice.first != 0
        || slice.rows != slice.height
      {
        return Err("fixed table slice changed".into());
      }
      if shard.fixed_counts {
        let fill = Instant::now();
        let table =
          self.tables[ci - self.members.len()].witness(&prepared.counts);
        time.fill = fill.elapsed();
        return Ok(TraceSource::Host(table));
      }
    }
    let allocation = Instant::now();
    let mut values = Val::zero_vec(
      slice.height.checked_mul(width).ok_or("shard matrix size overflow")?,
    );
    time.allocation = allocation.elapsed();
    let filling = Instant::now();
    if ci < self.members.len() {
      let fill = |scratch: &mut Scratch<B::Element>,
                  (offset, row): (usize, &mut [Val])| {
        let index = slice.first + offset;
        let members = prepared
          .members
          .get(ci)
          .ok_or("prepared record grouping mismatch")?;
        let member = members
          .get(members.partition_point(|m| m.end <= index))
          .ok_or("slice exceeds prepared member rows")?;
        let query = index - member.first;
        let table = &prepared.record.queries.tables[member.function];
        let multiplicity = table.count(query);
        if multiplicity >= Val::ORDER_U64 {
          return Err("function count reaches field characteristic".into());
        }
        let chip = self.plan.members[member.function];
        let placement = &self.placements[chip];
        let name = &self.plan.artifact.functions[member.function].name;
        if self.plan.depth.fills[chip].is_empty() {
          self.plan.fills[member.function]
            .fill_into(
              prepared.record,
              (table, query),
              &mut scratch.scratch,
              &mut scratch.buffer,
              |column, value| {
                row[placement.columns[column]] = B::into_stark(value)
              },
            )
            .map_err(|error| format!("{name} query {query}: {error}"))?;
        } else {
          // `prepare_incremental` counted every gap limb already; this
          // row's counts go to the thread's discarded sink.
          let Scratch { scratch, buffer, source, ranges } = scratch;
          self
            .fill_depth_source(
              prepared.record,
              member.function,
              query,
              (scratch, buffer),
              source,
              ranges,
            )
            .map_err(|error| format!("{name} query {query}: {error}"))?;
          for (&column, &value) in placement.columns.iter().zip(source.iter()) {
            row[column] = B::into_stark(value);
          }
        }
        placement.finish(row, multiplicity);
        Ok::<_, String>(())
      };
      let real = &mut values[..slice.rows * width];
      // Rows are filled in parallel batches, and a thread waiting on this
      // circuit's batches runs other circuits' work meanwhile, so only the
      // batches' own durations are attributed to this circuit.
      #[cfg(feature = "parallel")]
      {
        let busy = AtomicU64::new(0);
        real.par_chunks_mut(width * 32).enumerate().try_for_each_init(
          Scratch::default,
          |scratch, (batch, cells)| {
            let start = Instant::now();
            for (i, row) in cells.chunks_mut(width).enumerate() {
              fill(scratch, (batch * 32 + i, row))?;
            }
            busy.fetch_add(
              u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX),
              Ordering::Relaxed,
            );
            Ok::<_, String>(())
          },
        )?;
        time.fill = Duration::from_nanos(busy.into_inner());
        return Ok(TraceSource::Host(RowMajorMatrix::new(values, width)));
      }
      #[cfg(not(feature = "parallel"))]
      {
        let mut scratch = Scratch::default();
        for row in real.chunks_mut(width).enumerate() {
          fill(&mut scratch, row)?;
        }
      }
    } else if !self.fixed_circuit(ci) {
      let rom_index = ci - self.members.len() - self.tables.len();
      self.rom.populate_rows(
        prepared.record,
        rom_index,
        slice.first,
        slice.rows,
        &mut values,
      );
    }
    time.fill = filling.elapsed();
    Ok(TraceSource::Host(RowMajorMatrix::new(values, width)))
  }

  pub fn prove_incremental(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    layout: &BatchLayout,
    retention: Retention,
  ) -> Result<BatchProof, String> {
    self
      .prove_incremental_timed(
        record, entry, args, output, layout, retention, false,
      )
      .map(|run| run.proof)
  }

  /// Prove with `layout`, building each shard's witness one shard ahead of
  /// the prover, on a feed as wide as the current pool, when `pipeline`
  /// holds. The schedule changes no proof byte.
  #[allow(clippy::too_many_arguments)]
  pub fn prove_incremental_timed(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    layout: &BatchLayout,
    retention: Retention,
    pipeline: bool,
  ) -> Result<IncrementalRun, String> {
    let feed = pipeline.then(ShardFeed::matching_current).transpose()?;
    self.prove_incremental_fed(
      record,
      entry,
      args,
      output,
      layout,
      retention,
      feed.as_ref(),
    )
  }

  /// Prove with `layout`, building each shard's witness one shard ahead of
  /// the prover on `feed`, or serially without one. The schedule changes no
  /// proof byte.
  #[allow(clippy::too_many_arguments)]
  pub fn prove_incremental_fed(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    layout: &BatchLayout,
    retention: Retention,
    feed: Option<&ShardFeed>,
  ) -> Result<IncrementalRun, String> {
    let preparation = Instant::now();
    let host = self.prepare_host_parts(record, Some((entry, args)))?;
    self.prove_from_parts(
      record,
      &host,
      (entry, args, output),
      layout,
      retention,
      feed,
      preparation,
    )
  }

  #[allow(clippy::too_many_arguments)]
  fn prove_from_parts(
    &self,
    record: &Execution<B>,
    host: &HostParts,
    (entry, args, output): (&str, &[B::Element], &[B::Element]),
    layout: &BatchLayout,
    retention: Retention,
    feed: Option<&ShardFeed>,
    preparation: Instant,
  ) -> Result<IncrementalRun, String> {
    self.validate_layout(&host.rows, layout)?;
    if layout.memory_intervals != self.record_shape(record)?.memory_intervals {
      return Err("layout memory intervals differ from record".into());
    }
    let prepared = self.prepare_device_parts(
      record,
      host,
      record.host_population.sharded().then_some(layout),
    )?;
    // SAFETY: the guard is a local of this call, dropped before `record`'s
    // borrow ends.
    #[cfg(feature = "cuda")]
    let _attached = prepared
      .device
      .as_deref()
      .map(|device| unsafe { device.attach(record) })
      .transpose()?;
    let preparation_seconds = preparation.elapsed().as_secs_f64();
    let times = std::sync::Mutex::new(Vec::new());
    // A pipelined supply of one shard overlaps the proving of the previous
    // one, and its witness prefetches its device image: reserve that image
    // before the previous witness is handed over.
    #[cfg(feature = "cuda")]
    let order = self.supply_order(layout.shards.len(), retention);
    #[cfg(feature = "cuda")]
    let pipelined = Self::pipelines(&order, feed);
    let proving = Instant::now();
    let streamed = self.prove_streamed_scheduled(
      entry,
      args,
      output,
      StreamPlan {
        shards: layout.shards.len(),
        memory_intervals: layout.memory_intervals.clone(),
        retention,
      },
      feed,
      |round, shard| {
        let (witness, time) =
          self.timed_witness(&prepared, &layout.shards[shard])?;
        #[cfg(feature = "cuda")]
        if pipelined
          && let Some(device) = &prepared.device
          && let Some(at) = order.iter().position(|&s| s == (round, shard))
          && let Some(&(_, next)) = order.get(at + 1)
        {
          device.reserve_next(next);
        }
        times
          .lock()
          .unwrap_or_else(|e| e.into_inner())
          .push((round, shard, time));
        Ok(witness)
      },
    )?;
    let wall = proving.elapsed();
    let times = times.into_inner().unwrap_or_else(|e| e.into_inner());
    let mut population = self.population_report(layout, &times);
    population.pipelined = streamed.pipelined;
    population.preparation_seconds = preparation_seconds;
    population.stall_seconds = streamed.stall.as_secs_f64();
    Ok(IncrementalRun {
      proof: streamed.proof,
      trace_seconds: preparation_seconds + population.population_seconds,
      proving_seconds: wall.saturating_sub(streamed.stall).as_secs_f64(),
      population,
    })
  }

  fn population_report(
    &self,
    layout: &BatchLayout,
    times: &[(usize, usize, ShardTime)],
  ) -> PopulationReport {
    let seconds = |d: Duration| d.as_secs_f64();
    let totals =
      |round: usize, shard: Option<usize>, t: &ShardTime| PopulationTotals {
        round,
        shard,
        wall_seconds: seconds(t.wall),
        allocation_seconds: t
          .circuits
          .iter()
          .map(|c| seconds(c.allocation))
          .sum(),
        fill_seconds: t.circuits.iter().map(|c| seconds(c.fill)).sum(),
        lookup_seconds: seconds(t.lookups),
      };
    let mut report = PopulationReport::default();
    let mut circuits: Vec<CircuitPopulation> = self
      .names
      .iter()
      .enumerate()
      .map(|(ci, name)| {
        let slices = layout.shards.iter().map(|s| s.circuits[ci]);
        CircuitPopulation {
          circuit: name.clone(),
          round_seconds: vec![0.0; 2],
          shards: slices.clone().filter(|s| s.height != 0).count(),
          real_rows: slices.clone().map(|s| s.rows as u64).sum(),
          padded_cells: slices
            .map(|s| (s.height * self.system.circuits[ci].main_width) as u64)
            .sum(),
          ..Default::default()
        }
      })
      .collect();
    for &(round, shard, ref time) in times {
      let shard_totals = totals(round, Some(shard), time);
      report.population_seconds += shard_totals.wall_seconds;
      if report.rounds.len() <= round {
        report.rounds.resize_with(round + 1, Default::default);
      }
      let sum = &mut report.rounds[round];
      sum.round = round;
      sum.wall_seconds += shard_totals.wall_seconds;
      sum.allocation_seconds += shard_totals.allocation_seconds;
      sum.fill_seconds += shard_totals.fill_seconds;
      sum.lookup_seconds += shard_totals.lookup_seconds;
      report.shards.push(shard_totals);
      for (circuit, t) in circuits.iter_mut().zip(&time.circuits) {
        circuit.allocation_seconds += seconds(t.allocation);
        circuit.fill_seconds += seconds(t.fill);
        circuit.round_seconds[round.min(1)] += seconds(t.allocation + t.fill);
      }
    }
    for circuit in &mut circuits {
      circuit.seconds = circuit.allocation_seconds + circuit.fill_seconds;
    }
    circuits.sort_by(|a, b| b.seconds.total_cmp(&a.seconds));
    circuits.truncate(TOP_CIRCUITS);
    report.top_circuits = circuits;
    report
  }

  pub fn plan_incremental(
    &self,
    record: &Execution<B>,
    options: &planning::Options,
    resident: u64,
  ) -> Result<planning::BatchPlan, String> {
    options.validate()?;
    if let Some(layout) = options.forced_layout()? {
      return self.plan_forced(record, layout, options, resident);
    }
    if let Some(logs) = &options.fixed_log_heights {
      let layout = self.fixed_layout(record, logs)?;
      return self.plan_forced(record, layout, options, resident);
    }
    if options.packing == Some(false) {
      return self.plan_uniform_incremental(record, options, resident);
    }
    let rows = self.record_rows(record)?;
    let intervals = self.record_shape(record)?.memory_intervals;
    let budget = ram_budget(options);
    let device_cells = options.device_cells()?;
    if let Some(rejected) =
      self.incremental_floor(record, &rows, options, budget, resident)?
    {
      return Ok(rejected);
    }
    let whole_cells = rows
      .iter()
      .enumerate()
      .map(|(ci, &n)| Ok(padded(n)? as u128 * self.committed_width(ci)))
      .collect::<Result<Vec<_>, String>>()?
      .into_iter()
      .sum::<u128>()
      .max(1);
    let mut limit =
      u128::from(device_cells.unwrap_or(u64::MAX)).min(whole_cells);
    let mut height_limit = options.height_limit()?;
    let mut previous = None;
    let mut candidates = Vec::new();
    loop {
      let layout =
        match self.packed_layout(&rows, &intervals, limit, height_limit) {
          Ok(layout) => layout,
          Err(error) => return previous.ok_or(error),
        };
      let mut batch = self.plan_layout(
        record,
        &layout,
        budget,
        resident,
        options.retention,
        options.pipeline,
      )?;
      batch.device_cells = device_cells;
      batch.device_budget_bytes = self.device_budget(options)?;
      batch.fits &=
        batch.device_budget_bytes.is_none_or(|n| batch.device_peak_bytes <= n);
      candidates.push(planning::PlanCandidate::from(&batch));
      batch.candidates = candidates.clone();
      batch.layout = Some(layout);
      if batch.fits
        || limit <= 1
        || batch.device_budget_bytes.is_some_and(|n| {
          self.device_peak(0, 0, batch.device_record_bytes, 0) > u128::from(n)
        })
      {
        return Ok(batch);
      }
      if batch.max_rows > 1
        && batch.device_budget_bytes.is_some_and(|n| {
          batch.device_peak_bytes > n
            && self.device_peak(
              u128::from(batch.shard_cells),
              u128::from(batch.shard_cells),
              batch.device_record_bytes,
              0,
            ) <= u128::from(n)
        })
      {
        height_limit = Some(batch.max_rows / 2);
      } else {
        limit /= 2;
      }
      previous = Some(batch);
    }
  }

  /// Charge a caller's layout instead of searching for one.
  pub(super) fn plan_forced(
    &self,
    record: &Execution<B>,
    layout: BatchLayout,
    options: &planning::Options,
    resident: u64,
  ) -> Result<planning::BatchPlan, String> {
    let rows = self.record_rows(record)?;
    self.validate_layout(&rows, &layout)?;
    if layout.memory_intervals != self.record_shape(record)?.memory_intervals {
      return Err("layout memory intervals differ from record".into());
    }
    let mut batch = self.plan_layout(
      record,
      &layout,
      ram_budget(options),
      resident,
      options.retention,
      options.pipeline,
    )?;
    self.bound_forced(&mut batch, options)?;
    batch.candidates = vec![planning::PlanCandidate::from(&batch)];
    batch.layout = Some(layout);
    batch.forced_layout = true;
    Ok(batch)
  }

  /// Applies `options`' device bounds to a plan of a forced layout.
  fn bound_forced(
    &self,
    batch: &mut planning::BatchPlan,
    options: &planning::Options,
  ) -> Result<(), String> {
    batch.device_cells = options.device_cells()?;
    batch.device_budget_bytes = self.device_budget(options)?;
    batch.fits &= batch.device_cells.is_none_or(|n| batch.shard_cells <= n)
      && batch.device_budget_bytes.is_none_or(|n| batch.device_peak_bytes <= n);
    Ok(())
  }

  /// [`Self::plan_forced`] of a validated layout with `terms`, when the
  /// device populates the `generated` circuits from a record of `bytes`
  /// (see [`Self::plan_terms`]), without reading the record.
  #[cfg_attr(not(feature = "cuda"), allow(dead_code))]
  pub(super) fn plan_forced_terms(
    &self,
    terms: &LayoutTerms,
    generated: &[bool],
    bytes: u64,
    options: &planning::Options,
    resident: u64,
  ) -> Result<planning::BatchPlan, String> {
    let mut batch = self.plan_terms(
      terms,
      generated,
      bytes,
      ram_budget(options),
      resident,
      options.retention,
      options.pipeline,
    );
    self.bound_forced(&mut batch, options)?;
    Ok(batch)
  }

  fn plan_uniform_incremental(
    &self,
    record: &Execution<B>,
    options: &planning::Options,
    resident: u64,
  ) -> Result<planning::BatchPlan, String> {
    let rows = self.record_rows(record)?;
    let tallest = rows
      .iter()
      .enumerate()
      .filter(|(ci, _)| !self.fixed_circuit(*ci))
      .map(|(_, &n)| padded(n))
      .collect::<Result<Vec<_>, _>>()?
      .into_iter()
      .max()
      .unwrap_or(1)
      .max(1);
    let budget = ram_budget(options);
    let cell_budget = options.device_cells()?;
    if let Some(rejected) =
      self.incremental_floor(record, &rows, options, budget, resident)?
    {
      return Ok(rejected);
    }
    let device_budget = self.device_budget(options)?;
    let mut cap = options.max_rows.unwrap_or(tallest).min(tallest);
    let mut candidates = Vec::new();
    let mut previous = None;
    loop {
      let layout = match self.uniform_layout(record, cap) {
        Ok(layout) => layout,
        Err(error) => return previous.ok_or(error),
      };
      let mut plan = self.plan_layout(
        record,
        &layout,
        budget,
        resident,
        options.retention,
        options.pipeline,
      )?;
      plan.max_rows = cap;
      plan.device_cells = cell_budget;
      plan.device_budget_bytes = device_budget;
      plan.fits &= cell_budget.is_none_or(|n| plan.shard_cells <= n)
        && device_budget.is_none_or(|n| plan.device_peak_bytes <= n);
      candidates.push(planning::PlanCandidate::from(&plan));
      plan.candidates = candidates.clone();
      plan.layout = Some(layout);
      if plan.fits
        || cap == 1
        || device_budget.is_some_and(|n| {
          self.device_peak(0, 0, plan.device_record_bytes, 0) > u128::from(n)
        })
      {
        return Ok(plan);
      }
      previous = Some(plan);
      cap /= 2;
    }
  }

  fn incremental_floor(
    &self,
    record: &Execution<B>,
    rows: &[usize],
    options: &planning::Options,
    budget: u64,
    resident: u64,
  ) -> Result<Option<planning::BatchPlan>, String> {
    // Every shard needs the fixed tables, setup and prepared-record metadata.
    // This lower bound avoids constructing a large packing that cannot fit.
    let circuits = rows
      .iter()
      .enumerate()
      .map(|(ci, &n)| {
        if self.fixed_circuit(ci) {
          CircuitSlice { first: 0, rows: n, height: n }
        } else {
          CircuitSlice::default()
        }
      })
      .collect();
    let floor = BatchLayout {
      version: 1,
      shards: vec![ShardLayout { circuits, fixed_counts: true }],
      memory_intervals: vec![],
    };
    let mut batch = self.plan_layout(
      record,
      &floor,
      budget,
      resident,
      planning::RetentionPolicy::Regenerate,
      Some(false),
    )?;
    let largest_row = rows
      .iter()
      .enumerate()
      .filter(|(ci, n)| !self.fixed_circuit(*ci) && **n != 0)
      .map(|(ci, _)| self.committed_width(ci))
      .max()
      .unwrap_or(0);
    let minimum_cells = u128::from(batch.shard_cells) + largest_row;
    batch.device_cells = options.device_cells()?;
    batch.device_budget_bytes = self.device_budget(options)?;
    batch.fits &= batch
      .device_cells
      .is_none_or(|n| minimum_cells <= u128::from(n))
      && batch.device_budget_bytes.is_none_or(|n| batch.device_peak_bytes <= n);
    if batch.fits {
      return Ok(None);
    }
    batch.shard_cells = u64::try_from(minimum_cells).unwrap_or(u64::MAX);
    batch.candidates.push(planning::PlanCandidate::from(&batch));
    Ok(Some(batch))
  }

  #[cfg_attr(not(feature = "cuda"), allow(clippy::unnecessary_wraps))]
  fn plan_layout(
    &self,
    record: &Execution<B>,
    layout: &BatchLayout,
    budget: u64,
    resident: u64,
    policy: planning::RetentionPolicy,
    pipeline: Option<bool>,
  ) -> Result<planning::BatchPlan, String> {
    let generated: Vec<_> = (0..self.system.circuits.len())
      .map(|ci| self.generated_circuit(record, ci))
      .collect();
    #[cfg(feature = "cuda")]
    let bytes = self
      .device_plans_for(record)
      .map(|p| {
        if record.host_population.sharded() {
          p.record_bytes_for(self, record, layout)
        } else {
          p.record_bytes(self, record)
        }
      })
      .transpose()?
      .unwrap_or(0);
    #[cfg(not(feature = "cuda"))]
    let bytes = 0;
    Ok(self.plan_terms(
      &self.layout_terms(layout),
      &generated,
      bytes,
      budget,
      resident,
      policy,
      pipeline,
    ))
  }

  /// What planning `layout` needs that does not depend on which circuits
  /// the device populates.
  pub(super) fn layout_terms(&self, layout: &BatchLayout) -> LayoutTerms {
    let metadata = (layout.shards.len()
      * self.system.circuits.len()
      * size_of::<CircuitSlice>()) as u128
      + self.members.iter().map(|m| m.len() as u128 * 32).sum::<u128>()
      + self
        .plan
        .program
        .program
        .maps
        .iter()
        .map(|m| {
          self.plan.program.program.tables[m.input].rows.len() as u128 * 8
        })
        .sum::<u128>();
    let shards = layout
      .shards
      .iter()
      .map(|shard| {
        let heights: Vec<_> =
          shard.circuits.iter().map(|slice| slice.height).collect();
        let main: Vec<(usize, u128)> = heights
          .iter()
          .zip(&self.system.circuits)
          .enumerate()
          .filter(|(_, (h, _))| **h != 0)
          .map(|(ci, (&h, c))| (ci, h as u128 * c.main_width as u128))
          .collect();
        let committed: u128 = heights
          .iter()
          .enumerate()
          .map(|(ci, &h)| h as u128 * self.committed_width(ci))
          .sum();
        let population: u128 = heights
          .iter()
          .zip(&self.system.circuits)
          .map(|(&h, c)| h as u128 * (c.main_width + c.stage_2_width) as u128)
          .sum();
        let tallest = heights.iter().copied().max().unwrap_or(1).max(1);
        let max_rows = heights
          .iter()
          .enumerate()
          .filter(|(ci, _)| !self.fixed_circuit(*ci))
          .map(|(_, &h)| h)
          .max()
          .unwrap_or(1)
          .max(1);
        let (cpu, saved, prep) = self.prove_allocation(&heights, tallest);
        let lookup: u128 = if self.gpu_lookup_only {
          0
        } else {
          heights
            .iter()
            .zip(&self.system.circuits)
            .map(|(&h, c)| {
              let args: usize =
                c.graph.lookups.iter().map(|l| l.args.len()).sum();
              h as u128
                * ((c.num_lookups + args) as u128 * 8
                  + size_of::<multi_stark::lookup::LookupRowMut<'_, Val>>()
                    as u128)
            })
            .sum()
        };
        ShardTerms {
          main,
          committed,
          population,
          tallest,
          max_rows,
          cpu,
          saved,
          prep,
          lookup,
        }
      })
      .collect();
    LayoutTerms { metadata, shards }
  }

  /// The plan of a layout with `terms` when the device populates the
  /// `generated` circuits from a record of `device_record_bytes`.
  ///
  /// Device population costs the host nothing beyond the record it already
  /// holds: a proof lends the device record its execution record
  /// (`gpu::DeviceRecord::attach`), so a release under device pressure
  /// keeps no host copy and re-uploads from the record.
  #[allow(clippy::too_many_arguments)]
  pub(super) fn plan_terms(
    &self,
    terms: &LayoutTerms,
    generated: &[bool],
    device_record_bytes: u64,
    budget: u64,
    resident: u64,
    policy: planning::RetentionPolicy,
    pipeline: Option<bool>,
  ) -> planning::BatchPlan {
    use planning::RetentionPolicy;
    let bounded = |n: u128| u64::try_from(n).unwrap_or(u64::MAX);
    let metadata = terms.metadata;
    let mut device_peak = 0;
    let mut generation = 0;
    let mut proving = 0;
    let mut retained = 0;
    let mut retained_workspace = 0;
    let mut shard_cells = 0;
    let mut lookahead = 0;
    let mut stage1_cells = 0;
    let mut host_cells = 0;
    let mut max_rows = 0;
    for shard in &terms.shards {
      let main: u128 = shard
        .main
        .iter()
        .filter(|(ci, _)| !generated.get(*ci).copied().unwrap_or(false))
        .map(|(_, cells)| cells)
        .sum();
      let cells: u128 = shard.main.iter().map(|(_, cells)| cells).sum();
      let ShardTerms {
        committed,
        population,
        tallest,
        cpu,
        saved,
        prep,
        lookup,
        ..
      } = *shard;
      shard_cells = shard_cells.max(committed);
      stage1_cells += cells;
      host_cells += main;
      device_peak = device_peak.max(self.device_peak(
        committed,
        population,
        device_record_bytes,
        tallest,
      ));
      max_rows = max_rows.max(shard.max_rows);
      retained += saved;
      lookahead = lookahead.max(main * 8 + lookup);
      let workspace = if cfg!(feature = "cuda") {
        main * 8 + lookup + (256 << 20)
      } else {
        cpu
      };
      generation = generation.max(main * 8 + prep);
      proving = proving.max(workspace + prep);
      let overlap = if cfg!(feature = "cuda") { 0 } else { saved };
      retained_workspace = retained_workspace
        .max((workspace.max(main * 8) + prep).saturating_sub(overlap));
    }
    let base = u128::from(resident) + metadata;
    let regenerated_peak = base + generation.max(proving);
    let retained_peak = if terms.shards.len() == 1 {
      regenerated_peak
    } else {
      base + retained_workspace + retained
    };
    let retention = match policy {
      _ if self.requires_regeneration(terms.shards.len()) => {
        RetentionPolicy::Regenerate
      },
      RetentionPolicy::Auto if retained_peak <= u128::from(budget) => {
        RetentionPolicy::Retain
      },
      RetentionPolicy::Auto => RetentionPolicy::Regenerate,
      policy => policy,
    };
    let peak = if retention == RetentionPolicy::Retain {
      retained_peak
    } else {
      regenerated_peak
    };
    // A lookahead holds the next shard's host witness beside the shard
    // being committed or proven; without room for it, supply serially.
    let supplies = self
      .supply_order(
        terms.shards.len(),
        if retention == RetentionPolicy::Retain {
          Retention::Retain
        } else {
          Retention::Regenerate
        },
      )
      .len();
    let pipelined_peak = peak + lookahead;
    let pipelined = pipeline != Some(false)
      && supplies >= 2
      && pipelined_peak <= u128::from(budget);
    let peak = if pipelined { pipelined_peak } else { peak };
    planning::BatchPlan {
      max_rows,
      shards: terms.shards.len(),
      retention,
      budget_bytes: budget,
      stage1_cells: bounded(stage1_cells),
      generation_peak_bytes: bounded(base + generation),
      proving_peak_bytes: bounded(peak),
      fits: peak <= u128::from(budget),
      suggested_parts: usize::try_from(peak.div_ceil(u128::from(budget)))
        .unwrap_or(usize::MAX)
        .max(1),
      shard_cells: bounded(shard_cells),
      device_cells: None,
      host_stage1_cells: bounded(host_cells),
      device_record_bytes,
      device_peak_bytes: bounded(device_peak),
      device_budget_bytes: None,
      layout: None,
      population: Vec::new(),
      candidates: Vec::new(),
      retained_bytes: bounded(retained),
      regenerated_peak_bytes: Some(bounded(regenerated_peak)),
      retained_workspace_peak_bytes: Some(bounded(base + retained_workspace)),
      pipelined,
      lookahead_bytes: bounded(lookahead),
      forced_layout: false,
    }
  }
}
