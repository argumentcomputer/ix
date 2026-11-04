//! Explicit circuit ranges and bounded population from an immutable record.
use super::*;
use multi_stark::{
  batch::Retention,
  witness::{PreparedWitness, TraceSource},
};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

const MAX_SHARDS: usize = 65_536;
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

struct Member {
  function: usize,
  first: usize,
  end: usize,
}

pub struct PreparedRecord<'r, B: WitnessField> {
  record: &'r Execution<B>,
  counts: Vec<Vec<u64>>,
  members: Vec<Vec<Member>>,
  rows: Vec<usize>,
  #[cfg(feature = "cuda")]
  device: Option<std::sync::Arc<gpu::DeviceRecord>>,
}

fn ram_budget(options: &planning::Options) -> u64 {
  options
    .max_ram_bytes
    .or_else(|| planning::available_memory().map(|n| n / 100 * 85))
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

  /// `(memory width, circuit index)` of every memory circuit, ascending by
  /// width: the circuits whose boundary messages a batch preamble carries.
  pub fn memory_circuits(&self) -> Vec<(usize, usize)> {
    let start = self.members.len() + self.tables.len();
    let mut circuits: Vec<_> = self.system.circuits[start..]
      .iter()
      .enumerate()
      .map(|(i, c)| (c.main_width - 3, start + i))
      .collect();
    circuits.sort_unstable();
    circuits
  }

  pub fn record_rows(
    &self,
    record: &Execution<B>,
  ) -> Result<Vec<usize>, String> {
    self.plan.validate_record_shape(record)?;
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
    rows.extend(
      self
        .system
        .circuits
        .iter()
        .skip(rows.len())
        .map(|c| record.memory.indices_for_width(c.main_width - 3).len()),
    );
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
      + 2 * c.quotient_degree() as u128
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
    let domain_rows =
      1usize.checked_shl(domain_log as u32).ok_or("trace domain overflow")?;
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
          degrees.push(slice.height.ilog2() as u8);
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

  pub fn prepare_incremental<'r>(
    &self,
    record: &'r Execution<B>,
    root: Option<(&str, &[B::Element])>,
  ) -> Result<PreparedRecord<'r, B>, String> {
    self.plan.validate_record(record)?;
    if let Some((entry, args)) = root {
      self.plan.root(record, entry, args)?;
    }
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
    Ok(PreparedRecord {
      record,
      counts: self.auxiliary_counts(record)?,
      members,
      rows: self.record_rows(record)?,
      #[cfg(feature = "cuda")]
      device: self
        .device_plans_for(record)
        .map(|plans| {
          gpu::DeviceRecord::upload(self, plans, record, self.device)
            .map(std::sync::Arc::new)
        })
        .transpose()?,
    })
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
    self.plan.validate_record_shape(prepared.record)?;
    if shard.circuits.len() != self.system.circuits.len() {
      return Err("wrong shard circuit count".into());
    }
    let populate = |(ci, slice)| {
      let mut time = CircuitTime::default();
      let trace = self.populate_slice(prepared, shard, ci, slice, &mut time)?;
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
      let fill = |scratch: &mut (Vec<B::Element>, Vec<B::Element>),
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
        let output = table.output(query);
        if output.multiplicity >= Val::ORDER_U64 {
          return Err("function count reaches field characteristic".into());
        }
        let placement = &self.placements[self.plan.members[member.function]];
        self.plan.fills[member.function]
          .fill_into(
            prepared.record,
            (table.input(query), output),
            &mut scratch.0,
            &mut scratch.1,
            |column, value| {
              row[placement.columns[column]] = B::into_stark(value)
            },
          )
          .map_err(|error| {
            format!(
              "{} query {query}: {error}",
              self.plan.artifact.functions[member.function].name
            )
          })?;
        placement.finish(row, output.multiplicity);
        Ok::<_, String>(())
      };
      let real = &mut values[..slice.rows * width];
      // Rows are filled in parallel batches, and a thread waiting on this
      // circuit's batches runs other circuits' work meanwhile, so only the
      // batches' own durations are attributed to this circuit.
      #[cfg(feature = "parallel")]
      {
        let busy = std::sync::atomic::AtomicU64::new(0);
        real.par_chunks_mut(width * 32).enumerate().try_for_each_init(
          || (Vec::new(), Vec::new()),
          |scratch, (batch, cells)| {
            let start = Instant::now();
            for (i, row) in cells.chunks_mut(width).enumerate() {
              fill(scratch, (batch * 32 + i, row))?;
            }
            busy.fetch_add(
              start.elapsed().as_nanos() as u64,
              std::sync::atomic::Ordering::Relaxed,
            );
            Ok::<_, String>(())
          },
        )?;
        time.fill = Duration::from_nanos(busy.into_inner());
        return Ok(TraceSource::Host(RowMajorMatrix::new(values, width)));
      }
      #[cfg(not(feature = "parallel"))]
      {
        let mut scratch = (Vec::new(), Vec::new());
        for row in real.chunks_mut(width).enumerate() {
          fill(&mut scratch, row)?;
        }
      }
    } else if !self.fixed_circuit(ci) {
      let bucket = prepared.record.memory.indices_for_width(width - 3);
      for (&index, row) in bucket[slice.first..slice.first + slice.rows]
        .iter()
        .zip(values.chunks_mut(width))
      {
        let cell =
          prepared.record.memory.get(index).ok_or("missing ROM entry")?;
        row[0] = Val::from_u64(cell.multiplicity);
        row[1] = Val::ONE;
        row[2] = Val::from_usize(cell.address);
        for (dest, &value) in row[3..].iter_mut().zip(cell.cell.value) {
          *dest = B::into_stark(value);
        }
      }
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
    let rows = self.record_rows(record)?;
    self.validate_layout(&rows, layout)?;
    if layout.memory_intervals != self.record_shape(record)?.memory_intervals {
      return Err("layout memory intervals differ from record".into());
    }
    let prepared = self.prepare_incremental(record, Some((entry, args)))?;
    let preparation_seconds = preparation.elapsed().as_secs_f64();
    let times = std::sync::Mutex::new(Vec::new());
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
    let mut height_limit = options.max_rows;
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
          self.device_peak(0, batch.device_record_bytes, 0) > n as u128
        })
      {
        return Ok(batch);
      }
      if batch.max_rows > 1
        && batch.device_budget_bytes.is_some_and(|n| {
          batch.device_peak_bytes > n
            && self.device_peak(
              batch.shard_cells as u128,
              batch.device_record_bytes,
              0,
            ) <= n as u128
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
  fn plan_forced(
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
    batch.device_cells = options.device_cells()?;
    batch.device_budget_bytes = self.device_budget(options)?;
    batch.fits &= batch.device_cells.is_none_or(|n| batch.shard_cells <= n)
      && batch.device_budget_bytes.is_none_or(|n| batch.device_peak_bytes <= n);
    batch.candidates = vec![planning::PlanCandidate::from(&batch)];
    batch.layout = Some(layout);
    batch.forced_layout = true;
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
          self.device_peak(0, plan.device_record_bytes, 0) > n as u128
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
    let minimum_cells = batch.shard_cells as u128 + largest_row;
    batch.device_cells = options.device_cells()?;
    batch.device_budget_bytes = self.device_budget(options)?;
    batch.fits &= batch.device_cells.is_none_or(|n| minimum_cells <= n as u128)
      && batch.device_budget_bytes.is_none_or(|n| batch.device_peak_bytes <= n);
    if batch.fits {
      return Ok(None);
    }
    batch.shard_cells = minimum_cells.min(u64::MAX as u128) as u64;
    batch.candidates.push(planning::PlanCandidate::from(&batch));
    Ok(Some(batch))
  }

  fn plan_layout(
    &self,
    record: &Execution<B>,
    layout: &BatchLayout,
    budget: u64,
    resident: u64,
    policy: planning::RetentionPolicy,
    pipeline: Option<bool>,
  ) -> Result<planning::BatchPlan, String> {
    use planning::RetentionPolicy;
    let margin = |n: u128| n.saturating_mul(5).div_ceil(4);
    let bounded = |n: u128| n.min(u64::MAX as u128) as u64;
    let metadata = (layout.shards.len()
      * self.system.circuits.len()
      * std::mem::size_of::<CircuitSlice>()) as u128
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
    let generated: Vec<_> = (0..self.system.circuits.len())
      .map(|ci| self.generated_circuit(record, ci))
      .collect();
    #[cfg(feature = "cuda")]
    let device_record_bytes = self
      .device_plans_for(record)
      .map(|p| p.record_bytes(self, record))
      .transpose()?
      .unwrap_or(0);
    #[cfg(not(feature = "cuda"))]
    let device_record_bytes = 0;
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
    for shard in &layout.shards {
      let heights: Vec<_> =
        shard.circuits.iter().map(|slice| slice.height).collect();
      let main: u128 = heights
        .iter()
        .zip(&self.system.circuits)
        .enumerate()
        .map(
          |(ci, (&h, c))| {
            if generated[ci] { 0 } else { h as u128 * c.main_width as u128 }
          },
        )
        .sum();
      let cells: u128 = heights
        .iter()
        .zip(&self.system.circuits)
        .map(|(&h, c)| h as u128 * c.main_width as u128)
        .sum();
      let committed: u128 = heights
        .iter()
        .enumerate()
        .map(|(ci, &h)| h as u128 * self.committed_width(ci))
        .sum();
      shard_cells = shard_cells.max(committed);
      stage1_cells += cells;
      host_cells += main;
      let tallest = heights.iter().copied().max().unwrap_or(1).max(1);
      device_peak = device_peak.max(self.device_peak(
        committed,
        device_record_bytes,
        tallest,
      ));
      max_rows = max_rows.max(
        heights
          .iter()
          .enumerate()
          .filter(|(ci, _)| !self.fixed_circuit(*ci))
          .map(|(_, &h)| h)
          .max()
          .unwrap_or(1)
          .max(1),
      );
      let (cpu, saved, prep) = self.prove_allocation(&heights, tallest);
      retained += saved;
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
                + std::mem::size_of::<
                  multi_stark::lookup::LookupRowMut<'_, Val>,
                >() as u128)
          })
          .sum()
      };
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
    #[cfg(feature = "cuda")]
    let release_copy =
      if gpu::release_enabled() { u128::from(device_record_bytes) } else { 0 };
    #[cfg(not(feature = "cuda"))]
    let release_copy = 0u128;
    let base = resident as u128 + metadata + release_copy;
    let regenerated_peak = margin(base + generation.max(proving));
    let retained_peak = if layout.shards.len() == 1 {
      regenerated_peak
    } else {
      margin(base + retained_workspace + retained)
    };
    let retention = match policy {
      _ if self.requires_regeneration(layout.shards.len()) => {
        RetentionPolicy::Regenerate
      },
      RetentionPolicy::Auto if retained_peak <= budget as u128 => {
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
    let supplies = if retention == RetentionPolicy::Retain
      && !self.requires_regeneration(layout.shards.len())
    {
      layout.shards.len()
    } else {
      2 * layout.shards.len()
    };
    let pipelined_peak = peak + margin(lookahead);
    let pipelined = pipeline != Some(false)
      && supplies >= 2
      && pipelined_peak <= budget as u128;
    let peak = if pipelined { pipelined_peak } else { peak };
    Ok(planning::BatchPlan {
      max_rows,
      shards: layout.shards.len(),
      retention,
      budget_bytes: budget,
      stage1_cells: bounded(stage1_cells),
      generation_peak_bytes: bounded(margin(base + generation)),
      proving_peak_bytes: bounded(peak),
      fits: peak <= budget as u128,
      suggested_parts: usize::try_from(peak.div_ceil(budget as u128))
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
      retained_workspace_peak_bytes: Some(bounded(margin(
        base + retained_workspace,
      ))),
      pipelined,
      lookahead_bytes: bounded(lookahead),
      forced_layout: false,
    })
  }
}
