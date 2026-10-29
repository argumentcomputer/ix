//! Shared resource planning for IxVM and recursive proofs. The model follows
//! multi-stark's allocation phases; it is an estimate, not an allocator limit.
use super::*;
use multi_stark::batch::Retention;
use serde::{Deserialize, Serialize};

#[derive(
  Clone, Copy, Debug, Default, Deserialize, Serialize, PartialEq, Eq,
)]
#[serde(rename_all = "lowercase")]
pub enum RetentionPolicy {
  Retain,
  Regenerate,
  #[default]
  Auto,
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct Options {
  pub max_rows: Option<usize>,
  pub max_ram_bytes: Option<u64>,
  pub retention: RetentionPolicy,
  pub device: Option<i32>,
}
impl Options {
  pub fn read(
    path: Option<&String>,
    rows: Option<&String>,
    retention: Option<&String>,
  ) -> Result<Self, String> {
    let mut result = if let Some(path) = path {
      serde_json::from_slice(&std::fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?
    } else {
      Self::default()
    };
    if path.is_none() {
      result.max_rows = rows
        .map(|s| s.parse::<usize>().map_err(|e| e.to_string()))
        .transpose()?
        .filter(|&n| n != 0);
      result.retention = match retention.map(String::as_str).unwrap_or("auto") {
        "auto" => RetentionPolicy::Auto,
        "retain" => RetentionPolicy::Retain,
        "regenerate" => RetentionPolicy::Regenerate,
        _ => return Err("retention must be auto, retain or regenerate".into()),
      };
    }
    result.validate()?;
    Ok(result)
  }
  pub fn validate(&self) -> Result<(), String> {
    if self.max_rows.is_some_and(|n| n == 0 || !n.is_power_of_two()) {
      return Err("shard rows must be a positive power of two".into());
    }
    if self.max_ram_bytes == Some(0) {
      return Err("RAM budget must be positive".into());
    }
    if self.device.is_some_and(|d| d < 0) {
      return Err("negative CUDA device".into());
    }
    #[cfg(not(feature = "cuda"))]
    if self.device.is_some() {
      return Err("CUDA device requested from a CPU build".into());
    }
    Ok(())
  }
}

pub fn available_memory() -> Option<u64> {
  let text = std::fs::read_to_string("/proc/meminfo").ok()?;
  let host = text
    .lines()
    .find_map(|l| {
      l.strip_prefix("MemAvailable:")
        .and_then(|s| s.split_whitespace().next()?.parse::<u64>().ok())
    })?
    .checked_mul(1024)?;
  // Respect a container limit when cgroup v2 is mounted at its namespace root.
  let container = std::fs::read_to_string("/sys/fs/cgroup/memory.max")
    .ok()
    .and_then(|s| s.trim().parse::<u64>().ok())
    .zip(
      std::fs::read_to_string("/sys/fs/cgroup/memory.current")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok()),
    )
    .map(|(limit, used)| limit.saturating_sub(used));
  Some(container.map_or(host, |n| n.min(host)))
}
pub fn resident_memory() -> u64 {
  std::fs::read_to_string("/proc/self/status")
    .ok()
    .and_then(|s| {
      s.lines().find_map(|l| {
        l.strip_prefix("VmRSS:")
          .and_then(|v| v.split_whitespace().next()?.parse::<u64>().ok())
      })
    })
    .unwrap_or(0)
    .saturating_mul(1024)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BatchPlan {
  pub max_rows: usize,
  pub shards: usize,
  pub retention: RetentionPolicy,
  pub budget_bytes: u64,
  pub stage1_cells: u64,
  pub generation_peak_bytes: u64,
  pub proving_peak_bytes: u64,
  pub fits: bool,
  pub suggested_parts: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct RecordShape {
  pub heights: Vec<usize>,
  pub memory_intervals: Vec<(u64, u64, u64)>,
}

#[derive(Clone, Debug, Serialize)]
pub struct StreamResources {
  pub retention: RetentionPolicy,
  pub peak_bytes: u64,
  pub budget_bytes: u64,
  pub fits: bool,
}
impl BatchPlan {
  pub fn retention(&self) -> Retention {
    match self.retention {
      RetentionPolicy::Retain => Retention::Retain,
      _ => Retention::Regenerate,
    }
  }
}

fn padded(n: usize) -> Result<usize, String> {
  if n == 0 {
    Ok(0)
  } else {
    n.checked_next_power_of_two().ok_or_else(|| "trace height overflow".into())
  }
}
fn bounded(n: u128) -> u64 {
  n.min(u128::from(u64::MAX)) as u64
}
fn margin(n: u128) -> u128 {
  n.saturating_mul(5).div_ceil(4)
}

impl<B: WitnessField> Backend<'_, '_, B> {
  /// Multiple records share a batch transcript, but only one record's input
  /// matrices are resident at a time. Retained commitments accumulate across
  /// *all* records, so per-record retention decisions would undercount RAM.
  /// Shared artifacts and execution storage are charged by the controller.
  pub fn plan_stream(
    &self,
    records: &[(&[usize], usize)],
    options: &Options,
  ) -> Result<StreamResources, String> {
    options.validate()?;
    if records.is_empty() {
      return Err("stream has no records".into());
    }
    let budget = options.max_ram_bytes.unwrap_or(8 << 30);
    let mut regenerated_peak = 0;
    let mut retained_total = 0;
    let mut shards = 0usize;
    for &(heights, rows) in records {
      let plan = self.plan_heights(
        heights,
        &Options {
          max_rows: Some(rows),
          retention: RetentionPolicy::Regenerate,
          ..options.clone()
        },
        0,
      )?;
      if plan.max_rows != rows {
        return Err("stream rows changed during planning".into());
      }
      shards =
        shards.checked_add(plan.shards).ok_or("stream shard overflow")?;
      regenerated_peak = regenerated_peak
        .max(u128::from(plan.proving_peak_bytes))
        .max(u128::from(plan.generation_peak_bytes));
      let (_, retained, _) = self.prove_allocation(heights, rows);
      retained_total += retained * plan.shards as u128;
    }
    // Includes the current shard twice, conservatively; the same stage-one
    // allocation model is used for ordinary batches above.
    let retained_peak = regenerated_peak + margin(retained_total);
    let retention = match options.retention {
      _ if self.gpu_lookup_only => RetentionPolicy::Regenerate,
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
    Ok(StreamResources {
      retention,
      peak_bytes: bounded(peak),
      budget_bytes: budget,
      fits: peak <= u128::from(budget) && shards <= 65536,
    })
  }

  /// The fixed-table floor plus the caller's artifact/setup residency. An
  /// environment split cannot shrink these allocations.
  pub fn plan_fixed(
    &self,
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    let heights: Vec<_> =
      self.system.circuits.iter().map(|c| c.preprocessed_height).collect();
    self.plan_heights(&heights, options, resident)
  }

  /// Plan from the record before allocating the stage-one matrices. The RSS
  /// term includes the caller's advice/program residency and execution record.
  pub fn plan_batch(
    &self,
    record: &Execution<B>,
    options: &Options,
  ) -> Result<BatchPlan, String> {
    self.plan_record(record, options, resident_memory())
  }

  /// Resident controllers charge shared artifacts and execution records to
  /// their pool; the workspace plan receives only residency not charged there.
  pub fn plan_record(
    &self,
    record: &Execution<B>,
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    options.validate()?;
    self.plan_heights(&self.record_shape(record)?.heights, options, resident)
  }

  pub fn record_shape(
    &self,
    record: &Execution<B>,
  ) -> Result<RecordShape, String> {
    let mut heights = Vec::new();
    for members in &self.members {
      heights.push(padded(
        members.iter().map(|&i| record.queries.tables[i].len()).sum(),
      )?);
    }
    heights.extend(
      self
        .system
        .circuits
        .iter()
        .skip(heights.len())
        .take(self.tables.len())
        .map(|c| c.preprocessed_height),
    );
    let memory_start = heights.len();
    let mut counts = std::collections::BTreeMap::<usize, usize>::new();
    for entry in record.memory.iter() {
      *counts.entry(entry.cell.value.len()).or_default() += 1;
    }
    let mut memory_intervals = Vec::new();
    for c in &self.system.circuits[memory_start..] {
      let width = c.main_width - 3;
      let indices = record.memory.indices_for_width(width);
      if let Some(&first) = indices.first() {
        let start = record.memory.get(first).unwrap().address as u64;
        let end = start
          .checked_add(indices.len() as u64)
          .ok_or("ROM boundary overflow")?;
        memory_intervals.push((width as u64, start, end));
      }
      heights
        .push(padded(counts.get(&(c.main_width - 3)).copied().unwrap_or(0))?);
    }
    Ok(RecordShape { heights, memory_intervals })
  }

  pub fn plan_heights(
    &self,
    heights: &[usize],
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    options.validate()?;
    if heights.len() != self.system.circuits.len()
      || heights.iter().any(|&h| h != 0 && !h.is_power_of_two())
    {
      return Err("invalid planning heights".into());
    }
    let budget = options
      .max_ram_bytes
      .or_else(|| available_memory().map(|n| n / 100 * 85))
      .unwrap_or(8 << 30)
      .max(1);
    if heights
      .iter()
      .zip(&self.system.circuits)
      .any(|(&h, c)| c.preprocessed_height != 0 && h != c.preprocessed_height)
    {
      return Err("planning changed a fixed table's height".into());
    }
    let tallest = heights
      .iter()
      .zip(&self.system.circuits)
      .filter(|(_, c)| c.preprocessed_height == 0)
      .map(|(&h, _)| h)
      .max()
      .unwrap_or(1)
      .max(1);
    let cells: u128 = heights
      .iter()
      .zip(&self.system.circuits)
      .map(|(&h, c)| h as u128 * c.main_width as u128)
      .sum();
    // Row descriptors and the ROM inverse index are temporary population data.
    let descriptors: u128 = heights.iter().map(|&h| h as u128 * 32).sum();
    let generation = margin(u128::from(resident) + cells * 8 + descriptors);
    let mut rows = options.max_rows.unwrap_or(tallest).min(tallest);
    loop {
      let shards = tallest.div_ceil(rows);
      let (single, retained, prep) = self.prove_allocation(heights, rows);
      // Keep the observed RSS in this estimate even though the caller drops
      // its record. This conservatively covers artifact/advice residency and
      // allocator pages that are not returned to the operating system.
      let base = u128::from(resident) + cells * 8 + prep;
      let regenerated_peak = margin(base + single);
      let retained_peak =
        margin(base + single + retained * shards.saturating_sub(1) as u128);
      let retention = match options.retention {
        _ if self.gpu_lookup_only => RetentionPolicy::Regenerate,
        RetentionPolicy::Auto if retained_peak <= u128::from(budget) => {
          RetentionPolicy::Retain
        },
        RetentionPolicy::Auto => RetentionPolicy::Regenerate,
        x => x,
      };
      let peak = if retention == RetentionPolicy::Retain {
        retained_peak
      } else {
        regenerated_peak
      };
      let fits = generation.max(peak) <= u128::from(budget) && shards <= 65536;
      if fits || rows == 1 || shards >= 65536 || generation > u128::from(budget)
      {
        return Ok(BatchPlan {
          max_rows: rows,
          shards,
          retention,
          budget_bytes: budget,
          stage1_cells: bounded(cells),
          generation_peak_bytes: bounded(generation),
          proving_peak_bytes: bounded(peak),
          fits,
          suggested_parts: usize::try_from(
            generation.max(peak).div_ceil(u128::from(budget)),
          )
          .unwrap_or(usize::MAX)
          .max(1),
        });
      }
      rows /= 2;
    }
  }

  fn prove_allocation(
    &self,
    heights: &[usize],
    rows: usize,
  ) -> (u128, u128, u128) {
    let b = 1u128 << self.parameters.log_blowup;
    let (
      mut witness,
      mut lde,
      mut lookups,
      mut messages,
      mut stage2,
      mut committed,
      mut prep,
      mut tallest,
    ) = (0u128, 0, 0, 0, 0, 0, 0, 0);
    for (&height, c) in heights.iter().zip(&self.system.circuits) {
      let n = if c.preprocessed_height == 0 { height.min(rows) } else { height }
        as u128;
      if n == 0 {
        continue;
      }
      tallest = tallest.max(n);
      let count = c.num_lookups as u128;
      let args: u128 =
        c.graph.lookups.iter().map(|l| l.args.len() as u128).sum();
      let main = c.main_width as u128;
      witness += 8 * n * (main + count + args)
        + n
          * std::mem::size_of::<multi_stark::lookup::LookupRowMut<'_, Val>>()
            as u128;
      lde += 8 * b * n * main;
      lookups += 8 * n * (count + args);
      messages += 32 * n * count;
      stage2 += 8 * n * c.stage_2_width as u128;
      committed += 8
        * b
        * n
        * (main + c.stage_2_width as u128 + 2 * c.quotient_degree() as u128);
      prep += 8
        * (1 + b)
        * c.preprocessed_width as u128
        * c.preprocessed_height as u128
        + 64 * b * c.preprocessed_height as u128;
    }
    let h = b * tallest;
    let retained = lde + 64 * h + lookups;
    let phase2 = retained + messages + stage2;
    let open = committed + 192 * h + 160 * h + 88 * h;
    (witness.max(phase2).max(open), retained, prep)
  }
}
