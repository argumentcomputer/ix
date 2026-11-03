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

/// Committed cells (stage-one, stage-two and quotient columns over padded
/// rows) per trace shard that a CUDA prover plans to unless told otherwise.
/// This is the legacy lanes' `AIUR_TRACE_SHARD_MAX_CELLS` default, sized for
/// a 96 GB device: one such shard of the recursive verifier peaks near 33 GB.
pub const DEFAULT_DEVICE_CELLS: u64 = 1_500_000_000;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct Options {
  pub max_rows: Option<usize>,
  pub max_ram_bytes: Option<u64>,
  pub retention: RetentionPolicy,
  pub device: Option<i32>,
  /// Device-residency bound in committed cells per shard. CUDA builds
  /// default to `AIUR_TRACE_SHARD_MAX_CELLS`, then [`DEFAULT_DEVICE_CELLS`];
  /// CPU builds apply it only when given.
  pub max_cells: Option<u64>,
  /// False keeps the common-row layout while using incremental population.
  pub packing: Option<bool>,
  pub max_device_bytes: Option<u64>,
  /// Build the next shard's witness while the current one is committed or
  /// proven, when that extra shard fits the RAM budget (the default), or
  /// never (`false`). Either schedule produces the same proof bytes.
  pub pipeline: Option<bool>,
  /// Prove with this layout instead of planning one. Population placement
  /// changes the planner's estimates and therefore its layout, so runs
  /// compared byte for byte must share a layout.
  pub layout: Option<super::streaming::BatchLayout>,
  /// A JSON file holding a [`super::streaming::BatchLayout`], or a proof
  /// report whose `plan.layout` holds one; [`Options::read`] loads it into
  /// `layout`.
  pub layout_file: Option<String>,
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
    if let Some(path) = result.layout_file.take() {
      result.layout = Some(read_layout(&path)?);
    }
    result.max_ram_bytes = Some(result.max_ram_bytes.unwrap_or_else(|| {
      available_memory().map(|n| n / 100 * 85).unwrap_or(8 << 30)
    }));
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
    if self.max_cells == Some(0) {
      return Err("device cell budget must be positive".into());
    }
    if self.max_device_bytes == Some(0) {
      return Err("device RAM budget must be positive".into());
    }
    #[cfg(not(feature = "cuda"))]
    if self.device.is_some() {
      return Err("CUDA device requested from a CPU build".into());
    }
    if self.layout.is_some() && self.layout_file.is_some() {
      return Err("give either a layout or a layout file".into());
    }
    Ok(())
  }

  /// The layout to prove with, if the caller fixed one.
  pub fn forced_layout(
    &self,
  ) -> Result<Option<super::streaming::BatchLayout>, String> {
    match (&self.layout, &self.layout_file) {
      (Some(layout), _) => Ok(Some(layout.clone())),
      (None, Some(path)) => read_layout(path).map(Some),
      (None, None) => Ok(None),
    }
  }

  /// The committed-cell bound each shard is planned to, if any. A CUDA
  /// prover always runs on a device, so it is bounded even without an
  /// explicit device index; CPU proving is bounded only on request.
  pub fn device_cells(&self) -> Result<Option<u64>, String> {
    if self.max_cells.is_some() || !cfg!(feature = "cuda") {
      return Ok(self.max_cells);
    }
    configured_cells().map(Some)
  }
}

/// Read a layout file: a bare [`super::streaming::BatchLayout`], or a JSON
/// object holding one at `layout` or `plan.layout` (a proof report).
pub fn read_layout(
  path: &str,
) -> Result<super::streaming::BatchLayout, String> {
  let value: serde_json::Value = serde_json::from_slice(
    &std::fs::read(path).map_err(|e| format!("{path}: {e}"))?,
  )
  .map_err(|e| format!("{path}: {e}"))?;
  let layout = if value.get("shards").is_some() {
    value
  } else if let Some(layout) = value.get("layout") {
    layout.clone()
  } else if let Some(layout) = value.get("plan").and_then(|p| p.get("layout")) {
    layout.clone()
  } else {
    return Err(format!("{path}: no batch layout"));
  };
  serde_json::from_value(layout).map_err(|e| format!("{path}: {e}"))
}

/// The committed-cell limit per shard a controller sizes its workspace for:
/// `AIUR_TRACE_SHARD_MAX_CELLS`, otherwise [`DEFAULT_DEVICE_CELLS`].
pub fn configured_cells() -> Result<u64, String> {
  match std::env::var("AIUR_TRACE_SHARD_MAX_CELLS") {
    Ok(value) => {
      value.parse::<u64>().ok().filter(|&n| n > 0).ok_or_else(|| {
        "AIUR_TRACE_SHARD_MAX_CELLS must be a positive integer".into()
      })
    },
    Err(std::env::VarError::NotPresent) => Ok(DEFAULT_DEVICE_CELLS),
    Err(error) => Err(format!("AIUR_TRACE_SHARD_MAX_CELLS: {error}")),
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
/// The process's peak resident set (`VmHWM`), in bytes.
pub fn peak_resident_memory() -> u64 {
  status_bytes("VmHWM:")
}

pub fn resident_memory() -> u64 {
  status_bytes("VmRSS:")
}

fn status_bytes(field: &str) -> u64 {
  std::fs::read_to_string("/proc/self/status")
    .ok()
    .and_then(|s| {
      s.lines().find_map(|l| {
        l.strip_prefix(field)
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
  /// Committed cells of the largest shard, and the device bound it was
  /// planned against.
  #[serde(default)]
  pub shard_cells: u64,
  #[serde(default)]
  pub device_cells: Option<u64>,
  #[serde(default)]
  pub host_stage1_cells: u64,
  #[serde(default)]
  pub device_record_bytes: u64,
  #[serde(default)]
  pub device_peak_bytes: u64,
  #[serde(default)]
  pub device_budget_bytes: Option<u64>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub layout: Option<super::streaming::BatchLayout>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub population: Vec<PopulationStatistics>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub candidates: Vec<PlanCandidate>,
  #[serde(default)]
  pub retained_bytes: u64,
  /// Peak without retaining earlier shards, independent of the selected policy.
  #[serde(default)]
  pub regenerated_peak_bytes: Option<u64>,
  /// Workspace outside the current retained commitment; CUDA keeps its
  /// conservative host workspace because commitments may spill from device.
  #[serde(default)]
  pub retained_workspace_peak_bytes: Option<u64>,
  /// Whether proving builds one shard's witness ahead of the prover;
  /// `proving_peak_bytes` then includes that witness.
  #[serde(default)]
  pub pipelined: bool,
  /// Host bytes of the largest shard witness, which pipelining holds in
  /// addition to the shard being committed or proven.
  #[serde(default)]
  pub lookahead_bytes: u64,
  /// The layout came from the caller rather than the planner.
  #[serde(default)]
  pub forced_layout: bool,
}

/// Who writes a circuit's stage-one rows.
#[derive(
  Clone, Copy, Debug, Default, Deserialize, Serialize, PartialEq, Eq,
)]
#[serde(rename_all = "snake_case")]
pub enum PopulationProvider {
  /// Host population from the execution record.
  #[default]
  Cpu,
  /// `AIUR_GPU_TRACE=generated`: the CUDA plan interpreter.
  GpuInterpreter,
  /// `AIUR_GPU_TRACE=compiled`: a writer from a registered compiled bundle.
  GpuCodegen,
}

/// Why a circuit's rows are populated on the host.
#[derive(
  Clone, Copy, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord,
)]
#[serde(rename_all = "snake_case")]
pub enum HostCause {
  /// Device population is not enabled (or not built).
  DeviceDisabled,
  /// Device population is enabled, but `AIUR_GPU_TRACE_CIRCUITS` excludes
  /// this circuit.
  NotSelected,
  /// `AIUR_GPU_TRACE=compiled` selects only compiled writers, and the
  /// registered bundle has none for this circuit.
  NotCompiled,
  /// A member's plan stores to memory.
  Store,
  /// A member's plan loads from memory.
  Load,
  /// A member's plan reads a hint channel the device does not implement.
  UnsupportedHint,
  /// A member's plan calls a map the device does not implement.
  UnsupportedMap,
  /// A member's plan exceeds a limit of the device encoding.
  EncodingLimit,
  /// Some members could be filled on the device, but not all of them.
  IneligibleGroup,
  Rom,
  FixedTable,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PopulationStatistics {
  pub circuit: String,
  pub real_rows: usize,
  pub padded_rows: usize,
  pub stage1_cells: u64,
  pub generated: bool,
  #[serde(default)]
  pub provider: PopulationProvider,
  /// Empty when the circuit is generated on the device.
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub host_causes: Vec<HostCause>,
  pub reason: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PlanCandidate {
  pub rows: usize,
  pub shards: usize,
  pub shard_cells: u64,
  pub generation_peak_bytes: u64,
  pub proving_peak_bytes: u64,
  pub device_peak_bytes: u64,
  pub fits: bool,
}

impl From<&BatchPlan> for PlanCandidate {
  fn from(plan: &BatchPlan) -> Self {
    Self {
      rows: plan.max_rows,
      shards: plan.shards,
      shard_cells: plan.shard_cells,
      generation_peak_bytes: plan.generation_peak_bytes,
      proving_peak_bytes: plan.proving_peak_bytes,
      device_peak_bytes: plan.device_peak_bytes,
      fits: plan.fits,
    }
  }
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct RecordShape {
  pub heights: Vec<usize>,
  pub memory_intervals: Vec<(u64, u64, u64)>,
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
    let mut batch = self.plan_record_inner(record, options, resident)?;
    let rows = self.record_rows(record)?;
    batch.population = rows
      .iter()
      .zip(&self.system.circuits)
      .enumerate()
      .map(|(ci, (&real, circuit))| {
        let generated = self.generated_circuit(record, ci);
        let (causes, reason) = self.population_cause(record, ci);
        let padded_rows = padded(real)?;
        Ok(PopulationStatistics {
          circuit: self.names[ci].clone(),
          real_rows: real,
          padded_rows,
          stage1_cells: bounded(
            padded_rows as u128 * circuit.main_width as u128,
          ),
          generated,
          provider: self.population_provider(record, ci),
          host_causes: causes,
          reason,
        })
      })
      .collect::<Result<_, String>>()?;
    Ok(batch)
  }

  fn plan_record_inner(
    &self,
    record: &Execution<B>,
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    self.plan_incremental(record, options, resident)
  }

  #[cfg(feature = "cuda")]
  pub(super) fn device_plans_for(
    &self,
    _record: &Execution<B>,
  ) -> Option<&gpu::DevicePlans> {
    self
      .device_plans
      .as_ref()
      .filter(|plans| plans.circuits.iter().any(|&on| on))
  }

  /// Who populates circuit `ci`.
  pub(super) fn population_provider(
    &self,
    record: &Execution<B>,
    ci: usize,
  ) -> PopulationProvider {
    if !self.generated_circuit(record, ci) {
      return PopulationProvider::Cpu;
    }
    #[cfg(feature = "cuda")]
    if self
      .device_plans
      .as_ref()
      .and_then(gpu::DevicePlans::compiled)
      .is_some_and(|compiled| compiled.covers(ci))
    {
      return PopulationProvider::GpuCodegen;
    }
    PopulationProvider::GpuInterpreter
  }

  /// Why circuit `ci` is populated where it is, as categories and text.
  fn population_cause(
    &self,
    record: &Execution<B>,
    ci: usize,
  ) -> (Vec<HostCause>, String) {
    if self.generated_circuit(record, ci) {
      #[cfg(feature = "cuda")]
      if let Some(provider) = self
        .device_plans
        .as_ref()
        .and_then(|plans| plans.compiled()?.provider(ci))
      {
        return (vec![], provider);
      }
      (vec![], "generated on device".to_owned())
    } else if ci >= self.members.len() + self.tables.len() {
      (vec![HostCause::Rom], "ROM circuit".to_owned())
    } else if ci >= self.members.len() {
      (vec![HostCause::FixedTable], "fixed table".to_owned())
    } else {
      #[cfg(feature = "cuda")]
      if let Some(plans) = &self.device_plans {
        return plans.host_cause(self, ci);
      }
      (vec![HostCause::DeviceDisabled], "host population selected".to_owned())
    }
  }

  pub(super) fn generated_circuit(
    &self,
    record: &Execution<B>,
    ci: usize,
  ) -> bool {
    #[cfg(feature = "cuda")]
    {
      self
        .device_plans_for(record)
        .is_some_and(|plans| plans.circuits.get(ci).copied().unwrap_or(false))
    }
    #[cfg(not(feature = "cuda"))]
    {
      let _ = (record, ci);
      false
    }
  }

  pub fn record_shape(
    &self,
    record: &Execution<B>,
  ) -> Result<RecordShape, String> {
    self.plan.validate_record_shape(record)?;
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
      heights.push(padded(indices.len())?);
    }
    Ok(RecordShape { heights, memory_intervals })
  }

  pub fn plan_heights(
    &self,
    heights: &[usize],
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    self.plan_placed_heights(heights, options, resident, &[], 0)
  }

  fn plan_placed_heights(
    &self,
    heights: &[usize],
    options: &Options,
    resident: u64,
    generated: &[bool],
    device_record_bytes: u64,
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
    let host_cells: u128 = heights
      .iter()
      .zip(&self.system.circuits)
      .enumerate()
      .filter(|(ci, _)| !generated.get(*ci).copied().unwrap_or(false))
      .map(|(_, (&h, c))| h as u128 * c.main_width as u128)
      .sum();
    let descriptors: u128 = heights
      .iter()
      .enumerate()
      .filter(|(ci, _)| !generated.get(*ci).copied().unwrap_or(false))
      .map(|(_, &h)| h as u128 * 32)
      .sum();
    let upload = if generated.iter().any(|&on| on) { 256 << 20 } else { 0 };
    let generation =
      margin(u128::from(resident) + host_cells * 8 + descriptors + upload);
    let device_cells = options.device_cells()?;
    let device_budget = self.device_budget(options)?;
    let mut rows = options.max_rows.unwrap_or(tallest).min(tallest);
    let mut candidates = Vec::new();
    loop {
      let shards = tallest.div_ceil(rows);
      let shard_cells = self.shard_committed_cells(heights, rows);
      let device_peak =
        self.device_peak(shard_cells, device_record_bytes, rows);
      let (mut single, retained, prep) = self.prove_allocation(heights, rows);
      if cfg!(feature = "cuda") {
        single = self.placed_device_host_allocation(
          heights,
          rows,
          shards,
          options.retention == RetentionPolicy::Regenerate,
          generated,
        );
      }
      // Keep the observed RSS in this estimate even though the caller drops
      // its record. This conservatively covers artifact/advice residency and
      // allocator pages that are not returned to the operating system.
      let base = u128::from(resident) + host_cells * 8 + prep;
      let regenerated_peak = margin(base + single);
      let retained_peak =
        margin(base + single + retained * shards.saturating_sub(1) as u128);
      let retention = match options.retention {
        _ if self.requires_regeneration(shards) => RetentionPolicy::Regenerate,
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
      // Halving rows also bounds what one shard keeps on the device.
      let fits = generation.max(peak) <= u128::from(budget)
        && shards <= 65536
        && device_budget.is_none_or(|budget| device_peak <= u128::from(budget))
        && device_cells.is_none_or(|limit| shard_cells <= u128::from(limit));
      candidates.push(PlanCandidate {
        rows,
        shards,
        shard_cells: bounded(shard_cells),
        generation_peak_bytes: bounded(generation),
        proving_peak_bytes: bounded(peak),
        device_peak_bytes: bounded(device_peak),
        fits,
      });
      if fits
        || rows == 1
        || shards >= 65536
        || generation > u128::from(budget)
        || device_budget.is_some_and(|budget| {
          self.device_peak(0, device_record_bytes, 0) > u128::from(budget)
        })
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
          shard_cells: bounded(shard_cells),
          device_cells,
          host_stage1_cells: bounded(host_cells),
          device_record_bytes,
          device_peak_bytes: bounded(device_peak),
          device_budget_bytes: device_budget,
          layout: None,
          population: Vec::new(),
          candidates,
          retained_bytes: bounded(retained * shards as u128),
          regenerated_peak_bytes: Some(bounded(
            generation.max(regenerated_peak),
          )),
          retained_workspace_peak_bytes: None,
          pipelined: false,
          lookahead_bytes: 0,
          forced_layout: false,
        });
      }
      rows /= 2;
    }
  }

  pub(super) fn device_budget(
    &self,
    options: &Options,
  ) -> Result<Option<u64>, String> {
    if let Some(bytes) = options.max_device_bytes {
      return Ok(Some(bytes));
    }
    #[cfg(feature = "cuda")]
    return gpu::memory_budget(self.device).map(Some);
    #[cfg(not(feature = "cuda"))]
    Ok(None)
  }

  pub(super) fn device_peak(
    &self,
    cells: u128,
    record: u64,
    tallest: usize,
  ) -> u128 {
    #[cfg(feature = "cuda")]
    {
      let scratch =
        self.device_plans.as_ref().map_or(0, gpu::DevicePlans::scratch_bytes);
      let blowup = 1u128 << self.parameters.log_blowup;
      let fixed: u128 = self
        .system
        .circuits
        .iter()
        .map(|c| {
          c.preprocessed_height as u128
            * (8 * (1 + blowup) * c.preprocessed_width as u128 + 64 * blowup)
        })
        .sum();
      let height = tallest.max(
        self
          .system
          .circuits
          .iter()
          .map(|c| c.preprocessed_height)
          .max()
          .unwrap_or(0),
      );
      // Opening, FRI and Merkle buffers scale with the tallest LDE, even
      // when a narrow circuit consumes few committed cells.
      let opening = height as u128 * blowup * (192 + 160 + 88);
      margin(
        u128::from(record)
          + u128::from(scratch)
          + fixed
          + opening
          + cells * 8 * ((1u128 << self.parameters.log_blowup) + 1),
      )
    }
    #[cfg(not(feature = "cuda"))]
    {
      let _ = (cells, record, tallest);
      0
    }
  }

  /// Committed cells of the first (largest) shard: every function or memory
  /// circuit contributes at most `rows` padded rows, fixed tables their full
  /// domain. Counts stage-one, stage-two and quotient (extension) columns.
  fn shard_committed_cells(&self, heights: &[usize], rows: usize) -> u128 {
    heights
      .iter()
      .zip(&self.system.circuits)
      .map(|(&height, c)| {
        let n =
          if c.preprocessed_height == 0 { height.min(rows) } else { height };
        n as u128
          * (c.main_width + c.stage_2_width + 2 * c.quotient_degree()) as u128
      })
      .sum()
  }

  pub(super) fn prove_allocation(
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

  /// Host workspace when the CUDA prover commits, builds stage two and opens
  /// on the device; the CPU phases of [`Self::prove_allocation`] would
  /// overstate it several times. The host holds witnesses: shard traces and,
  /// unless the device derives them, their lookup buffers. A retained single
  /// shard takes its trace from the source matrices the caller already
  /// counts; otherwise the supplier copies it. With several shards, at most
  /// the shard being committed or proven and the next one are held, and
  /// shards after the first contain only the rows of taller circuits beyond
  /// the earlier shards. Upload staging is a constant. Retained multi-shard
  /// commitments keep the CPU model, since device pressure can spill them to
  /// the host. The large recursive verifier measured 25.0 GiB (host lookups)
  /// and 10.5 GiB (device lookups) peak RSS for one shard.
  #[cfg(all(test, feature = "cuda"))]
  pub(super) fn device_host_allocation(
    &self,
    heights: &[usize],
    rows: usize,
    shards: usize,
    regenerate: bool,
  ) -> u128 {
    self.placed_device_host_allocation(heights, rows, shards, regenerate, &[])
  }

  fn placed_device_host_allocation(
    &self,
    heights: &[usize],
    rows: usize,
    shards: usize,
    regenerate: bool,
    generated: &[bool],
  ) -> u128 {
    // Witness bytes of the first two shards: (trace, lookups) for each.
    let mut witness = [(0u128, 0u128); 2];
    for (ci, (&height, c)) in
      heights.iter().zip(&self.system.circuits).enumerate()
    {
      let args: u128 =
        c.graph.lookups.iter().map(|l| l.args.len() as u128).sum();
      let lookup_row = if self.gpu_lookup_only {
        0
      } else {
        8 * (c.num_lookups as u128 + args)
          + std::mem::size_of::<multi_stark::lookup::LookupRowMut<'_, Val>>()
            as u128
      };
      for (shard, (trace, lookups)) in witness.iter_mut().enumerate() {
        let n = if c.preprocessed_height == 0 {
          height.saturating_sub(shard * rows).min(rows)
        } else {
          height
        } as u128;
        if !generated.get(ci).copied().unwrap_or(false) {
          *trace += 8 * n * c.main_width as u128;
        }
        *lookups += n * lookup_row;
      }
    }
    let staging = 256 << 20;
    let [(trace, lookups), (next_trace, next_lookups)] = witness;
    match (shards, regenerate) {
      (1, false) => lookups + staging,
      (1, true) => trace + lookups + staging,
      _ => trace + lookups + next_trace + next_lookups + staging,
    }
  }
}
