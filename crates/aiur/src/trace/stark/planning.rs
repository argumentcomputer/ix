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
/// Larger shards are admitted by a 96 GiB device but prove slower: their
/// taller rows grow the opening and FRI buffers.
pub const DEFAULT_DEVICE_CELLS: u64 = 1_500_000_000;

/// Rows per circuit per trace shard that a cell-bounded plan stays within
/// unless `max_rows` says otherwise. Of two layouts with the same committed
/// cells, the taller one proves slower: on an RTX PRO 6000, Init claim shards
/// of 1.5e9 cells took 30–32 s at 2^23 rows and 34.5–36 s at 2^24.
pub const DEFAULT_DEVICE_ROWS: usize = 1 << 23;

/// What [`Backend::fit_device_circuits`] found, for its report.
#[cfg(feature = "cuda")]
#[derive(Default)]
struct DeviceSearch {
  admission: crate::execute::Admission,
  device_circuits: usize,
  whole_bytes: u64,
  /// Shard cells, rows and shards of the host layout.
  host_layout: (u64, usize, usize),
  trials: usize,
}

#[cfg(feature = "cuda")]
impl DeviceSearch {
  fn report(&self, plan: &BatchPlan) {
    let count = self.admission.circuits.iter().filter(|&&on| on).count();
    let (cells, rows, shards) = self.host_layout;
    eprintln!(
      "[aiur/gpu] device record of {} circuits ({} B) does not fit at the \
       host layout of {shards} shards ({cells} cells, {rows} rows); \
       populating {count} of them on the device ({} B, {} candidates, {} \
       host stage-one cells); host peak {} of {} B, device peak {} of {:?} B",
      self.device_circuits,
      self.whole_bytes,
      plan.device_record_bytes,
      self.trials,
      plan.host_stage1_cells,
      plan.proving_peak_bytes,
      plan.budget_bytes,
      plan.device_peak_bytes,
      plan.device_budget_bytes,
    );
  }
}

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
  /// Prove with this layout instead of planning one. A planned layout is
  /// the one host population gets, whatever the population placement; a
  /// forced one is proven with the configured placement as given.
  pub layout: Option<streaming::BatchLayout>,
  /// A JSON file holding a [`super::streaming::BatchLayout`], or a proof
  /// report whose `plan.layout` holds one; [`Options::read`] loads it into
  /// `layout`.
  pub layout_file: Option<String>,
  /// Prove as one trace shard with every circuit active at these log2
  /// heights, in system circuit order; fixed tables keep their own heights.
  /// Every record that fits proves in the same shape, which is what a
  /// verifier circuit fixed in advance needs.
  pub fixed_log_heights: Option<Vec<u8>>,
  /// Plan exactly one trace shard. The committed-cell bound and the device
  /// budget do not apply: multi-stark admits device memory per phase and
  /// spills LDEs to the host when a phase does not fit, so a shard above
  /// the device model costs time, not correctness. The RAM budget still
  /// applies, and a record that cannot be one shard within it is refused.
  pub single_shard: bool,
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
      result.retention = match retention.map_or("auto", String::as_str) {
        "auto" => RetentionPolicy::Auto,
        "retain" => RetentionPolicy::Retain,
        "regenerate" => RetentionPolicy::Regenerate,
        _ => return Err("retention must be auto, retain or regenerate".into()),
      };
    }
    if let Some(path) = result.layout_file.take() {
      result.layout = Some(read_layout(&path)?);
    }
    result.max_ram_bytes = Some(
      result
        .max_ram_bytes
        .unwrap_or_else(|| default_budget().unwrap_or(8 << 30)),
    );
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
    if self.fixed_log_heights.is_some()
      && (self.layout.is_some() || self.layout_file.is_some())
    {
      return Err("give either a layout or fixed log-heights".into());
    }
    if self.single_shard
      && (self.layout.is_some()
        || self.layout_file.is_some()
        || self.fixed_log_heights.is_some())
    {
      return Err("a single-shard plan cannot also take a fixed layout".into());
    }
    Ok(())
  }

  /// The layout to prove with, if the caller fixed one.
  pub fn forced_layout(
    &self,
  ) -> Result<Option<streaming::BatchLayout>, String> {
    match (&self.layout, &self.layout_file) {
      (Some(layout), _) => Ok(Some(layout.clone())),
      (None, Some(path)) => read_layout(path).map(Some),
      (None, None) => Ok(None),
    }
  }

  /// The committed-cell bound each shard is planned to, if any. A CUDA
  /// prover always runs on a device, so it is bounded even without an
  /// explicit device index; CPU proving is bounded only on request. A
  /// single-shard plan is not bounded by cells.
  pub fn device_cells(&self) -> Result<Option<u64>, String> {
    if self.single_shard {
      return Ok(None);
    }
    if self.max_cells.is_some() || !cfg!(feature = "cuda") {
      return Ok(self.max_cells);
    }
    configured_cells().map(Some)
  }

  /// The row cap each shard is planned to: `max_rows` when given, otherwise
  /// [`DEFAULT_DEVICE_ROWS`] for a cell-bounded plan, and none otherwise.
  pub fn height_limit(&self) -> Result<Option<usize>, String> {
    if self.max_rows.is_some() {
      return Ok(self.max_rows);
    }
    Ok(self.device_cells()?.map(|_| DEFAULT_DEVICE_ROWS))
  }
}

/// Read a layout file: a bare [`super::streaming::BatchLayout`], or a JSON
/// object holding one at `layout` or `plan.layout` (a proof report).
pub fn read_layout(path: &str) -> Result<streaming::BatchLayout, String> {
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

/// The default host budget, `MemTotal` less the one host reservation
/// ([`record_pool::host::default_budget`]), in bytes.
pub fn default_budget() -> Option<u64> {
  record_pool::host::default_budget().and_then(|n| u64::try_from(n).ok())
}

/// GPUs this process can prove on, counted without initializing CUDA: the
/// NVIDIA driver's device entries, narrowed by `CUDA_VISIBLE_DEVICES`. Zero
/// in a build without CUDA.
pub fn gpu_count() -> usize {
  if !cfg!(feature = "cuda") {
    return 0;
  }
  let present = std::fs::read_dir("/proc/driver/nvidia/gpus")
    .map_or(0, |entries| entries.filter_map(Result::ok).count());
  match std::env::var("CUDA_VISIBLE_DEVICES") {
    Ok(visible) => visible_devices(&visible, present),
    Err(_) => present,
  }
}

/// The devices a `CUDA_VISIBLE_DEVICES` value selects out of `present`. As
/// in the CUDA runtime, the list ends at its first invalid entry.
pub(crate) fn visible_devices(visible: &str, present: usize) -> usize {
  visible
    .split(',')
    .map(str::trim)
    .take_while(|entry| {
      entry.parse::<usize>().is_ok_and(|index| index < present)
        || entry.starts_with("GPU-")
        || entry.starts_with("MIG-")
    })
    .count()
    .min(present)
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
  pub layout: Option<streaming::BatchLayout>,
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
  /// A member's plan reads a hint channel the device does not implement.
  UnsupportedHint,
  /// A member's plan calls a map the device does not implement.
  UnsupportedMap,
  /// A member's plan exceeds a limit of the device encoding.
  EncodingLimit,
  /// Some members could be filled on the device, but not all of them.
  IneligibleGroup,
  /// The record's device population does not fit at the layout host
  /// population gets, so the whole record stays on the host.
  DeviceLayout,
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
  u64::try_from(n).unwrap_or(u64::MAX)
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
    let mut batch = self.plan_population(record, options, resident)?;
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

  /// Plans the layout host population would get, and populates on the
  /// device at that layout, pipelined whenever the host plan is, when the
  /// whole device record fits there. Otherwise it admits the device
  /// circuits that fit ([`Self::fit_device_circuits`]) at that layout, or,
  /// on request, at a smaller one whose fuller admission is predicted to
  /// prove faster; the layout, and so the proof, then depends on device
  /// memory, as the cell and device budgets already make it. A record whose
  /// device plan fits no layout keeps host population. A record host population cannot prove
  /// at any layout is planned with device population, which needs less host
  /// memory. A layout the caller forces is planned as given.
  fn plan_population(
    &self,
    record: &Execution<B>,
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    record.host_population.set(false);
    record.host_population.set_circuits(None);
    record.host_population.set_sharded(false);
    #[cfg(feature = "cuda")]
    if self.device_plans_for(record).is_some()
      && options.forced_layout()?.is_none()
      && options.fixed_log_heights.is_none()
    {
      record.host_population.set(true);
      let host = self.plan_record_inner(record, options, resident)?;
      record.host_population.set(false);
      let Some(layout) = host.layout.clone().filter(|_| host.fits) else {
        return self.plan_record_inner(record, options, resident);
      };
      let keeps =
        |plan: &BatchPlan| plan.fits && (plan.pipelined || !host.pipelined);
      let mut device =
        self.plan_forced(record, layout.clone(), options, resident)?;
      if !keeps(&device) {
        // The whole record does not fit: upload one shard image at a time
        // (when the record's references allow it), whose images planning
        // charges instead.
        record.host_population.set_sharded(true);
        device = self.plan_forced(record, layout.clone(), options, resident)?;
      }
      if !keeps(&device) {
        // The executor and the prover plan a record under the same lane
        // options, so the prover reuses the executor's search.
        let key = format!(
          "{}|{resident}|{:?}",
          serde_json::to_string(options).map_err(|e| e.to_string())?,
          self.device_budget(options)?
        );
        let previous = record.host_population.admitted(&key);
        let mut search = true;
        if let Some(previous) = previous {
          // An earlier search that admitted nothing is not repeated.
          search = false;
          if previous.circuits.iter().any(|&on| on) {
            if let Some(reused) = self.plan_admission(
              record, &layout, &previous, options, resident, &keeps,
            )? {
              device = reused;
            } else {
              search = true;
            }
          }
        }
        if search {
          let found = self.fit_device_circuits(
            record, &layout, &host, options, resident, &keeps,
          )?;
          let plan = if found.admission.circuits.iter().any(|&on| on) {
            self.plan_admission(
              record,
              &layout,
              &found.admission,
              options,
              resident,
              &keeps,
            )?
          } else {
            None
          };
          if let Some(plan) = &plan
            && std::env::var_os("AIUR_POPULATION_REPORT").is_some()
          {
            found.report(plan);
          }
          record.host_population.set_admitted(
            key,
            if plan.is_some() {
              found.admission
            } else {
              crate::execute::Admission {
                circuits: vec![false; self.members.len()],
              }
            },
          );
          if let Some(plan) = plan {
            device = plan;
          }
        }
      }
      if keeps(&device) {
        device.forced_layout = false;
        device.candidates = host.candidates;
        return Ok(device);
      }
      record.host_population.set_circuits(None);
      record.host_population.set(true);
      return Ok(host);
    }
    self.plan_record_inner(record, options, resident)
  }

  /// The plan of `admission` for `record`, whose host layout is `layout`,
  /// if `keeps` accepts it. Sets the record's population override to the
  /// admitted circuits, or clears it when `None`.
  #[cfg(feature = "cuda")]
  pub(super) fn plan_admission(
    &self,
    record: &Execution<B>,
    layout: &streaming::BatchLayout,
    admission: &crate::execute::Admission,
    options: &Options,
    resident: u64,
    keeps: &impl Fn(&BatchPlan) -> bool,
  ) -> Result<Option<BatchPlan>, String> {
    let chosen = layout.clone();
    record.host_population.set_circuits(Some(admission.circuits.clone()));
    let plan = self.plan_forced(record, chosen, options, resident)?;
    if keeps(&plan) {
      return Ok(Some(plan));
    }
    record.host_population.set_circuits(None);
    Ok(None)
  }

  /// When the whole device record does not fit beside the host layout's
  /// shards, admits the device circuits that save the most host population
  /// per device byte, as many as `keeps` accepts: circuits are ranked by
  /// stage-one cells over the bytes admitting them alone holds, and admitted
  /// greedily in that order, skipping any whose plan `keeps` rejects. The
  /// host layout, and so the proof host population would make, is kept.
  /// Everything is planned from the layout's terms and the record's byte
  /// model, without reading the record again.
  #[cfg(feature = "cuda")]
  fn fit_device_circuits(
    &self,
    record: &Execution<B>,
    layout: &streaming::BatchLayout,
    host: &BatchPlan,
    options: &Options,
    resident: u64,
    keeps: &impl Fn(&BatchPlan) -> bool,
  ) -> Result<DeviceSearch, String> {
    let mut found = DeviceSearch {
      admission: crate::execute::Admission {
        circuits: vec![false; self.members.len()],
      },
      ..DeviceSearch::default()
    };
    let Some(plans) = self.device_plans.as_ref() else { return Ok(found) };
    let rows = self.record_rows(record)?;
    let model = if record.host_population.sharded() {
      plans.record_model_for(self, record, layout)?
    } else {
      plans.record_model(self, record)?
    };
    let mut ranked: Vec<(usize, f64)> = (0..plans.circuits.len())
      .filter(|&ci| plans.supports(record, ci) && rows[ci] != 0)
      .map(|ci| {
        let cells =
          padded(rows[ci])? as f64 * self.system.circuits[ci].main_width as f64;
        Ok((ci, cells / model.alone(ci).max(1) as f64))
      })
      .collect::<Result<_, String>>()?;
    ranked.sort_by(|a, b| b.1.total_cmp(&a.1).then(a.0.cmp(&b.0)));
    let mut whole = vec![false; plans.circuits.len()];
    for &(ci, _) in &ranked {
      whole[ci] = true;
    }
    let generated = |admitted: &[bool]| -> Vec<bool> {
      (0..self.system.circuits.len())
        .map(|ci| admitted.get(ci).copied().unwrap_or(false))
        .collect()
    };
    let plan = |terms: &streaming::LayoutTerms, admitted: &[bool]| {
      self.plan_forced_terms(
        terms,
        &generated(admitted),
        model.bytes(admitted),
        options,
        resident,
      )
    };
    let mut trials = 0;
    let mut admit = |terms: &streaming::LayoutTerms| {
      trials += 1;
      if keeps(&plan(terms, &whole)?) {
        return Ok::<_, String>(whole.clone());
      }
      // Runs of circuits are tested at once: a run that is accepted joins
      // whole, a rejected one is split in halves, so one circuit too large
      // to fit is skipped without giving up the smaller ones ranked after
      // it.
      let mut admitted = vec![false; plans.circuits.len()];
      let mut runs = vec![0..ranked.len()];
      while let Some(run) = runs.pop() {
        trials += 1;
        let mut trial = admitted.clone();
        for &(ci, _) in &ranked[run.clone()] {
          trial[ci] = true;
        }
        if keeps(&plan(terms, &trial)?) {
          admitted = trial;
        } else if run.len() > 1 {
          let middle = run.start + run.len() / 2;
          runs.push(middle..run.end);
          runs.push(run.start..middle);
        }
      }
      Ok(admitted)
    };
    let terms = self.layout_terms(layout);
    let admitted = admit(&terms)?;
    found.admission.circuits = admitted;
    found.device_circuits = ranked.len();
    found.whole_bytes = model.bytes(&whole);
    found.host_layout = (host.shard_cells, host.max_rows, host.shards);
    found.trials = trials;
    Ok(found)
  }

  fn plan_record_inner(
    &self,
    record: &Execution<B>,
    options: &Options,
    resident: u64,
  ) -> Result<BatchPlan, String> {
    let mut batch = self.plan_incremental(record, options, resident)?;
    if options.single_shard && batch.shards != 1 {
      batch.fits = false;
    }
    Ok(batch)
  }

  #[cfg(feature = "cuda")]
  pub(super) fn device_plans_for(
    &self,
    record: &Execution<B>,
  ) -> Option<&gpu::DevicePlans> {
    self
      .device_plans
      .as_ref()
      .filter(|plans| plans.circuits.iter().any(|&on| on))
      .filter(|_| !record.host_population.get())
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
        if plans.circuits[ci] && !plans.supports(record, ci) {
          return (
            vec![HostCause::UnsupportedHint],
            "the record binds no device data to its arena reads".to_owned(),
          );
        }
        if (record.host_population.get() || !record.host_population.admits(ci))
          && plans.circuits[ci]
        {
          return (
            vec![HostCause::DeviceLayout],
            "the device record does not fit at the host layout".to_owned(),
          );
        }
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
      self.device_plans_for(record).is_some_and(|plans| {
        plans.supports(record, ci) && record.host_population.admits(ci)
      })
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
    let mut memory_intervals = Vec::new();
    for &width in &self.rom.widths {
      let cells = record.memory.width_cells(width);
      if let Some(first) = cells.get(0) {
        let start = first.address as u64;
        let end = start
          .checked_add(cells.len() as u64)
          .ok_or("ROM boundary overflow")?;
        memory_intervals.push((width as u64, start, end));
      }
      heights.push(padded(self.rom.row_count_for_entries(width, cells.len()))?);
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
    let budget =
      options.max_ram_bytes.or_else(default_budget).unwrap_or(8 << 30).max(1);
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
      u128::from(resident) + host_cells * 8 + descriptors + upload;
    let device_cells = options.device_cells()?;
    let device_budget = self.device_budget(options)?;
    let mut rows = options.height_limit()?.unwrap_or(tallest).min(tallest);
    let mut candidates = Vec::new();
    loop {
      let shards = tallest.div_ceil(rows);
      let shard_cells = self.shard_committed_cells(heights, rows);
      let device_peak = self.device_peak(
        shard_cells,
        self.shard_population_cells(heights, rows),
        device_record_bytes,
        rows,
      );
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
      let regenerated_peak = base + single;
      let retained_peak =
        base + single + retained * shards.saturating_sub(1) as u128;
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
          self.device_peak(0, 0, device_record_bytes, 0) > u128::from(budget)
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

  #[cfg_attr(not(feature = "cuda"), allow(clippy::unnecessary_wraps))]

  pub(super) fn device_budget(
    &self,
    options: &Options,
  ) -> Result<Option<u64>, String> {
    if options.single_shard {
      return Ok(None);
    }
    if let Some(bytes) = options.max_device_bytes {
      return Ok(Some(bytes));
    }
    #[cfg(feature = "cuda")]
    return gpu::memory_budget(self.device).map(Some);
    #[cfg(not(feature = "cuda"))]
    Ok(None)
  }

  /// Device peak of a shard committing `cells` cells, `population_cells` of
  /// them stage-one and stage-two cells, with `tallest` rows and a device
  /// record of `record` bytes (zero without device population).
  ///
  /// Population and lookups need the device record, its launch workspaces,
  /// and the stage-one and stage-two LDEs together; the quotient and opening
  /// phases need every committed LDE but no record when it is releasable,
  /// since admission reclaims a releasable record before anything else. A
  /// pinned record is charged in both phases.
  pub(super) fn device_peak(
    &self,
    cells: u128,
    population_cells: u128,
    record: u64,
    tallest: usize,
  ) -> u128 {
    #[cfg(feature = "cuda")]
    {
      // `record` includes the population launch workspaces; a shard
      // without device population has neither.
      let population = u128::from(record);
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
      let lde = |cells: u128| cells * 8 * (blowup + 1);
      // No term carries a margin. The record and its workspaces are their
      // allocations' sizes (`gpu::DevicePlans::record_bytes`, at most 1%
      // above the device memory an Init upload measurably takes). The
      // fixed, opening and LDE terms are estimates that bound the measured
      // device high-water mark from above on an RTX PRO 6000: Init claim
      // shards of 1.5e9 cells modelled at 74.8 GB used at most 66.7 GB
      // host-populated, and with their whole 22 GB device record every
      // multi-stark phase admission left at least 7.2 GB free beyond its
      // target; a 2.1e9-cell root wrap modelled at 88.1 GB used at most
      // 71.1 GB. The stage-two (lookup) phase's temporaries are not modelled
      // beyond the population LDEs: an aggregate shard at 2^22 rows with a
      // 34 GB record needed 30 GB of them for one circuit, and its record
      // was released and uploaded again.
      let generation = population + fixed + opening + lde(population_cells);
      let pinned = if gpu::release_enabled() { 0 } else { population };
      let proving = pinned + fixed + opening + lde(cells);
      generation.max(proving)
    }
    #[cfg(not(feature = "cuda"))]
    {
      let _ = (cells, population_cells, record, tallest);
      0
    }
  }

  /// Committed cells of the first (largest) shard: every function or memory
  /// circuit contributes at most `rows` padded rows, fixed tables their full
  /// domain. Counts stage-one, stage-two and quotient (extension) columns.
  fn shard_committed_cells(&self, heights: &[usize], rows: usize) -> u128 {
    self.shard_cells_of(heights, rows, true)
  }

  /// [`Self::shard_committed_cells`] without the quotient columns.
  fn shard_population_cells(&self, heights: &[usize], rows: usize) -> u128 {
    self.shard_cells_of(heights, rows, false)
  }

  fn shard_cells_of(
    &self,
    heights: &[usize],
    rows: usize,
    quotient: bool,
  ) -> u128 {
    heights
      .iter()
      .zip(&self.system.circuits)
      .map(|(&height, c)| {
        let n =
          if c.preprocessed_height == 0 { height.min(rows) } else { height };
        let quotient = if quotient { 3 * c.quotient_degree() } else { 0 };
        n as u128 * (c.main_width + c.stage_2_width + quotient) as u128
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
        + n * size_of::<multi_stark::lookup::LookupRowMut<'_, Val>>() as u128;
      lde += 8 * b * n * main;
      lookups += 8 * n * (count + args);
      messages += 32 * n * count;
      stage2 += 8 * n * c.stage_2_width as u128;
      committed += 8
        * b
        * n
        * (main + c.stage_2_width as u128 + 3 * c.quotient_degree() as u128);
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
          + size_of::<multi_stark::lookup::LookupRowMut<'_, Val>>() as u128
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
