//! Division of the controller's host RAM between execution records and
//! proving workspace, fixed for the run.
//!
//! CUDA lanes follow legacy's GPU scheduler: a fixed workspace reserve per
//! lane sized from the committed-cell limit per shard, 10% headroom, and the
//! remainder to records. Records never borrow the workspace, so a completed
//! record can always be proven and released. Headroom also covers native
//! executors' stacks: at most a few hundred MB per execution (93 MB for an
//! Init leaf), released when the execution ends.
//!
//! CPU proving has no cell limit; its plans grow with the budget they are
//! given, so CPU lanes divide what remains after setup equally between
//! records and workspace until a CPU reserve is measured.
use serde::Serialize;

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum WorkspaceSource {
  /// CPU lanes: half of what remains after setup, shared by every lane.
  Half,
  /// CUDA lanes: legacy's per-lane formula for the controller's cell limit.
  Cells,
  /// CUDA lanes: `workspace_per_lane_bytes` from the controller config.
  Override,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct Allocation {
  /// `max_ram_bytes` as configured.
  pub requested_bytes: u64,
  /// The tightest visible cgroup limit, applied to CUDA controllers.
  pub cgroup_limit_bytes: Option<u64>,
  /// The allowance divided below.
  pub budget_bytes: u64,
  pub setup_rss_bytes: u64,
  pub setup_allowance_bytes: u64,
  pub headroom_bytes: u64,
  pub cell_limit: Option<u64>,
  pub workspace_source: WorkspaceSource,
  pub workspace_per_lane_bytes: u64,
  pub workspace_bytes: u64,
  pub record_bytes: u64,
}

/// Legacy's host workspace for one GPU lane proving shards of `cells`
/// committed cells: `ceil((16 × cells + 256 MiB) × 43 / 40)` bytes.
pub fn cell_workspace(cells: u64) -> Option<u64> {
  cells
    .checked_mul(16)?
    .checked_add(256 << 20)?
    .checked_mul(43)
    .map(|n| n.div_ceil(40))
}

pub struct Request {
  pub max_ram_bytes: u64,
  pub setup_rss_bytes: u64,
  pub lanes: usize,
  /// The committed-cell limit per shard of CUDA lanes; `None` for CPU lanes.
  pub cell_limit: Option<u64>,
  pub cgroup_limit_bytes: Option<u64>,
  pub workspace_per_lane_bytes: Option<u64>,
}

/// Resolve the record and workspace pools once, before any execution.
pub fn allocate(request: &Request) -> Result<Allocation, String> {
  let Request {
    max_ram_bytes,
    setup_rss_bytes,
    lanes,
    cell_limit,
    cgroup_limit_bytes,
    workspace_per_lane_bytes,
  } = *request;
  if lanes == 0 || max_ram_bytes == 0 {
    return Err("lanes and RAM must be positive".into());
  }
  let lanes = u64::try_from(lanes).map_err(|_| "lane count overflow")?;
  let Some(cells) = cell_limit else {
    if workspace_per_lane_bytes.is_some() {
      return Err("workspace_per_lane_bytes applies to CUDA lanes only".into());
    }
    let remaining = max_ram_bytes
      .checked_sub(setup_rss_bytes.saturating_mul(5) / 4)
      .ok_or("RAM budget cannot hold resident artifacts and prover systems")?;
    let half = remaining / 2;
    if half == 0 {
      return Err("no record capacity remains".into());
    }
    return Ok(Allocation {
      requested_bytes: max_ram_bytes,
      cgroup_limit_bytes: None,
      budget_bytes: max_ram_bytes,
      setup_rss_bytes,
      setup_allowance_bytes: max_ram_bytes - remaining,
      headroom_bytes: 0,
      cell_limit,
      workspace_source: WorkspaceSource::Half,
      workspace_per_lane_bytes: half / lanes,
      workspace_bytes: half,
      record_bytes: half,
    });
  };
  let budget =
    cgroup_limit_bytes.map_or(max_ram_bytes, |limit| max_ram_bytes.min(limit));
  let setup = setup_rss_bytes
    .checked_mul(5)
    .map(|n| n.div_ceil(4))
    .ok_or("setup allowance overflow")?;
  let headroom = budget / 10;
  let (per_lane, source) = match workspace_per_lane_bytes {
    Some(0) => return Err("workspace_per_lane_bytes must be positive".into()),
    Some(bytes) => (bytes, WorkspaceSource::Override),
    None => (
      cell_workspace(cells).ok_or("prover workspace budget overflow")?,
      WorkspaceSource::Cells,
    ),
  };
  let workspace =
    per_lane.checked_mul(lanes).ok_or("prover workspace budget overflow")?;
  let reserved = [setup, headroom, workspace]
    .into_iter()
    .try_fold(0u64, u64::checked_add)
    .ok_or("host budget overflow")?;
  let records =
    budget.checked_sub(reserved).filter(|&r| r > 0).ok_or_else(|| {
      format!(
        "host budget of {budget} bytes cannot hold setup ({setup}), headroom \
         ({headroom}) and {lanes} lanes of {per_lane}-byte workspace; raise \
         --max-ram, lower AIUR_TRACE_SHARD_MAX_CELLS, or set a smaller \
         AIUR_HOST_WORKSPACE_BYTES"
      )
    })?;
  Ok(Allocation {
    requested_bytes: max_ram_bytes,
    cgroup_limit_bytes,
    budget_bytes: budget,
    setup_rss_bytes,
    setup_allowance_bytes: setup,
    headroom_bytes: headroom,
    cell_limit,
    workspace_source: source,
    workspace_per_lane_bytes: per_lane,
    workspace_bytes: workspace,
    record_bytes: records,
  })
}

#[cfg(test)]
mod tests {
  use super::*;

  const GIB: u64 = 1 << 30;

  fn cuda() -> Request {
    Request {
      max_ram_bytes: 160 * GIB,
      setup_rss_bytes: 566_325_248,
      lanes: 1,
      cell_limit: Some(1_500_000_000),
      cgroup_limit_bytes: None,
      workspace_per_lane_bytes: None,
    }
  }

  fn cpu() -> Request {
    Request { cell_limit: None, ..cuda() }
  }

  /// The one-GPU, 160 GiB example from the allocation design.
  #[test]
  fn cuda_reserves_workspace_and_headroom_then_records() {
    let a = allocate(&cuda()).unwrap();
    assert_eq!(a.workspace_per_lane_bytes, 26_088_568_116);
    assert_eq!(a.headroom_bytes, 16 * GIB);
    assert_eq!(a.setup_allowance_bytes, 707_906_560);
    assert_eq!(
      a.setup_allowance_bytes
        + a.headroom_bytes
        + a.workspace_bytes
        + a.record_bytes,
      a.budget_bytes
    );
    // About 119.04 GiB of records, against 79.67 GiB from an equal split.
    assert_eq!(a.record_bytes / (GIB / 1000), 119_043);
  }

  #[test]
  fn cpu_divides_what_remains_after_setup() {
    let a = allocate(&cpu()).unwrap();
    let remaining = 160 * GIB - 566_325_248 * 5 / 4;
    assert_eq!(a.record_bytes, remaining / 2);
    assert_eq!(a.workspace_bytes, remaining / 2);
    assert_eq!(a.headroom_bytes, 0);
    assert_eq!(a.workspace_source, WorkspaceSource::Half);
    let two = allocate(&Request { lanes: 2, ..cpu() }).unwrap();
    assert_eq!(two.workspace_per_lane_bytes, remaining / 4);
  }

  #[test]
  fn lanes_scale_workspace_not_the_budget() {
    let a = allocate(&Request { lanes: 4, max_ram_bytes: 640 * GIB, ..cuda() })
      .unwrap();
    assert_eq!(a.budget_bytes, 640 * GIB);
    assert_eq!(a.workspace_bytes, 4 * a.workspace_per_lane_bytes);
  }

  #[test]
  fn cgroup_caps_only_cuda_budgets() {
    let limit = Some(100 * GIB);
    let a = allocate(&Request { cgroup_limit_bytes: limit, ..cuda() });
    assert_eq!(a.unwrap().budget_bytes, 100 * GIB);
    let a = allocate(&Request { cgroup_limit_bytes: limit, ..cpu() });
    assert_eq!(a.unwrap().budget_bytes, 160 * GIB);
  }

  #[test]
  fn overrides_and_insufficient_budgets() {
    let with = |bytes| Request { workspace_per_lane_bytes: bytes, ..cuda() };
    let a = allocate(&with(Some(10 * GIB))).unwrap();
    assert_eq!(a.workspace_source, WorkspaceSource::Override);
    assert_eq!(a.workspace_bytes, 10 * GIB);
    assert!(allocate(&with(Some(0))).is_err());
    assert!(allocate(&with(Some(200 * GIB))).is_err());
    assert!(
      allocate(&Request { cell_limit: Some(u64::MAX), ..cuda() }).is_err()
    );
    assert!(
      allocate(&Request { workspace_per_lane_bytes: Some(GIB), ..cpu() })
        .is_err()
    );
    assert!(allocate(&Request { max_ram_bytes: 1, ..cpu() }).is_err());
  }
}
