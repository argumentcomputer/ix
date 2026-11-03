pub(super) struct HostBudget {
  pub limit: usize,
  pub records: usize,
  pub workspace: usize,
  pub headroom: usize,
  pub resident: usize,
  pub initial: usize,
}

/// Legacy's host workspace for one lane proving shards of `cells`
/// committed cells: `ceil((16 × cells + 256 MiB) × 43 / 40)` bytes.
pub fn cell_workspace(cells: usize) -> Option<usize> {
  cells
    .checked_mul(16)?
    .checked_add(256 << 20)?
    .checked_mul(43)
    .map(|n| n.div_ceil(40))
}

impl HostBudget {
  pub(super) fn new(
    lanes: usize,
    executions: usize,
    per_lane: usize,
    detected: Option<usize>,
    ceiling: Option<usize>,
    workspace: usize,
    resident: usize,
  ) -> Result<Self, String> {
    if lanes == 0 || executions == 0 || workspace == 0 {
      return Err(
        "lanes, execution threads and prover workspace must be positive".into(),
      );
    }
    let requested = if per_lane == 0 {
      detected.ok_or("cannot detect host memory; specify --max-ram per GPU")?
    } else {
      per_lane.checked_mul(lanes).ok_or("process host budget overflow")?
    };
    let limit = ceiling.map_or(requested, |ceiling| requested.min(ceiling));
    let headroom = limit / 10;
    let reserved = workspace
      .checked_mul(lanes)
      .and_then(|n| n.checked_add(headroom))
      .and_then(|n| n.checked_add(resident))
      .ok_or("process workspace budget overflow")?;
    let records = limit.checked_sub(reserved)
      .ok_or("host budget cannot hold the GPU workers' workspace; raise --max-ram or lower AIUR_TRACE_SHARD_MAX_CELLS")?;
    let slots = lanes
      .checked_mul(2)
      .and_then(|n| n.checked_add(executions))
      .ok_or("record admission count overflow")?;
    let initial = records / slots;
    if initial == 0 {
      return Err("no host capacity remains for execution records".into());
    }
    Ok(Self { limit, records, workspace, headroom, resident, initial })
  }
}

pub(super) use record_pool::host::cgroup_memory_limit;

#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
#[allow(clippy::cast_sign_loss)] // MemAvailable and the fraction are positive
pub fn detected_ram_budget() -> Option<usize> {
  available_ram_bytes()
    .map(|b| (b as f64 * ixon::shard::RAM_USABLE_FRAC) as usize)
}

/// `MemAvailable` from `/proc/meminfo`, in bytes (Linux; includes
/// reclaimable page cache). `None` if unreadable — the caller then
/// disables the gate rather than guessing.
fn available_ram_bytes() -> Option<usize> {
  let s = std::fs::read_to_string("/proc/meminfo").ok()?;
  let rest = s.lines().find_map(|l| l.strip_prefix("MemAvailable:"))?;
  let kib: usize = rest.trim().trim_end_matches("kB").trim().parse().ok()?;
  Some(kib * 1024)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn per_lane_values_expand_once_and_auto_detection_is_global() {
    let gib = 1usize << 30;
    let workspace = cell_workspace(1_500_000_000).unwrap();
    assert_eq!(workspace, 26_088_568_116);
    let explicit =
      HostBudget::new(4, 12, 230 * gib, None, Some(920 * gib), workspace, 0)
        .unwrap();
    assert_eq!(explicit.limit, 920 * gib);
    assert_eq!(
      explicit.records + explicit.workspace * 4 + explicit.headroom,
      explicit.limit
    );
    assert_eq!(explicit.initial, explicit.records / 20);
    let auto =
      HostBudget::new(4, 12, 0, Some(800 * gib), Some(700 * gib), workspace, 0)
        .unwrap();
    assert_eq!(auto.limit, 700 * gib);
    let one = cell_workspace(1).unwrap();
    assert!(HostBudget::new(4, 12, usize::MAX, None, None, one, 0).is_err());
    assert!(HostBudget::new(4, 12, 1, None, None, one, 0).is_err());
  }

  #[test]
  fn resident_memory_is_set_aside_before_records() {
    let gib = 1usize << 30;
    let workspace = cell_workspace(1_500_000_000).unwrap();
    let without =
      HostBudget::new(1, 3, 160 * gib, None, None, workspace, 0).unwrap();
    let with =
      HostBudget::new(1, 3, 160 * gib, None, None, workspace, gib).unwrap();
    assert_eq!(without.records - with.records, gib);
    assert_eq!(
      with.records + with.workspace + with.headroom + with.resident,
      with.limit
    );
    assert!(
      HostBudget::new(1, 3, 160 * gib, None, None, workspace, 200 * gib)
        .is_err()
    );
  }
}
