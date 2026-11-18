pub(super) struct HostBudget {
  pub limit: usize,
  pub records: usize,
  pub workspace: usize,
  pub resident: usize,
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
  /// Splits the process-wide host budget into the lanes' prover workspaces,
  /// the resident bytes already loaded, and the shared record pool.
  /// `requested` is the explicit budget (`--max-ram`), 0 for `default`;
  /// `default` is [`record_pool::host::default_budget`], which already holds
  /// the one host reservation, so nothing further is set aside here.
  pub(super) fn new(
    lanes: usize,
    requested: usize,
    default: Option<usize>,
    workspace: usize,
    resident: usize,
  ) -> Result<Self, String> {
    if lanes == 0 || workspace == 0 {
      return Err("lanes and prover workspace must be positive".into());
    }
    let limit = if requested == 0 {
      default.ok_or("cannot read MemTotal; pass --max-ram")?
    } else {
      requested
    };
    let reserved = workspace
      .checked_mul(lanes)
      .and_then(|n| n.checked_add(resident))
      .ok_or("process workspace budget overflow")?;
    let records = limit.checked_sub(reserved)
      .ok_or("host budget cannot hold the GPU workers' workspace; raise --max-ram or lower AIUR_TRACE_SHARD_MAX_CELLS")?;
    if records == 0 {
      return Err("no host capacity remains for execution records".into());
    }
    Ok(Self { limit, records, workspace, resident })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn explicit_budget_is_process_wide_and_default_is_used_otherwise() {
    let gib = 1usize << 30;
    let workspace = cell_workspace(1_500_000_000).unwrap();
    assert_eq!(workspace, 26_088_568_116);
    let explicit =
      HostBudget::new(4, 230 * gib, Some(900 * gib), workspace, 0).unwrap();
    assert_eq!(explicit.limit, 230 * gib);
    assert_eq!(explicit.records + explicit.workspace * 4, explicit.limit);
    let default = HostBudget::new(4, 0, Some(800 * gib), workspace, 0).unwrap();
    assert_eq!(default.limit, 800 * gib);
    assert!(HostBudget::new(1, 0, None, workspace, 0).is_err());
    let one = cell_workspace(1).unwrap();
    assert!(HostBudget::new(4, usize::MAX, None, usize::MAX, 0).is_err());
    assert!(HostBudget::new(4, 1, None, one, 0).is_err());
  }

  #[test]
  fn resident_memory_is_set_aside_before_records() {
    let gib = 1usize << 30;
    let workspace = cell_workspace(1_500_000_000).unwrap();
    let without = HostBudget::new(1, 160 * gib, None, workspace, 0).unwrap();
    let with = HostBudget::new(1, 160 * gib, None, workspace, gib).unwrap();
    assert_eq!(without.records - with.records, gib);
    assert_eq!(with.records + with.workspace + with.resident, with.limit);
    assert!(HostBudget::new(1, 160 * gib, None, workspace, 200 * gib).is_err());
  }
}
