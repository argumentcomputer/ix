use std::{
  fs,
  path::{Path, PathBuf},
};

pub(super) struct HostBudget {
  pub limit: usize,
  pub records: usize,
  pub workspace: usize,
  pub headroom: usize,
  pub initial: usize,
}

impl HostBudget {
  pub(super) fn new(
    lanes: usize,
    executions: usize,
    per_lane: usize,
    detected: Option<usize>,
    ceiling: Option<usize>,
    cells: usize,
  ) -> Result<Self, String> {
    if lanes == 0 || executions == 0 || cells == 0 {
      return Err(
        "lanes, execution threads and trace-cell budget must be positive"
          .into(),
      );
    }
    let requested = if per_lane == 0 {
      detected.ok_or("cannot detect host memory; specify --max-ram per GPU")?
    } else {
      per_lane.checked_mul(lanes).ok_or("process host budget overflow")?
    };
    let limit = ceiling.map_or(requested, |ceiling| requested.min(ceiling));
    let workspace = cells
      .checked_mul(16)
      .and_then(|n| n.checked_add(256 << 20))
      .and_then(|n| n.checked_mul(43))
      .map(|n| n.div_ceil(40))
      .ok_or("prover workspace budget overflow")?;
    let headroom = limit / 10;
    let reserved = workspace
      .checked_mul(lanes)
      .and_then(|n| n.checked_add(headroom))
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
    Ok(Self { limit, records, workspace, headroom, initial })
  }
}

fn memory_limit_at(mount: &Path, group: &Path) -> Option<usize> {
  let mut limit = None;
  for path in group.ancestors().take_while(|path| path.starts_with(mount)) {
    if let Some(bytes) = fs::read_to_string(path.join("memory.max"))
      .ok()
      .and_then(|s| s.trim().parse::<usize>().ok())
    {
      limit = Some(limit.map_or(bytes, |old: usize| old.min(bytes)));
    }
  }
  limit
}

/// The tightest visible cgroup-v2 ancestor limit, also respecting a
/// cgroup namespace whose mount starts below the hierarchy root.
pub(super) fn cgroup_memory_limit() -> Option<usize> {
  let membership = fs::read_to_string("/proc/self/cgroup").ok()?;
  let group = membership.lines().find_map(|line| line.strip_prefix("0::"))?;
  let mounts = fs::read_to_string("/proc/self/mountinfo").ok()?;
  let mut limit = None;
  for line in mounts.lines() {
    let Some((fields, _)) = line.split_once(" - cgroup2 ") else { continue };
    let fields: Vec<_> = fields.split_whitespace().collect();
    let (Some(root), Some(mount)) = (fields.get(3), fields.get(4)) else {
      continue;
    };
    let mount = PathBuf::from(mount.replace("\\040", " "));
    let root = PathBuf::from(root.replace("\\040", " "));
    let relative = Path::new(group).strip_prefix(&root).ok()?;
    if let Some(bytes) = memory_limit_at(&mount, &mount.join(relative)) {
      limit = Some(limit.map_or(bytes, |old: usize| old.min(bytes)));
    }
  }
  limit
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn per_lane_values_expand_once_and_auto_detection_is_global() {
    let gib = 1usize << 30;
    let explicit =
      HostBudget::new(4, 12, 230 * gib, None, Some(920 * gib), 1_500_000_000)
        .unwrap();
    assert_eq!(explicit.limit, 920 * gib);
    assert_eq!(
      explicit.records + explicit.workspace * 4 + explicit.headroom,
      explicit.limit
    );
    assert_eq!(explicit.initial, explicit.records / 20);
    let auto = HostBudget::new(
      4,
      12,
      0,
      Some(800 * gib),
      Some(700 * gib),
      1_500_000_000,
    )
    .unwrap();
    assert_eq!(auto.limit, 700 * gib);
    assert!(HostBudget::new(4, 12, usize::MAX, None, None, 1).is_err());
    assert!(HostBudget::new(4, 12, 1, None, None, 1).is_err());
  }

  #[test]
  fn cgroup_parent_limit_applies_when_leaf_is_unlimited() {
    let mount = std::env::temp_dir()
      .join(format!("ix-record-cgroup-{}", std::process::id()));
    let group = mount.join("parent/leaf");
    fs::create_dir_all(&group).unwrap();
    fs::write(mount.join("memory.max"), "1000\n").unwrap();
    fs::write(mount.join("parent/memory.max"), "800\n").unwrap();
    fs::write(group.join("memory.max"), "max\n").unwrap();
    assert_eq!(memory_limit_at(&mount, &group), Some(800));
    fs::write(group.join("memory.max"), "600\n").unwrap();
    assert_eq!(memory_limit_at(&mount, &group), Some(600));
    fs::remove_dir_all(mount).unwrap();
  }
}
