//! Host memory limits visible to this process.
use std::{
  fs,
  path::{Path, PathBuf},
};

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
pub fn cgroup_memory_limit() -> Option<usize> {
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
