//! Linux memory telemetry and pressure policy shared by both compilation stages.

use ixon::CompileError;
use std::path::{Path, PathBuf};
use std::time::Duration;

pub(super) const MIB: u64 = 1024 * 1024;
pub(super) const GIB: u64 = 1024 * MIB;

pub(super) fn budget_from_env(key: &str) -> Result<Option<u64>, CompileError> {
  std::env::var(key).ok().map(|value| parse_budget(key, &value)).transpose()
}

fn parse_budget(key: &str, value: &str) -> Result<u64, CompileError> {
  value
    .parse::<f64>()
    .ok()
    .filter(|v| v.is_finite() && *v > 0.0 && *v < (u64::MAX / GIB) as f64)
    .map(|v| {
      // The filter proves this is finite and positive.
      #[allow(clippy::cast_sign_loss)]
      let bytes = (v * GIB as f64) as u64;
      bytes
    })
    .filter(|&bytes| bytes > 0)
    .ok_or_else(|| {
      resource_error(format!("{key} must be a positive finite number"))
    })
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn memory_budget_rejects_invalid_and_unrepresentable_values() {
    for value in ["", "0", "-1", "nan", "inf", "1e50", "1e-100", "no"] {
      assert!(matches!(
        parse_budget("TEST", value),
        Err(CompileError::ResourceLimit { .. })
      ));
    }
    assert_eq!(parse_budget("TEST", "0.5").unwrap(), GIB / 2);
    assert_eq!(parse_budget("TEST", "100").unwrap(), 100 * GIB);
  }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Memory {
  pub(super) capacity: u64,
  pub(super) available: u64,
  pub(super) process: u64,
  pub(super) swap_used: u64,
  pub(super) stall_us: u64,
}

pub(super) fn field(text: &str, key: &str) -> Option<u64> {
  text.lines().find_map(|line| {
    line.strip_prefix(key)?.split_whitespace().next()?.parse().ok()
  })
}
pub(super) fn psi_total(text: &str) -> u64 {
  text
    .lines()
    .find(|line| line.starts_with("full "))
    .and_then(|line| {
      line
        .split_whitespace()
        .find_map(|v| v.strip_prefix("total=")?.parse().ok())
    })
    .unwrap_or(0)
}
fn proc_path(text: &str) -> PathBuf {
  PathBuf::from(
    text
      .replace("\\040", " ")
      .replace("\\011", "\t")
      .replace("\\012", "\n")
      .replace("\\134", "\\"),
  )
}

/// Resolve the unified cgroup relative to its visible mount, including
/// namespace roots and every visible ancestor's memory.max/memory.high.
pub(super) fn cgroup_dirs(cgroups: &str, mounts: &str) -> Vec<PathBuf> {
  let Some(group) = cgroups.lines().find_map(|line| line.strip_prefix("0::"))
  else {
    return Vec::new();
  };
  let group = proc_path(group);
  if group.components().any(|c| matches!(c, std::path::Component::ParentDir)) {
    return Vec::new();
  }
  for line in mounts.lines() {
    let Some((left, right)) = line.split_once(" - ") else {
      continue;
    };
    if right.split_whitespace().next() != Some("cgroup2") {
      continue;
    }
    let fields: Vec<_> = left.split_whitespace().collect();
    if fields.len() < 5 {
      continue;
    }
    let root = proc_path(fields[3]);
    let mount = proc_path(fields[4]);
    let relative = if group == Path::new("/") {
      Path::new("")
    } else if let Ok(relative) = group.strip_prefix(&root) {
      relative
    } else {
      continue;
    };
    let leaf = mount.join(relative);
    return leaf
      .ancestors()
      .take_while(|path| path.starts_with(&mount))
      .map(Path::to_path_buf)
      .collect();
  }
  Vec::new()
}

pub(super) struct MemoryReader {
  cgroups: Vec<PathBuf>,
}
impl MemoryReader {
  pub(super) fn new() -> Self {
    Self {
      cgroups: cgroup_dirs(
        &std::fs::read_to_string("/proc/self/cgroup").unwrap_or_default(),
        &std::fs::read_to_string("/proc/self/mountinfo").unwrap_or_default(),
      ),
    }
  }
  pub(super) fn read(&mut self) -> Option<Memory> {
    let mem = std::fs::read_to_string("/proc/meminfo").ok()?;
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let mut capacity = field(&mem, "MemTotal:")?.saturating_mul(1024);
    let mut available = field(&mem, "MemAvailable:")?.saturating_mul(1024);
    for dir in &self.cgroups {
      let current = std::fs::read_to_string(dir.join("memory.current"))
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok());
      for file in ["memory.max", "memory.high"] {
        if let (Some(current), Some(limit)) = (
          current,
          std::fs::read_to_string(dir.join(file))
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok()),
        ) {
          capacity = capacity.min(limit);
          available = available.min(limit.saturating_sub(current));
        }
      }
    }
    Some(Memory {
      capacity,
      available,
      process: field(&status, "VmRSS:")?
        .saturating_add(field(&status, "VmSwap:").unwrap_or(0))
        .saturating_mul(1024),
      swap_used: field(&mem, "SwapTotal:")?
        .saturating_sub(field(&mem, "SwapFree:")?)
        .saturating_mul(1024),
      stall_us: psi_total(
        &std::fs::read_to_string("/proc/pressure/memory").unwrap_or_default(),
      ),
    })
  }
}

pub(super) fn resource_error(reason: impl Into<String>) -> CompileError {
  CompileError::ResourceLimit { reason: reason.into() }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Pressure {
  Healthy,
  Hold,
  Backoff,
  Critical,
}

pub(super) fn reclaiming(
  now: Memory,
  before: Memory,
  elapsed: Duration,
) -> bool {
  let stalls = now.stall_us.saturating_sub(before.stall_us);
  stalls > (elapsed.as_micros() as u64 / 10).max(1)
    || now.swap_used.saturating_sub(before.swap_used) > 8 * MIB
}

pub(super) fn pressure(
  now: Memory,
  before: Memory,
  elapsed: Duration,
  budget: Option<u64>,
) -> Pressure {
  let capacity = budget.map_or(now.capacity, |b| b.min(now.capacity));
  let reserve = (capacity / 8).max(64 * MIB).min(capacity / 2);
  let available = budget.map_or(now.available, |b| {
    now.available.min(b.saturating_sub(now.process))
  });
  if available < reserve / 2 {
    return Pressure::Critical;
  }
  if available < reserve * 2 || reclaiming(now, before, elapsed) {
    Pressure::Backoff
  } else if available < reserve * 3 {
    Pressure::Hold
  } else {
    Pressure::Healthy
  }
}
