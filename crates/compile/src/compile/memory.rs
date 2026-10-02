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
  /// This process's resident set plus its own swapped-out pages.
  pub(super) process: u64,
  /// This process's own swapped-out pages (`VmSwap`). Unlike system-wide
  /// swap, its growth means the kernel is reclaiming *this* process.
  pub(super) process_swap: u64,
  /// Cumulative "full" memory stall in microseconds of the innermost
  /// visible cgroup (system-wide PSI when that cgroup exposes none).
  pub(super) stall_us: u64,
}

impl Memory {
  pub(super) fn headroom(self, budget: Option<u64>) -> u64 {
    budget.map_or(self.available, |b| {
      self.available.min(b.saturating_sub(self.process))
    })
  }

  pub(super) fn reserve(self, budget: Option<u64>) -> u64 {
    let capacity = budget.map_or(self.capacity, |b| b.min(self.capacity));
    (capacity / 8).max(64 * MIB).min(capacity / 2)
  }
}

pub(super) fn field(text: &str, key: &str) -> Option<u64> {
  text.lines().find_map(|line| {
    line.strip_prefix(key)?.split_whitespace().next()?.parse().ok()
  })
}
/// The cumulative "full" stall total of a PSI file, if it has one.
pub(super) fn psi_total(text: &str) -> Option<u64> {
  text.lines().find(|line| line.starts_with("full ")).and_then(|line| {
    line.split_whitespace().find_map(|v| v.strip_prefix("total=")?.parse().ok())
  })
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

/// The memory PSI file closest to this process: the innermost visible
/// cgroup's `memory.pressure` when it is readable, else the system-wide one.
/// Chosen once, so the cumulative total never switches source mid-run.
fn psi_path(cgroups: &[PathBuf]) -> PathBuf {
  cgroups
    .first()
    .map(|leaf| leaf.join("memory.pressure"))
    .filter(|path| {
      std::fs::read_to_string(path).is_ok_and(|text| psi_total(&text).is_some())
    })
    .unwrap_or_else(|| PathBuf::from("/proc/pressure/memory"))
}

pub(super) struct MemoryReader {
  cgroups: Vec<PathBuf>,
  psi: PathBuf,
  /// Last stall total read; reused when a read fails, so a transient
  /// failure cannot fabricate a stall burst on the next good read.
  stall_us: u64,
}
impl MemoryReader {
  pub(super) fn new() -> Self {
    let cgroups = cgroup_dirs(
      &std::fs::read_to_string("/proc/self/cgroup").unwrap_or_default(),
      &std::fs::read_to_string("/proc/self/mountinfo").unwrap_or_default(),
    );
    let psi = psi_path(&cgroups);
    Self { cgroups, psi, stall_us: 0 }
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
    if let Some(total) =
      std::fs::read_to_string(&self.psi).ok().and_then(|text| psi_total(&text))
    {
      self.stall_us = total.max(self.stall_us);
    }
    let process_swap =
      field(&status, "VmSwap:").unwrap_or(0).saturating_mul(1024);
    Some(Memory {
      capacity,
      available,
      process: field(&status, "VmRSS:")?
        .saturating_mul(1024)
        .saturating_add(process_swap),
      process_swap,
      stall_us: self.stall_us,
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

/// This process's own swap-out counts below this many reserves of headroom.
///
/// With more headroom than that, swapping comes from LRU balancing against
/// other workloads' page cache: admitting fewer blocks does not cure it, and
/// the headroom itself shows that memory is not short.
const SWAP_HEADROOM: u64 = 4;
/// Memory stalls count below this many reserves of headroom. Stall time is
/// not attributable: the system-wide figure is every workload's, and the
/// innermost cgroup is often shared too (a terminal's or a build service's,
/// with every job started from it), and it includes refaults of this
/// process's own file mappings, which running fewer blocks does not cure.
/// Only where memory is genuinely short should every consumer back off.
const STALL_HEADROOM: u64 = 2;

/// Reclaim activity that this process should answer by running fewer
/// blocks: its own pages being swapped out (more than 8 MiB since the last
/// sample) below four reserves of headroom, or its innermost cgroup stalled
/// on memory for over a tenth of the interval below two. System-wide swap
/// traffic is never consulted. Headroom and reserve here are the system's or
/// cgroup's, never a process budget's: the kernel reclaims when memory is
/// short, not when this process nears its own soft budget, which the
/// callers enforce from headroom alone.
pub(super) fn reclaiming(
  now: Memory,
  before: Memory,
  elapsed: Duration,
) -> bool {
  let headroom = now.available;
  let reserve = now.reserve(None);
  let swapping = headroom < reserve.saturating_mul(SWAP_HEADROOM)
    && now.process_swap.saturating_sub(before.process_swap) > 8 * MIB;
  let stalled = headroom < reserve.saturating_mul(STALL_HEADROOM)
    && now.stall_us.saturating_sub(before.stall_us)
      > (elapsed.as_micros() as u64 / 10).max(1);
  swapping || stalled
}

pub(super) fn pressure(
  now: Memory,
  before: Memory,
  elapsed: Duration,
  budget: Option<u64>,
) -> Pressure {
  let reserve = now.reserve(budget);
  let available = now.headroom(budget);
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
