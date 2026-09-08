//! Host and cgroup-v2 headroom for IxVM admission. This is telemetry, not an
//! allocator limit: the supervisor must still enforce the hard memory cap.

use std::{
  fs,
  path::{Component, Path, PathBuf},
};

pub(super) const GIB: u64 = 1 << 30;
const MIB: u64 = 1 << 20;

#[derive(Clone, Copy, Debug)]
pub(super) struct Memory {
  pub capacity: u64,
  /// Minimum of host available RAM and every visible cgroup's headroom.
  pub available: u64,
  pub rss: u64,
  pub swap: u64,
  pub stall_us: u64,
  /// System-wide full memory PSI's ten-second average, in basis points.
  pub stall_avg10_bp: u64,
  /// Tightest visible cgroup constraint, for diagnostics (may be memory.high).
  pub cgroup: Option<(u64, u64)>,
}

impl Memory {
  pub(super) fn reserve(self) -> u64 {
    (self.capacity / 5).max(64 * MIB).min(self.capacity / 2)
  }

  pub(super) fn budget(self) -> u64 {
    self.available.saturating_sub(self.reserve())
  }

  fn constrain(&mut self, current: u64, limit: u64) {
    let headroom = limit.saturating_sub(current);
    self.capacity = self.capacity.min(limit);
    self.available = self.available.min(headroom);
    if self
      .cgroup
      .is_none_or(|(used, cap)| headroom <= cap.saturating_sub(used))
    {
      self.cgroup = Some((current, limit));
    }
  }
}

fn field(text: &str, key: &str) -> Result<u64, String> {
  text
    .lines()
    .find_map(|line| {
      line.strip_prefix(key)?.split_whitespace().next()?.parse().ok()
    })
    .ok_or_else(|| format!("missing or invalid {key} in memory telemetry"))
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

// Same mount/namespace resolution as the compiler's memory reader, but fail
// closed if a Linux memory hierarchy cannot be resolved instead of assuming
// the whole host is ours. Read all visible ancestors: siblings consume their
// parent's allowance even when our own memory.max is unlimited.
fn cgroup_dirs(groups: &str, mounts: &str) -> Result<Vec<PathBuf>, String> {
  let group = groups
    .lines()
    .find_map(|line| line.strip_prefix("0::"))
    .ok_or("IxVM adaptive memory admission requires cgroup v2 on Linux")?;
  let group = proc_path(group);
  if !group.is_absolute()
    || group.components().any(|c| c == Component::ParentDir)
  {
    return Err("invalid process cgroup path".into());
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
    if !mount.is_absolute()
      || mount.components().any(|c| c == Component::ParentDir)
    {
      continue;
    }
    let relative = if group == Path::new("/") {
      Path::new("")
    } else if let Ok(relative) = group.strip_prefix(&root) {
      relative
    } else {
      continue;
    };
    return Ok(
      mount
        .join(relative)
        .ancestors()
        .take_while(|p| p.starts_with(&mount))
        .map(Path::to_path_buf)
        .collect(),
    );
  }
  Err("cannot resolve the process's cgroup-v2 mount".into())
}

fn read(path: &Path) -> Result<String, String> {
  fs::read_to_string(path)
    .map_err(|e| format!("memory telemetry {}: {e}", path.display()))
}

fn optional_limit(path: &Path) -> Result<Option<u64>, String> {
  match fs::read_to_string(path) {
    Ok(s) if s.trim() == "max" => Ok(None),
    Ok(s) => s
      .trim()
      .parse()
      .map(Some)
      .map_err(|e| format!("invalid memory limit {}: {e}", path.display())),
    // The hierarchy root and groups without the memory controller need not
    // expose limit files. Other read errors must not remove a known cap.
    Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
    Err(e) => Err(format!("memory telemetry {}: {e}", path.display())),
  }
}

fn psi_full(text: &str) -> Result<(u64, u64), String> {
  let error = || "missing or invalid full memory PSI telemetry".to_owned();
  let full = text.lines().find(|l| l.starts_with("full ")).ok_or_else(error)?;
  let value = |key: &str| {
    full.split_whitespace().find_map(|v| v.strip_prefix(key)).ok_or_else(error)
  };
  let total =
    value("total=")?.parse::<u64>().map_err(|e| format!("{}: {e}", error()))?;
  // PSI prints percentages with two decimal places. Parse fixed point so
  // NaN, infinities and malformed telemetry cannot silently disable backoff.
  let (whole, fraction) = value("avg10=")?.split_once('.').ok_or_else(error)?;
  if fraction.len() != 2
    || !whole.bytes().chain(fraction.bytes()).all(|b| b.is_ascii_digit())
  {
    return Err(error());
  }
  let avg10 = whole
    .parse::<u64>()
    .ok()
    .and_then(|v| v.checked_mul(100))
    .and_then(|v| v.checked_add(fraction.parse::<u64>().ok()?))
    .filter(|&v| v <= 10_000)
    .ok_or_else(error)?;
  Ok((total, avg10))
}

fn optional_pressure(path: &Path) -> Result<(u64, u64), String> {
  pressure_result(path, fs::read_to_string(path))
}

fn pressure_result(
  path: &Path,
  result: std::io::Result<String>,
) -> Result<(u64, u64), String> {
  match result {
    Ok(text) => psi_full(&text),
    // PSI may be absent or disabled at boot (EOPNOTSUPP). Headroom and swap
    // checks still apply; other failures are not silently zero pressure.
    Err(e)
      if matches!(
        e.kind(),
        std::io::ErrorKind::NotFound | std::io::ErrorKind::Unsupported
      ) =>
    {
      Ok((0, 0))
    },
    Err(e) => Err(format!("memory telemetry {}: {e}", path.display())),
  }
}

pub(super) struct MemoryReader {
  cgroups: Vec<PathBuf>,
}

impl MemoryReader {
  /// No Linux telemetry on other operating systems: callers use a serial
  /// fallback, never silently open a full-width unmonitored pool.
  pub(super) fn new() -> Result<Option<Self>, String> {
    if !cfg!(target_os = "linux") {
      return Ok(None);
    }
    Ok(Some(Self {
      cgroups: cgroup_dirs(
        &read(Path::new("/proc/self/cgroup"))?,
        &read(Path::new("/proc/self/mountinfo"))?,
      )?,
    }))
  }

  pub(super) fn read(&self) -> Result<Memory, String> {
    let mem = read(Path::new("/proc/meminfo"))?;
    let status = read(Path::new("/proc/self/status"))?;
    let (stall_us, stall_avg10_bp) =
      optional_pressure(Path::new("/proc/pressure/memory"))?;
    let mut snapshot = Memory {
      capacity: field(&mem, "MemTotal:")?.saturating_mul(1024),
      available: field(&mem, "MemAvailable:")?.saturating_mul(1024),
      rss: field(&status, "VmRSS:")?.saturating_mul(1024),
      swap: field(&status, "VmSwap:")?.saturating_mul(1024),
      stall_us,
      stall_avg10_bp,
      cgroup: None,
    };
    self.constrain(&mut snapshot)?;
    Ok(snapshot)
  }

  fn constrain(&self, snapshot: &mut Memory) -> Result<(), String> {
    for dir in &self.cgroups {
      if !dir.is_dir() {
        return Err(format!("memory cgroup disappeared: {}", dir.display()));
      }
      // Re-read limits every sample, including previously unlimited parents.
      let limits = [
        optional_limit(&dir.join("memory.max"))?,
        optional_limit(&dir.join("memory.high"))?,
      ];
      if limits.iter().any(Option::is_some) {
        let current =
          read(&dir.join("memory.current"))?.trim().parse::<u64>().map_err(
            |e| format!("invalid memory.current at {}: {e}", dir.display()),
          )?;
        for limit in limits.into_iter().flatten() {
          snapshot.constrain(current, limit);
        }
      }
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests;
