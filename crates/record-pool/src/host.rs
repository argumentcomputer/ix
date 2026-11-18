//! Host memory as the prover sizes it: the machine's total memory, less one
//! fixed reservation.
//!
//! Sizing deliberately ignores `MemAvailable` and cgroup limits. Free memory
//! changes with page cache, tmpfs and other processes, so deriving budgets
//! from it would give the same environment different partitions on the same
//! machine. A caller that runs the prover under a memory limit passes that
//! limit as an explicit budget instead.
use std::fs;

/// Percent of `MemTotal` reserved for the operating system, allocator pages
/// and transient buffers. It is the only reservation taken from the host:
/// records, prover workspaces and resident state all come out of the rest.
pub const RESERVED_PERCENT: usize = 20;

fn meminfo_bytes(meminfo: &str, field: &str) -> Option<usize> {
  let rest = meminfo.lines().find_map(|l| l.strip_prefix(field))?;
  let kib: usize = rest.trim().strip_suffix("kB")?.trim().parse().ok()?;
  kib.checked_mul(1024)
}

/// The machine's total memory (`MemTotal`), in bytes.
pub fn total_memory() -> Option<usize> {
  meminfo_bytes(&fs::read_to_string("/proc/meminfo").ok()?, "MemTotal:")
}

/// The default host budget for one prover process: `MemTotal` less
/// [`RESERVED_PERCENT`].
pub fn default_budget() -> Option<usize> {
  total_memory().map(|bytes| bytes / 100 * (100 - RESERVED_PERCENT))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn reads_total_not_available_memory() {
    let meminfo = "MemTotal:       261066088 kB\n\
                   MemFree:        160000000 kB\n\
                   MemAvailable:   216000000 kB\n";
    assert_eq!(meminfo_bytes(meminfo, "MemTotal:"), Some(261_066_088 * 1024));
    assert_eq!(meminfo_bytes(meminfo, "SwapTotal:"), None);
    assert_eq!(meminfo_bytes("MemTotal: junk kB\n", "MemTotal:"), None);
  }
}
