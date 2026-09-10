//! NUMA domains as scheduling lanes.
//!
//! A single STARK prove cannot use more than one SNC/NUMA domain's worth of
//! cores (measured: a full-box prove is 1.08–1.18x one 64-thread lane), while
//! three proves each pinned to their own domain scale 3.00x. Concurrent slots
//! that share one process and one rayon pool interleave on the same cores and
//! first-touch their buffers on whatever node the faulting thread ran, which
//! measured ~0.55x per slot (~1.7x aggregate at three slots).
//!
//! This module gives the scheduler one rayon pool per domain whose workers are
//! pinned with `sched_setaffinity(2)` and `set_mempolicy(2)`. Running a slot's
//! whole body inside `pool.install` puts every `par_iter` the prover reaches on
//! that pool, and pinning the calling thread first makes the slot's serial
//! allocations local too. Memory policy and CPU affinity are per task on
//! Linux, so both are applied on every thread that works for the slot.
//!
//! Configuration (environment, read once):
//! - `IX_NUMA=off` disables pinning (default `auto`: pin when ≥2 domains are
//!   visible to this process' cpuset).
//! - `IX_NUMA_POLICY=bind|preferred` (default `bind`): `bind` fails/OOMs rather
//!   than spilling to another node when a domain is full; `preferred` spills
//!   (measured ~10 % slower when it does).
//! - `IX_NUMA_THREADS=N` workers per domain pool (default: the domain's cpuset).
//! - `IX_NUMA_PACK=0|1` (default 1): allow two slots on one domain when it has
//!   the RAM and no domain is idle.
//!
//! Non-Linux targets and single-domain hosts get an empty topology and the
//! scheduler behaves exactly as before.

use std::sync::{Arc, OnceLock};

/// One NUMA domain visible to this process.
#[derive(Clone, Debug)]
pub struct Domain {
  pub node: u32,
  pub cpus: Vec<usize>,
  pub mem_bytes: usize,
}

/// Memory placement policy applied to pinned threads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Policy {
  Bind,
  Preferred,
}

/// Detected topology and the env-derived knobs.
#[derive(Clone, Debug)]
pub struct Topology {
  pub domains: Vec<Domain>,
  pub policy: Policy,
  pub threads: Option<usize>,
  pub pack: bool,
}

impl Topology {
  pub fn enabled(&self) -> bool {
    self.domains.len() >= 2
  }
}

fn env_flag(name: &str, default: bool) -> bool {
  match std::env::var(name) {
    Ok(v) => !matches!(
      v.trim().to_ascii_lowercase().as_str(),
      "0" | "off" | "false" | "no"
    ),
    Err(_) => default,
  }
}

/// Parse a sysfs cpulist such as `0-31,96-127`.
fn parse_cpulist(text: &str) -> Vec<usize> {
  let mut cpus = Vec::new();
  for part in text.trim().split(',') {
    let part = part.trim();
    if part.is_empty() {
      continue;
    }
    if let Some((lo, hi)) = part.split_once('-') {
      if let (Ok(lo), Ok(hi)) = (lo.parse::<usize>(), hi.parse::<usize>()) {
        cpus.extend(lo..=hi);
      }
    } else if let Ok(cpu) = part.parse::<usize>() {
      cpus.push(cpu);
    }
  }
  cpus
}

/// Parse `Node N MemTotal: X kB` out of a node meminfo file.
fn parse_mem_total(text: &str) -> Option<usize> {
  text.lines().find(|l| l.contains("MemTotal")).and_then(|l| {
    l.split_whitespace()
      .filter_map(|w| w.parse::<usize>().ok())
      .nth(1)
      .map(|kb| kb * 1024)
  })
}

#[cfg(target_os = "linux")]
fn allowed_cpus() -> Option<Vec<usize>> {
  // SAFETY: cpu_set_t is plain data; sched_getaffinity fills it for the
  // calling thread. Its size is the documented argument.
  unsafe {
    let mut set: libc::cpu_set_t = std::mem::zeroed();
    let rc = libc::sched_getaffinity(0, size_of::<libc::cpu_set_t>(), &mut set);
    if rc != 0 {
      return None;
    }
    let mut cpus = Vec::new();
    for cpu in 0..libc::CPU_SETSIZE as usize {
      if libc::CPU_ISSET(cpu, &set) {
        cpus.push(cpu);
      }
    }
    Some(cpus)
  }
}

#[cfg(not(target_os = "linux"))]
fn allowed_cpus() -> Option<Vec<usize>> {
  None
}

fn detect_uncached() -> Topology {
  let policy = match std::env::var("IX_NUMA_POLICY")
    .map(|v| v.trim().to_ascii_lowercase())
    .as_deref()
  {
    Ok("preferred") => Policy::Preferred,
    _ => Policy::Bind,
  };
  let threads = std::env::var("IX_NUMA_THREADS")
    .ok()
    .and_then(|v| v.trim().parse::<usize>().ok())
    .filter(|&n| n > 0);
  let pack = env_flag("IX_NUMA_PACK", true);
  let mut topology = Topology { domains: Vec::new(), policy, threads, pack };
  if !env_flag("IX_NUMA", true) || !cfg!(target_os = "linux") {
    return topology;
  }
  let Some(allowed) = allowed_cpus() else {
    return topology;
  };
  let Ok(entries) = std::fs::read_dir("/sys/devices/system/node") else {
    return topology;
  };
  let mut domains = Vec::new();
  for entry in entries.flatten() {
    let name = entry.file_name();
    let name = name.to_string_lossy();
    let Some(node) =
      name.strip_prefix("node").and_then(|n| n.parse::<u32>().ok())
    else {
      continue;
    };
    let base = entry.path();
    let Ok(cpulist) = std::fs::read_to_string(base.join("cpulist")) else {
      continue;
    };
    let cpus: Vec<usize> = parse_cpulist(&cpulist)
      .into_iter()
      .filter(|cpu| allowed.contains(cpu))
      .collect();
    if cpus.is_empty() {
      continue;
    }
    let mem_bytes = std::fs::read_to_string(base.join("meminfo"))
      .ok()
      .and_then(|t| parse_mem_total(&t))
      .unwrap_or(0);
    if mem_bytes == 0 {
      continue;
    }
    domains.push(Domain { node, cpus, mem_bytes });
  }
  domains.sort_by_key(|d| d.node);
  if domains.len() >= 2 {
    topology.domains = domains;
  }
  topology
}

/// The tightest cgroup-v2 memory limit that applies to this process
/// (`memory.max` of its cgroup and every ancestor), in bytes; `None` when no
/// limit is set or the hierarchy is unreadable. Lets a stage adapt to the
/// scope it was launched in instead of trusting an inherited environment.
pub fn cgroup_memory_max() -> Option<usize> {
  let cgroup = std::fs::read_to_string("/proc/self/cgroup").ok()?;
  let path =
    cgroup.lines().find_map(|l| l.strip_prefix("0::"))?.trim().to_string();
  let mut tightest: Option<usize> = None;
  let mut dir = std::path::PathBuf::from(format!("/sys/fs/cgroup{path}"));
  loop {
    if let Ok(text) = std::fs::read_to_string(dir.join("memory.max"))
      && let Ok(limit) = text.trim().parse::<usize>()
    {
      tightest = Some(tightest.map_or(limit, |t| t.min(limit)));
    }
    if dir == std::path::Path::new("/sys/fs/cgroup") {
      break;
    }
    if !dir.pop() {
      break;
    }
  }
  tightest
}

/// This process's resident memory per NUMA node, in bytes, from
/// `/proc/self/numa_maps` (`N<node>=<pages>` at that mapping's
/// `kernelpagesize_kB`). Observability only — a few milliseconds for a few
/// hundred mappings. Empty when the file is unreadable (non-Linux, no NUMA).
pub fn resident_by_node() -> Vec<(u32, usize)> {
  let Ok(text) = std::fs::read_to_string("/proc/self/numa_maps") else {
    return Vec::new();
  };
  let mut totals: std::collections::BTreeMap<u32, usize> =
    std::collections::BTreeMap::new();
  for line in text.lines() {
    let mut page_kb = 4usize;
    let mut counts: Vec<(u32, usize)> = Vec::new();
    for field in line.split_whitespace().skip(2) {
      if let Some(kb) = field.strip_prefix("kernelpagesize_kB=") {
        page_kb = kb.parse().unwrap_or(4);
      } else if let Some(rest) = field.strip_prefix('N')
        && let Some((node, pages)) = rest.split_once('=')
        && let (Ok(node), Ok(pages)) =
          (node.parse::<u32>(), pages.parse::<usize>())
      {
        counts.push((node, pages));
      }
    }
    for (node, pages) in counts {
      *totals.entry(node).or_insert(0) += pages * page_kb * 1024;
    }
  }
  totals.into_iter().collect()
}

/// The process-wide topology (detected once; env read once).
pub fn detect() -> &'static Topology {
  static TOPOLOGY: OnceLock<Topology> = OnceLock::new();
  TOPOLOGY.get_or_init(detect_uncached)
}

/// Pin the calling thread to `domain`'s CPUs and memory node.
pub fn pin_current_thread(domain: &Domain, policy: Policy) {
  pin_current_thread_to(&domain.cpus, domain.node, policy);
}

/// Pin the calling thread to an explicit CPU list (a whole domain or one of
/// its halves) and to memory node `node`.
#[cfg(target_os = "linux")]
pub fn pin_current_thread_to(cpus: &[usize], node: u32, policy: Policy) {
  // SAFETY: cpu_set_t is plain data manipulated through libc's CPU_* helpers;
  // set_mempolicy takes a node bitmask with its bit length. Both syscalls
  // only affect the calling thread.
  unsafe {
    let mut set: libc::cpu_set_t = std::mem::zeroed();
    libc::CPU_ZERO(&mut set);
    for &cpu in cpus {
      if cpu < libc::CPU_SETSIZE as usize {
        libc::CPU_SET(cpu, &mut set);
      }
    }
    let _ = libc::sched_setaffinity(0, size_of::<libc::cpu_set_t>(), &set);
    let mode = match policy {
      Policy::Bind => libc::MPOL_BIND,
      Policy::Preferred => libc::MPOL_PREFERRED,
    };
    let words = (node as usize / 64) + 1;
    let mut mask = vec![0u64; words];
    mask[node as usize / 64] |= 1u64 << (node % 64);
    let _ = libc::syscall(
      libc::SYS_set_mempolicy,
      libc::c_long::from(mode),
      mask.as_ptr(),
      (words * 64) as libc::c_ulong,
    );
  }
}

#[cfg(not(target_os = "linux"))]
pub fn pin_current_thread_to(_cpus: &[usize], _node: u32, _policy: Policy) {}

/// Undo `pin_current_thread` on the calling thread: all allowed CPUs, default
/// memory policy.
#[cfg(target_os = "linux")]
pub fn unpin_current_thread(topology: &Topology) {
  // SAFETY: as in `pin_current_thread`; MPOL_DEFAULT takes no mask.
  unsafe {
    let mut set: libc::cpu_set_t = std::mem::zeroed();
    libc::CPU_ZERO(&mut set);
    for domain in &topology.domains {
      for &cpu in &domain.cpus {
        if cpu < libc::CPU_SETSIZE as usize {
          libc::CPU_SET(cpu, &mut set);
        }
      }
    }
    let _ = libc::sched_setaffinity(0, size_of::<libc::cpu_set_t>(), &set);
    let _ = libc::syscall(
      libc::SYS_set_mempolicy,
      libc::c_long::from(libc::MPOL_DEFAULT),
      std::ptr::null::<u64>(),
      0_u64,
    );
  }
}

#[cfg(not(target_os = "linux"))]
pub fn unpin_current_thread(_topology: &Topology) {}

/// A rayon pool whose workers are pinned to one domain.
pub fn pool(
  topology: &Topology,
  domain: &Domain,
) -> Result<Arc<rayon::ThreadPool>, String> {
  let threads = topology.threads.unwrap_or(domain.cpus.len()).max(1);
  let node = domain.node;
  let pin_cpus = domain.cpus.clone();
  let policy = topology.policy;
  rayon::ThreadPoolBuilder::new()
    .num_threads(threads)
    .thread_name(move |i| format!("numa{node}-{i}"))
    .start_handler(move |_| pin_current_thread_to(&pin_cpus, node, policy))
    .build()
    .map(Arc::new)
    .map_err(|e| format!("numa pool for node {node}: {e}"))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn cpulist_ranges_and_singletons() {
    assert_eq!(parse_cpulist("0-3,8,10-11\n"), vec![0, 1, 2, 3, 8, 10, 11]);
    assert_eq!(parse_cpulist(""), Vec::<usize>::new());
  }

  #[test]
  fn meminfo_total() {
    let text = "Node 2 MemTotal:       516001 kB\nNode 2 MemFree:  1 kB\n";
    assert_eq!(parse_mem_total(text), Some(516001 * 1024));
    assert_eq!(parse_mem_total("nothing"), None);
  }

  #[test]
  fn resident_by_node_reads_this_process() {
    // On Linux the current process has some resident memory on some node.
    let resident = resident_by_node();
    if cfg!(target_os = "linux") {
      assert!(resident.iter().map(|(_, b)| *b).sum::<usize>() > 0);
    }
  }

  #[test]
  fn detect_never_panics_and_is_consistent() {
    let t = detect();
    assert!(t.domains.len() != 1);
    for d in &t.domains {
      assert!(!d.cpus.is_empty());
      assert!(d.mem_bytes > 0);
    }
  }
}
