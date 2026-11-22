//! A diagnostic sampler of process memory against the host budget's
//! accounting, enabled by `AIUR_MEMORY_TRACE=<seconds>`.
//!
//! Each sample logs one `[memory]` line: the kernel's view of the process
//! (`VmRSS`, `RssAnon`, `RssFile`, `RssShmem` from `/proc/self/status`,
//! `AnonHugePages` from `/proc/self/smaps_rollup`) and the record pool
//! ([`record_pool::PoolUsage`]). `untracked` is RSS less what the budget
//! accounts for: the pool's grants, every lane's workspace and the resident
//! bytes. A positive value is memory the budget does not see; a negative
//! one is accounted capacity not in use, usually idle workspace. The pass
//! ends with a `[memory] peak` line.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use record_pool::RecordPool;

use crate::format_gib;

/// What the budget accounts for besides the pool's grants.
#[derive(Clone, Copy, Debug)]
pub(super) struct Accounted {
  pub workspace: usize,
  pub resident: usize,
}

/// The running sampler; dropping it stops sampling and logs the peaks.
pub(super) struct MemoryTrace {
  stop: Arc<AtomicBool>,
  handle: Option<thread::JoinHandle<()>>,
}

impl MemoryTrace {
  /// Starts sampling if `AIUR_MEMORY_TRACE` names a positive interval.
  pub(super) fn start(
    pool: &RecordPool,
    accounted: Accounted,
    started: Instant,
  ) -> Option<Self> {
    let seconds = std::env::var("AIUR_MEMORY_TRACE")
      .ok()?
      .parse::<f64>()
      .ok()
      .filter(|s| s.is_finite() && *s > 0.0)?;
    let interval = Duration::from_secs_f64(seconds);
    let stop = Arc::new(AtomicBool::new(false));
    let (pool, flag) = (pool.clone(), Arc::clone(&stop));
    let handle = thread::Builder::new()
      .name("aiur-memory-trace".into())
      .spawn(move || sample_loop(&pool, accounted, started, interval, &flag))
      .ok()?;
    Some(Self { stop, handle: Some(handle) })
  }
}

impl Drop for MemoryTrace {
  fn drop(&mut self) {
    self.stop.store(true, Ordering::Relaxed);
    if let Some(handle) = self.handle.take() {
      handle.thread().unpark();
      let _ = handle.join();
    }
  }
}

#[derive(Default)]
struct Kernel {
  rss: usize,
  anon: usize,
  file: usize,
  shmem: usize,
  huge: usize,
}

/// A `/proc` field's value in bytes; the files report kB.
fn field(text: &str, name: &str) -> usize {
  text
    .lines()
    .find_map(|line| line.strip_prefix(name)?.strip_prefix(':'))
    .and_then(|rest| rest.split_whitespace().next()?.parse::<usize>().ok())
    .map_or(0, |kb| kb << 10)
}

fn kernel() -> Kernel {
  let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
  let rollup =
    std::fs::read_to_string("/proc/self/smaps_rollup").unwrap_or_default();
  Kernel {
    rss: field(&status, "VmRSS"),
    anon: field(&status, "RssAnon"),
    file: field(&status, "RssFile"),
    shmem: field(&status, "RssShmem"),
    huge: field(&rollup, "AnonHugePages"),
  }
}

fn signed_gib(bytes: isize) -> String {
  let sign = if bytes < 0 { "-" } else { "" };
  format!("{sign}{}", format_gib(bytes.unsigned_abs()))
}

fn sample_loop(
  pool: &RecordPool,
  accounted: Accounted,
  started: Instant,
  interval: Duration,
  stop: &AtomicBool,
) {
  let fixed = accounted.workspace + accounted.resident;
  let (mut peak_rss, mut peak_untracked) = (0, isize::MIN);
  loop {
    let usage = pool.usage();
    let k = kernel();
    let untracked = k.rss.cast_signed() - (usage.granted + fixed).cast_signed();
    peak_rss = peak_rss.max(k.rss);
    peak_untracked = peak_untracked.max(untracked);
    eprintln!(
      "[memory] +{:.0}s rss {} anon {} file {} shmem {} thp {} | pool granted {} used {} records {} executing {} | untracked {}",
      started.elapsed().as_secs_f64(),
      format_gib(k.rss),
      format_gib(k.anon),
      format_gib(k.file),
      format_gib(k.shmem),
      format_gib(k.huge),
      format_gib(usage.granted),
      format_gib(usage.used),
      usage.records,
      usage.executing,
      signed_gib(untracked),
    );
    if stop.load(Ordering::Relaxed) {
      break;
    }
    thread::park_timeout(interval);
  }
  eprintln!(
    "[memory] peak rss {} untracked {} (workspace {} resident {} accounted)",
    format_gib(peak_rss),
    signed_gib(peak_untracked),
    format_gib(accounted.workspace),
    format_gib(accounted.resident),
  );
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn proc_fields_parse_as_bytes() {
    let text = "Name:\tix\nVmRSS:\t  2048 kB\nRssAnon:\t1024 kB\n";
    assert_eq!(field(text, "VmRSS"), 2 << 20);
    assert_eq!(field(text, "RssAnon"), 1 << 20);
    assert_eq!(field(text, "RssFile"), 0);
  }
}
