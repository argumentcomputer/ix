//! Shared diagnostics helpers for phase logging.

use std::io::Read;
use std::sync::{LazyLock, mpsc};
use std::thread::{self, JoinHandle};
use std::time::Duration;

static MEMORY_DIAG: LazyLock<bool> =
  LazyLock::new(|| std::env::var_os("IX_MEMORY_DIAG").is_some());

fn field_kb(text: &str, name: &str) -> Option<u64> {
  text.lines().find_map(|line| {
    line.strip_prefix(name)?.split_whitespace().next()?.parse().ok()
  })
}

/// ` · rss X.X GiB (anon Y.Y, file Z.Z)` sampled from
/// `/proc/self/status`, appended to phase logs. Anon can only leave RAM
/// via swap; file RSS is reclaimable page cache — the split shows which
/// memory-reduction lever applies. Empty when procfs is unavailable.
pub fn rss_log_suffix() -> String {
  let Ok(status) = std::fs::read_to_string("/proc/self/status") else {
    return String::new();
  };
  let gib_tenths = |kb: u64| -> (u64, u64) {
    let tenths = kb * 10 / (1024 * 1024);
    (tenths / 10, tenths % 10)
  };
  match (
    field_kb(&status, "VmRSS:"),
    field_kb(&status, "RssAnon:"),
    field_kb(&status, "RssFile:"),
  ) {
    (Some(rss), Some(anon), Some(file)) => {
      let (r, rt) = gib_tenths(rss);
      let (a, at) = gib_tenths(anon);
      let (f, ft) = gib_tenths(file);
      format!(" · rss {r}.{rt} GiB (anon {a}.{at}, file {f}.{ft})")
    },
    _ => String::new(),
  }
}

// Stream maps instead of allocating a String proportional to the mapping
// count: this diagnostic must remain small even near vm.max_map_count.
fn count_lines(mut input: impl Read) -> std::io::Result<u64> {
  let mut buffer = [0u8; 8192];
  let mut count = 0;
  loop {
    let n = input.read(&mut buffer)?;
    if n == 0 {
      return Ok(count);
    }
    count += buffer[..n].iter().filter(|&&b| b == b'\n').count() as u64;
  }
}

// Diagnostic output rounds to tenths of a GiB, not an exact byte count.
#[allow(clippy::cast_precision_loss)]
fn gib_field(text: &str, name: &str) -> String {
  field_kb(text, name).map_or_else(
    || "?".into(),
    |kb| format!("{:.1}", kb as f64 / (1024.0 * 1024.0)),
  )
}

/// Detailed Linux memory snapshot for diagnosing allocation failures that
/// need not be physical OOMs (e.g. address-space or mapping-count limits).
fn memory_snapshot() -> String {
  let Ok(status) = std::fs::read_to_string("/proc/self/status") else {
    return "memory diagnostics unavailable (no /proc/self/status)".into();
  };
  let meminfo = std::fs::read_to_string("/proc/meminfo").unwrap_or_default();
  let maps = std::fs::File::open("/proc/self/maps")
    .ok()
    .and_then(|file| count_lines(file).ok())
    .map_or_else(|| "?".into(), |n| n.to_string());
  let map_limit = std::fs::read_to_string("/proc/sys/vm/max_map_count")
    .unwrap_or_else(|_| "?".into());
  let overcommit = std::fs::read_to_string("/proc/sys/vm/overcommit_memory")
    .unwrap_or_else(|_| "?".into());
  format!(
    "rss={} GiB (anon {}, file {}), vmsize={} GiB, peak_rss={} GiB, \
     process_swap={} GiB, available={} GiB, swap_free={}/{} GiB, \
     committed={}/{} GiB (overcommit={}), maps={}/{}",
    gib_field(&status, "VmRSS:"),
    gib_field(&status, "RssAnon:"),
    gib_field(&status, "RssFile:"),
    gib_field(&status, "VmSize:"),
    gib_field(&status, "VmHWM:"),
    gib_field(&status, "VmSwap:"),
    gib_field(&meminfo, "MemAvailable:"),
    gib_field(&meminfo, "SwapFree:"),
    gib_field(&meminfo, "SwapTotal:"),
    gib_field(&meminfo, "Committed_AS:"),
    gib_field(&meminfo, "CommitLimit:"),
    overcommit.trim(),
    maps,
    map_limit.trim(),
  )
}

/// Scope guard for an opt-in periodic memory sampler. Dropping it wakes and
/// joins the thread immediately, including on early compilation errors.
pub struct MemorySampler {
  stop: mpsc::Sender<()>,
  thread: Option<JoinHandle<()>>,
}

impl Drop for MemorySampler {
  fn drop(&mut self) {
    let _ = self.stop.send(());
    if let Some(thread) = self.thread.take() {
      let _ = thread.join();
    }
  }
}

/// With `IX_MEMORY_DIAG=1`, log process/system memory every five seconds,
/// including inside phases that never reach their completion log on OOM.
pub fn memory_sampler(label: &'static str) -> Option<MemorySampler> {
  if !*MEMORY_DIAG {
    return None;
  }
  let (stop, receiver) = mpsc::channel();
  match thread::Builder::new().name("ix-memory-diag".into()).spawn(move || {
    loop {
      eprintln!("[{label}] memory: {}", memory_snapshot());
      match receiver.recv_timeout(Duration::from_secs(5)) {
        Err(mpsc::RecvTimeoutError::Timeout) => {},
        _ => break,
      }
    }
  }) {
    Ok(thread) => Some(MemorySampler { stop, thread: Some(thread) }),
    Err(error) => {
      eprintln!("[{label}] could not start memory diagnostics: {error}");
      None
    },
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parses_proc_fields_without_confusing_similar_names() {
    let status = "VmRSS:\t1048576 kB\nRssAnon:\t524288 kB\n";
    assert_eq!(field_kb(status, "VmRSS:"), Some(1048576));
    assert_eq!(gib_field(status, "RssAnon:"), "0.5");
    assert_eq!(field_kb(status, "VmSwap:"), None);
    assert_eq!(gib_field(status, "VmSwap:"), "?");
    assert_eq!(field_kb("VmRSS: invalid kB\n", "VmRSS:"), None);
  }

  #[test]
  fn counts_maps_across_buffer_boundaries() {
    let maps = "some mapping\n".repeat(2000);
    assert_eq!(count_lines(maps.as_bytes()).unwrap(), 2000);
    assert_eq!(count_lines(&b""[..]).unwrap(), 0);
  }

  #[test]
  fn sampler_guard_wakes_and_joins_its_thread() {
    let (stop, receiver) = mpsc::channel();
    let thread = thread::spawn(move || receiver.recv().unwrap());
    drop(MemorySampler { stop, thread: Some(thread) });
  }
}
