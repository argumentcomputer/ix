//! Shared diagnostics helpers for phase logging.

/// ` · rss X.X GiB (anon Y.Y, file Z.Z)` sampled from
/// `/proc/self/status`, appended to phase logs. Anon can only leave RAM
/// via swap; file RSS is reclaimable page cache — the split shows which
/// memory-reduction lever applies. Empty when procfs is unavailable.
pub fn rss_log_suffix() -> String {
  let Ok(status) = std::fs::read_to_string("/proc/self/status") else {
    return String::new();
  };
  let field_kb = |name: &str| -> Option<u64> {
    status
      .lines()
      .find(|l| l.starts_with(name))
      .and_then(|l| l.split_whitespace().nth(1))
      .and_then(|v| v.parse().ok())
  };
  let gib_tenths = |kb: u64| -> (u64, u64) {
    let tenths = kb * 10 / (1024 * 1024);
    (tenths / 10, tenths % 10)
  };
  match (field_kb("VmRSS:"), field_kb("RssAnon:"), field_kb("RssFile:")) {
    (Some(rss), Some(anon), Some(file)) => {
      let (r, rt) = gib_tenths(rss);
      let (a, at) = gib_tenths(anon);
      let (f, ft) = gib_tenths(file);
      format!(" · rss {r}.{rt} GiB (anon {a}.{at}, file {f}.{ft})")
    },
    _ => String::new(),
  }
}
