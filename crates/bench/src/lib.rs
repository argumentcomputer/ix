//! The benchmark row contract shared by every measured tool.
//!
//! Each tool (`bench-typecheck`, `zisk-host`, `sp1-host`, `ix check-rs`,
//! `ix compile`) reports its results as one JSON object per benchmark name in
//! a single file:
//!
//! ```json
//! { "<name>": { "status": "ok", "<metric>": <number>, ...,
//!               "phases": { "<span>": <seconds>, ... } } }
//! ```
//!
//! Rows are flushed to disk after every name, so a killed process still
//! leaves a complete file of the rows measured so far. The orchestrator
//! (`ix bench run`) identifies a killed run's in-flight name as the first
//! requested name without a row, and merges `"status": "oom"` into whatever
//! partial metrics that row holds — tools themselves only ever write `ok` or
//! `rejected`.
//!
//! Exit codes are the failure channel (no stdout markers, no log grepping):
//! `0` — every row `ok`; [`EXIT_USAGE`] — bad invocation; [`EXIT_REJECTED`] —
//! the kernel rejected a constant (its `rejected` row is on disk; the tool
//! fails fast, so later names have no rows). Any other exit is an
//! infrastructure failure.

use std::collections::HashSet;
use std::io;
use std::path::Path;

use serde_json::{Map, Value};

/// Bad invocation (unknown name, missing input, conflicting flags).
pub const EXIT_USAGE: u8 = 2;
/// The kernel rejected at least one constant; its row is on disk.
pub const EXIT_REJECTED: u8 = 3;

/// Row outcome as written by a tool (`Oom` is only ever set by the
/// orchestrator, after the fact — a tool never observes its own OOM kill).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
  Ok,
  Rejected,
  Oom,
}

impl Status {
  pub fn as_str(self) -> &'static str {
    match self {
      Status::Ok => "ok",
      Status::Rejected => "rejected",
      Status::Oom => "oom",
    }
  }
}

/// Typed kernel-rejection error. Binaries write the `rejected` row, propagate
/// this through their error chain, and map it to [`EXIT_REJECTED`] in `main` —
/// keeping the failure channel an exit code rather than an error-message
/// format some consumer has to grep.
#[derive(Debug)]
pub struct Rejection {
  pub failures: u64,
  pub ctx: String,
}

impl std::fmt::Display for Rejection {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "kernel typecheck rejected {} item(s) in {}",
      self.failures, self.ctx
    )
  }
}

impl std::error::Error for Rejection {}

/// Peak resident set size (bytes) across this process *and its children*,
/// from tracing-texray's tree sampler. `None` until the sampler has started
/// or off Linux. Unlike a bare `/proc/self/status` read this includes child
/// processes (e.g. Zisk's ASM microservices, which mmap large ROMs in
/// separate PIDs).
pub fn peak_rss_bytes() -> Option<u64> {
  match tracing_texray::rss_sampler::peak_tree_rss_bytes() {
    0 => None,
    n => Some(n),
  }
}

/// Write the row `{ "<name>": { "status": …, …metrics } }` into the results
/// file at `path`, merging into any existing object (overwriting on
/// collision) so a multi-name run accumulates one map with a row per name.
pub fn write_row(
  path: &Path,
  name: &str,
  status: Status,
  metrics: Value,
) -> io::Result<()> {
  let mut row = match metrics {
    Value::Object(m) => m,
    Value::Null => Map::new(),
    other => {
      let mut m = Map::new();
      m.insert("value".to_string(), other);
      m
    },
  };
  row.insert("status".to_string(), Value::String(status.as_str().into()));
  write_json_entry(path, name, Value::Object(row))
}

/// Append the entry `{ "<name>": <value> }` to the JSON object at `path`,
/// creating the file if absent. Written whole after every merge, so an
/// external kill still leaves a valid file of the entries so far. serde_json
/// handles key escaping, so arbitrary Lean names are safe.
pub fn write_json_entry(
  path: &Path,
  name: &str,
  value: Value,
) -> io::Result<()> {
  let mut map: Map<String, Value> = match std::fs::read(path) {
    Ok(bytes) => serde_json::from_slice(&bytes).unwrap_or_default(),
    Err(e) if e.kind() == io::ErrorKind::NotFound => Map::new(),
    Err(e) => return Err(e),
  };
  map.insert(name.to_string(), value);
  std::fs::write(path, serde_json::to_string(&Value::Object(map))?)
}

/// Union comma-separated `--consts` values with names read from a
/// `--consts-file` (one per line, `#` comments and blank lines dropped),
/// preserving first-seen order so the same name is never measured twice.
pub fn collect_consts(
  consts: &[String],
  consts_file: Option<&Path>,
) -> io::Result<Vec<String>> {
  let mut seen: HashSet<String> = HashSet::new();
  let mut out: Vec<String> = Vec::new();
  for name in consts {
    let trimmed = name.trim();
    if !trimmed.is_empty() && seen.insert(trimmed.to_string()) {
      out.push(trimmed.to_string());
    }
  }
  if let Some(path) = consts_file {
    let contents = std::fs::read_to_string(path)?;
    for line in contents.lines() {
      let name = line.split('#').next().unwrap_or("").trim();
      if !name.is_empty() && seen.insert(name.to_string()) {
        out.push(name.to_string());
      }
    }
  }
  Ok(out)
}

#[cfg(test)]
mod tests {
  use serde_json::json;

  use super::*;

  #[test]
  fn collect_unions_and_dedups() {
    let path = std::env::temp_dir().join("ix_bench_test_consts.txt");
    std::fs::write(&path, "a\nb\n# comment\n  c  \n\na\n").expect("write");
    let consts = vec!["a".to_string(), "d".to_string()];
    let got = collect_consts(&consts, Some(&path)).expect("collect");
    assert_eq!(got, vec!["a", "d", "b", "c"]);
    let _ = std::fs::remove_file(&path);
  }

  #[test]
  fn collect_trims_and_skips_empty() {
    let consts = vec![" a ".to_string(), "".to_string(), "a".to_string()];
    let got = collect_consts(&consts, None).expect("collect");
    assert_eq!(got, vec!["a"]);
  }

  #[test]
  fn rows_accumulate_and_overwrite() {
    let path = std::env::temp_dir().join("ix_bench_test_rows.json");
    let _ = std::fs::remove_file(&path);
    write_row(&path, "a", Status::Ok, json!({"cycles": 1})).expect("write a");
    write_row(&path, "b", Status::Rejected, json!({})).expect("write b");
    write_row(&path, "a", Status::Ok, json!({"cycles": 2})).expect("rewrite");
    let v: Value = serde_json::from_slice(&std::fs::read(&path).expect("read"))
      .expect("parse");
    assert_eq!(v["a"], json!({"status": "ok", "cycles": 2}));
    assert_eq!(v["b"], json!({"status": "rejected"}));
    let _ = std::fs::remove_file(&path);
  }

  #[test]
  fn row_survives_preexisting_garbage() {
    let path = std::env::temp_dir().join("ix_bench_test_garbage.json");
    std::fs::write(&path, "not json").expect("write");
    write_row(&path, "a", Status::Ok, json!({"t": 1.5})).expect("write");
    let v: Value = serde_json::from_slice(&std::fs::read(&path).expect("read"))
      .expect("parse");
    assert_eq!(v["a"]["status"], "ok");
    let _ = std::fs::remove_file(&path);
  }
}
