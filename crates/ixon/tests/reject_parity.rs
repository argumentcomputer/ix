//! Malformed inputs every Rust reader of their kind refuses: the Rust side of
//! the shared fixture `Tests/Fixtures/ixon-v4/reject-parity.txt`, which the Lean suite
//! `ixon-reject-parity` (`Tests/Ix/IxonRejectParity.lean`) reads too, so
//! that both sides refuse the same byte strings. The `.ixes` cases are the
//! kernel crate's (`crates/kernel/tests/reject_parity.rs`).

use ixon::assumption_tree::AssumptionTree;
use ixon::constant::Constant;
use ixon::env::Env;
use ixon::proof::Claim;

const FIXTURE: &str =
  include_str!("../../../Tests/Fixtures/ixon-v4/reject-parity.txt");

/// The fixture's cases: kind, name and bytes.
fn cases() -> Vec<(&'static str, &'static str, Vec<u8>)> {
  FIXTURE
    .lines()
    .map(str::trim)
    .filter(|line| !line.is_empty() && !line.starts_with('#'))
    .map(|line| {
      let mut tokens = line.split_whitespace();
      let kind = tokens.next().unwrap();
      let name = tokens.next().unwrap();
      let mut bytes = Vec::new();
      for token in tokens {
        let (hex, count) = match token.split_once('*') {
          Some((hex, count)) => (hex, count.parse::<usize>().unwrap()),
          None => (token, 1),
        };
        assert!(hex.len() % 2 == 0, "{name}: odd hex token {token}");
        let chunk: Vec<u8> = (0..hex.len())
          .step_by(2)
          .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
          .collect();
        for _ in 0..count {
          bytes.extend_from_slice(&chunk);
        }
      }
      (kind, name, bytes)
    })
    .collect()
}

fn of_kind(kind: &str) -> Vec<(&'static str, Vec<u8>)> {
  let found: Vec<_> = cases()
    .into_iter()
    .filter(|(k, _, _)| *k == kind)
    .map(|(_, name, bytes)| (name, bytes))
    .collect();
  assert!(!found.is_empty(), "no {kind} cases");
  found
}

/// A constant decoded from exactly `bytes`.
fn constant(bytes: &[u8]) -> Result<Constant, String> {
  let mut rest = bytes;
  let constant = Constant::get(&mut rest)?;
  if !rest.is_empty() {
    return Err(format!("{} trailing bytes", rest.len()));
  }
  Ok(constant)
}

/// A constant whose bytes are its canonical encoding.
fn canonical(bytes: &[u8]) -> Result<Constant, String> {
  let constant = constant(bytes)?;
  let mut encoded = Vec::new();
  constant.put(&mut encoded);
  if encoded != bytes {
    return Err("noncanonical encoding".into());
  }
  Ok(constant)
}

fn environment(bytes: &[u8]) -> [(&'static str, Result<(), String>); 2] {
  [
    ("Env::get", Env::get(&mut &bytes[..]).map(drop)),
    ("Env::parse_lazy_index", Env::parse_lazy_index(bytes).map(drop)),
  ]
}

fn tree(bytes: &[u8]) -> Result<AssumptionTree, String> {
  let mut rest = bytes;
  let tree = AssumptionTree::get(&mut rest)?;
  if !rest.is_empty() {
    return Err(format!("{} trailing bytes", rest.len()));
  }
  Ok(tree)
}

#[test]
fn records_are_refused_by_every_constant_decoder() {
  for (name, bytes) in of_kind("record-accept") {
    canonical(&bytes).unwrap_or_else(|e| panic!("{name}: {e}"));
  }
  for (name, bytes) in of_kind("record") {
    assert!(constant(&bytes).is_err(), "{name} accepted");
  }
}

#[test]
fn noncanonical_records_are_refused() {
  for (name, bytes) in of_kind("noncanonical") {
    assert!(canonical(&bytes).is_err(), "{name} accepted");
    // Refused by the decoder itself, not only by the re-encoding.
    assert!(constant(&bytes).is_err(), "{name} decoded");
  }
}

#[test]
fn environments_are_refused_by_every_full_reader() {
  for (name, bytes) in of_kind("env-accept") {
    for (reader, result) in environment(&bytes) {
      result.unwrap_or_else(|e| panic!("{name}: {reader}: {e}"));
    }
  }
  for (name, bytes) in of_kind("env") {
    for (reader, result) in environment(&bytes) {
      assert!(result.is_err(), "{name}: {reader} accepted");
    }
  }
}

/// Runs `f` on a thread with a 256 MiB stack. The assumption-tree reader
/// recurses once per level up to its 4096-level bound before it refuses a
/// deeper tree (`tree deep`). That fits the default test stack in release
/// builds, but not with the larger frames of debug builds.
fn on_large_stack(f: impl FnOnce() + Send + 'static) {
  if let Err(panic) = std::thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(f)
    .expect("spawn the test thread")
    .join()
  {
    std::panic::resume_unwind(panic);
  }
}

#[test]
fn assumption_trees_are_refused() {
  on_large_stack(|| {
    for (name, bytes) in of_kind("tree-accept") {
      tree(&bytes).unwrap_or_else(|e| panic!("{name}: {e}"));
    }
    for (name, bytes) in of_kind("tree") {
      assert!(tree(&bytes).is_err(), "{name} accepted");
    }
  });
}

#[test]
fn claims_are_refused() {
  for (name, bytes) in of_kind("claim") {
    assert!(Claim::from_bytes(&bytes).is_err(), "{name} accepted");
  }
}
