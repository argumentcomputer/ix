//! The `.ixes` cases of the shared reject-parity fixture
//! (`Tests/Fixtures/ixon-v4/reject-parity.txt`): every manifest the Lean
//! parser (`parseIxesManifest`, the `ixon-reject-parity` suite) refuses, the
//! Rust reader refuses too.

use ix_kernel::shard::ShardManifest;

const FIXTURE: &str =
  include_str!("../../../Tests/Fixtures/ixon-v4/reject-parity.txt");

/// The fixture's cases of `kind`: name and bytes.
fn of_kind(kind: &str) -> Vec<(&'static str, Vec<u8>)> {
  let found: Vec<_> = FIXTURE
    .lines()
    .map(str::trim)
    .filter(|line| !line.is_empty() && !line.starts_with('#'))
    .filter_map(|line| {
      let mut tokens = line.split_whitespace();
      if tokens.next() != Some(kind) {
        return None;
      }
      let name = tokens.next().unwrap();
      let mut bytes = Vec::new();
      for token in tokens {
        let (hex, count) = match token.split_once('*') {
          Some((hex, count)) => (hex, count.parse::<usize>().unwrap()),
          None => (token, 1),
        };
        let chunk: Vec<u8> = (0..hex.len())
          .step_by(2)
          .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
          .collect();
        for _ in 0..count {
          bytes.extend_from_slice(&chunk);
        }
      }
      Some((name, bytes))
    })
    .collect();
  assert!(!found.is_empty(), "no {kind} cases");
  found
}

/// Runs `f` on a thread with a 256 MiB stack. The aggregation-tree reader
/// recurses once per level up to its 4096-level bound before it refuses a
/// deeper tree (`deep-tree`). That fits the default test stack in release
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
fn manifests_are_refused_as_the_lean_parser_refuses_them() {
  on_large_stack(|| {
    for (name, bytes) in of_kind("ixes-accept") {
      ShardManifest::from_bytes(&bytes)
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    }
    for (name, bytes) in of_kind("ixes") {
      assert!(ShardManifest::from_bytes(&bytes).is_err(), "{name} accepted");
    }
  });
}
