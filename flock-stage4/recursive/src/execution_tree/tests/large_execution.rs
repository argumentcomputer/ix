//! Recurse over actual CSLib execution proofs made with Boolean routing.
use super::*;
use ixby_flock::{hash::pack_bytes, ixby::paged_exec::ExecutionStatement};
use std::{
  io::{Read, Write},
  path::Path,
  process::{Command, Stdio},
  time::Instant,
};

const TEST: &str = "execution_tree::tests::large_execution::original_1024_execution_chain_proves_fresh";
const CHILD: &str = "IXBY_LARGE_EXECUTION_CHAIN_RECEIVER";

fn compiler() -> PagedTreeCompiler {
  // Approved original CSLib functional limits, fixed before any proof read.
  let profile = FunctionalProfile::new(
    [65536, 4096, 65536, 8192, 1024, 65536, 65536, 4096, 65536, 16777216],
    16_000_000_000,
  )
  .unwrap();
  let mut counts = [1; 11];
  counts[Component::Execution as usize] = 3;
  PagedTreeCompiler::new(profile, BatchClass::Shared1024, counts).unwrap()
}

fn read(path: &Path, limit: u64) -> Vec<u8> {
  let mut bytes = Vec::new();
  std::fs::File::open(path)
    .unwrap()
    .take(limit + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(bytes.len() as u64 <= limit);
  bytes
}
fn words(bytes: &[u8]) -> Vec<F128> {
  assert_eq!(bytes.len(), 57 * 16);
  bytes.as_chunks::<16>().0.iter().map(|w| pack_bytes(w)).collect()
}
fn record(dir: &Path, index: usize) -> PagedNodeProof {
  PagedNodeProof {
    statement: words(&read(
      &dir.join(format!("{index:010}.statement")),
      57 * 16,
    )),
    proof: read(&dir.join(format!("{index:010}.flock")), MAX_PAGED_TREE_BYTES),
  }
}
fn expected(a: &[F128], b: &[F128]) -> Vec<F128> {
  assert_eq!(a[..3], b[..3]);
  assert_eq!(a[30..], b[3..30]);
  [&a[..30], &b[30..]].concat()
}
fn save(name: &str, proof: &PagedNodeProof) {
  let Some(dir) = std::env::var_os("IXBY_LARGE_EXECUTION_CHAIN_OUT") else {
    return;
  };
  let dir = Path::new(&dir);
  for (extension, bytes) in [
    ("flock", proof.proof.clone()),
    (
      "statement",
      proof.statement.iter().flat_map(|w| crate::f128::bytes(*w)).collect(),
    ),
  ] {
    let mut file = std::fs::OpenOptions::new()
      .write(true)
      .create_new(true)
      .open(dir.join(format!("{name}.{extension}")))
      .unwrap();
    file.write_all(&bytes).unwrap();
    file.sync_all().unwrap();
  }
}

#[test]
#[ignore = "requires three original 1,024-fetch execution proofs; two recursive levels, boundary attacks, fresh receiver"]
fn original_1024_execution_chain_proves_fresh() {
  let mut compiler = compiler();
  if std::env::var_os(CHILD).is_some() {
    let node = compiler.compile_component(Component::Execution, 3).unwrap();
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(MAX_PAGED_TREE_BYTES + 57 * 16 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(
      bytes.len() > 57 * 16
        && bytes.len() as u64 <= MAX_PAGED_TREE_BYTES + 57 * 16
    );
    let statement = words(&bytes[..57 * 16]);
    node.verify(&statement, &bytes[57 * 16..]).unwrap();
    for at in 0..57 {
      for delta in [F128::ONE, F128::new(0, 1 << 63)] {
        let mut bad = statement.clone();
        bad[at] += delta;
        assert!(node.verify(&bad, &bytes[57 * 16..]).is_err());
      }
    }
    return;
  }
  let node = compiler.compile_component(Component::Execution, 2).unwrap();
  let dir = std::env::var_os("IXBY_LARGE_EXECUTION_PROOFS")
    .expect("IXBY_LARGE_EXECUTION_PROOFS");
  let leaves = (0..3).map(|i| record(Path::new(&dir), i)).collect::<Vec<_>>();
  let Owner::Leaf(leaf) = &node.children[0].setup().owner else {
    unreachable!()
  };
  let Leaf::Execution(setup) = leaf.as_ref() else { unreachable!() };
  for leaf in &leaves {
    setup
      .verify(
        &ExecutionStatement::from_words(&leaf.statement).unwrap(),
        &leaf.proof,
      )
      .unwrap();
  }
  let started = Instant::now();
  let first = node
    .prove(
      [&leaves[0].statement, &leaves[1].statement],
      [&leaves[0].proof, &leaves[1].proof],
    )
    .unwrap();
  assert_eq!(
    first.statement,
    expected(&leaves[0].statement, &leaves[1].statement)
  );
  node.verify(&first.statement, &first.proof).unwrap();
  eprintln!(
    "large execution node 2: {} bytes, {:?}, {:?}",
    first.proof.len(),
    started.elapsed(),
    node.geometry()
  );
  save("node-2", &first);
  for (name, a, b) in
    [("repeated", 0, 0), ("reversed", 1, 0), ("skipped", 0, 2)]
  {
    let error = node
      .prove(
        [&leaves[a].statement, &leaves[b].statement],
        [&leaves[a].proof, &leaves[b].proof],
      )
      .err()
      .expect("accepted nonadjacent valid execution segments");
    assert!(error.to_string().contains("advice constraints"), "{error:#}");
    eprintln!("{name} valid execution segments rejected: {error:#}");
  }
  drop(node);
  let node = compiler.compile_component(Component::Execution, 3).unwrap();
  let started = Instant::now();
  let root = node
    .prove(
      [&first.statement, &leaves[2].statement],
      [&first.proof, &leaves[2].proof],
    )
    .unwrap();
  assert_eq!(root.statement, expected(&first.statement, &leaves[2].statement));
  node.verify(&root.statement, &root.proof).unwrap();
  eprintln!(
    "large execution node 3: {} bytes, {:?}, {:?}",
    root.proof.len(),
    started.elapsed(),
    node.geometry()
  );
  save("node-3", &root);
  drop(node);
  drop(compiler);
  drop(leaves);
  drop(first);
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args([TEST, "--ignored", "--exact", "--nocapture", "--test-threads=1"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  for word in &root.statement {
    stdin.write_all(&crate::f128::bytes(*word)).unwrap();
  }
  stdin.write_all(&root.proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  eprintln!(
    "{}{}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
  assert!(
    output.status.success(),
    "fresh recursive execution receiver rejected"
  );
}
