//! Recurse over actual execution segment proofs with a caller-selected class.
use super::*;
use ixby_flock::{hash::pack_bytes, ixby::paged_exec::ExecutionStatement};
use std::{
  io::{Read, Write},
  path::Path,
  process::{Command, Stdio},
  time::Instant,
};

const TEST: &str = "execution_tree::tests::large_execution::original_1024_execution_chain_proves_fresh";
const PACKED_TEST: &str = "execution_tree::tests::large_execution::original_packed_1024_execution_chain_proves_fresh";
const LINKED_TEST: &str = "execution_tree::tests::large_execution::original_linked_1024_execution_chain_proves_fresh";
const SHAPE_TEST: &str = "execution_tree::tests::large_execution::execution_batch_shape_chain_proves_fresh";
const CHILD: &str = "IXBY_LARGE_EXECUTION_CHAIN_RECEIVER";

fn compiler(class: BatchClass, leaves: usize) -> PagedTreeCompiler {
  // The profile is used only by complete-run endpoints. This benchmark
  // compiles execution chains, which bind their published machine parameters
  // and boundaries but make no source-admission or termination claim.
  let profile = FunctionalProfile::new(
    [65536, 4096, 65536, 8192, 1024, 65536, 65536, 4096, 65536, 16777216],
    16_000_000_000,
  )
  .unwrap();
  let mut counts = [1; 11];
  counts[Component::Execution as usize] = leaves;
  PagedTreeCompiler::new(profile, class, counts).unwrap()
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
  proof_chain(BatchClass::Shared1024, TEST);
}

#[test]
#[ignore = "requires three original packed 1,024-fetch proofs; two recursive levels, boundary attacks, fresh receiver"]
fn original_packed_1024_execution_chain_proves_fresh() {
  proof_chain(BatchClass::SharedPacked1024, PACKED_TEST);
}

#[test]
#[ignore = "requires three original linked 1,024-fetch proofs; two recursive levels, boundary attacks, fresh receiver"]
fn original_linked_1024_execution_chain_proves_fresh() {
  proof_chain(BatchClass::SharedLinked1024, LINKED_TEST);
}

#[test]
#[ignore = "four execution segment proofs; selected batch class, leaf and recursive joins, fresh receiver"]
fn execution_batch_shape_chain_proves_fresh() {
  let class = BatchClass::from_name(
    &std::env::var("IXBY_EXECUTION_CHAIN_CLASS").unwrap(),
  )
  .unwrap();
  proof_chain(class, SHAPE_TEST);
}

fn proof_chain(class: BatchClass, test: &str) {
  let count = if test == SHAPE_TEST { 4 } else { 3 };
  let mut compiler = compiler(class, count);
  let compiling = Instant::now();
  if std::env::var_os(CHILD).is_some() {
    let node = compiler.compile_component(Component::Execution, count).unwrap();
    eprintln!(
      "{}",
      serde_json::json!({"event":"chain_receiver_setup",
      "class":class.name(),"seconds":compiling.elapsed().as_secs_f64(),
      "identity":blake3::Hash::from(node.identity()).to_hex().as_str(),
      "geometry":node.geometry()})
    );
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
    let checking = Instant::now();
    node.verify(&statement, &bytes[57 * 16..]).unwrap();
    eprintln!(
      "{}",
      serde_json::json!({"event":"chain_receiver_accepted",
      "class":class.name(),"seconds":checking.elapsed().as_secs_f64(),
      "bytes":bytes.len()-57*16})
    );
    for at in 0..57 {
      for delta in [F128::ONE, F128::new(0, 1 << 63)] {
        let mut bad = statement.clone();
        bad[at] += delta;
        assert!(node.verify(&bad, &bytes[57 * 16..]).is_err());
      }
    }
    let proof = &bytes[57 * 16..];
    assert!(node.verify(&statement, &proof[..proof.len() - 1]).is_err());
    let mut extended = proof.to_vec();
    extended.push(0);
    assert!(node.verify(&statement, &extended).is_err());
    eprintln!(
      "chain receiver rejected all 114 public-word mutations, truncation and trailing data"
    );
    return;
  }
  let node = compiler.compile_component(Component::Execution, 2).unwrap();
  eprintln!(
    "{}",
    serde_json::json!({"event":"chain_setup","class":class.name(),
    "leaves":2,"seconds":compiling.elapsed().as_secs_f64(),"geometry":node.geometry(),
    "identity":blake3::Hash::from(node.identity()).to_hex().as_str()})
  );
  let dir = std::env::var_os("IXBY_LARGE_EXECUTION_PROOFS")
    .expect("IXBY_LARGE_EXECUTION_PROOFS");
  let leaves =
    (0..count).map(|i| record(Path::new(&dir), i)).collect::<Vec<_>>();
  let Owner::Leaf(leaf) = &node.children[0].setup().owner else {
    unreachable!()
  };
  let Leaf::Execution(setup) = leaf.as_ref() else { unreachable!() };
  eprintln!(
    "{}",
    serde_json::json!({"event":"chain_leaf_setup","class":class.name(),
    "registry_digest":blake3::Hash::from(setup.verifier_shape().registry.digest()).to_hex().as_str(),
    "circuit_digest":blake3::Hash::from(setup.verifier_shape().circuit.digest()).to_hex().as_str(),
    "row_variables":class.nu(),"dense_variables":setup.pcs_params().m,
    "transcript_domain":std::str::from_utf8(class.transcript_domain()).unwrap()})
  );
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
  eprintln!(
    "{}",
    serde_json::json!({"event":"chain_proof","class":class.name(),
    "leaves":2,"seconds":started.elapsed().as_secs_f64(),
    "bytes":first.proof.len(),"geometry":node.geometry()})
  );
  save("node-2", &first);
  // The four-leaf experiment measures a join of two recursive proofs,
  // as well as the first-level joins of raw execution proofs.
  let right = if count == 4 {
    let started = Instant::now();
    let right = node
      .prove(
        [&leaves[2].statement, &leaves[3].statement],
        [&leaves[2].proof, &leaves[3].proof],
      )
      .unwrap();
    assert_eq!(
      right.statement,
      expected(&leaves[2].statement, &leaves[3].statement)
    );
    node.verify(&right.statement, &right.proof).unwrap();
    eprintln!(
      "{}",
      serde_json::json!({"event":"chain_proof","class":class.name(),
      "leaves":2,"first_leaf":2,"seconds":started.elapsed().as_secs_f64(),
      "bytes":right.proof.len(),"geometry":node.geometry()})
    );
    save("node-2-right", &right);
    right
  } else {
    PagedNodeProof {
      statement: leaves[2].statement.clone(),
      proof: leaves[2].proof.clone(),
    }
  };
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
  let compiling = Instant::now();
  let node = compiler.compile_component(Component::Execution, count).unwrap();
  eprintln!(
    "{}",
    serde_json::json!({"event":"chain_setup","class":class.name(),
    "leaves":count,"seconds":compiling.elapsed().as_secs_f64(),"geometry":node.geometry(),
    "identity":blake3::Hash::from(node.identity()).to_hex().as_str()})
  );
  let started = Instant::now();
  let root = node
    .prove([&first.statement, &right.statement], [&first.proof, &right.proof])
    .unwrap();
  assert_eq!(root.statement, expected(&first.statement, &right.statement));
  node.verify(&root.statement, &root.proof).unwrap();
  eprintln!(
    "large execution node {count}: {} bytes, {:?}, {:?}",
    root.proof.len(),
    started.elapsed(),
    node.geometry()
  );
  eprintln!(
    "{}",
    serde_json::json!({"event":"chain_proof","class":class.name(),
    "leaves":count,"seconds":started.elapsed().as_secs_f64(),
    "bytes":root.proof.len(),"geometry":node.geometry()})
  );
  save(&format!("node-{count}"), &root);
  drop(node);
  drop(compiler);
  drop(leaves);
  drop(first);
  drop(right);
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args([test, "--ignored", "--exact", "--nocapture", "--test-threads=1"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("IXBY_EXECUTION_CHAIN_CLASS", class.name())
    .env("RAYON_NUM_THREADS", "2")
    .env("MALLOC_ARENA_MAX", "2")
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
