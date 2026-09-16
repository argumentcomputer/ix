//! Check actual retained CLI execution chains, including valid but nonadjacent
//! child proofs. The fixture has 40 tail calls and an exact 83-step budget.
use super::*;
use ixby_flock::{hash::pack_bytes, ixby::paged_exec::ExecutionStatement};
use std::{
  io::Read,
  path::{Path, PathBuf},
};

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
fn record(directory: &Path, name: &str) -> PagedNodeProof {
  let bytes = read(&directory.join(format!("{name}.statement")), 57 * 16);
  assert_eq!(bytes.len(), 57 * 16);
  PagedNodeProof {
    statement: bytes
      .as_chunks::<16>()
      .0
      .iter()
      .map(|w| pack_bytes(w))
      .collect(),
    proof: read(&directory.join(format!("{name}.flock")), MAX_PAGED_TREE_BYTES),
  }
}

#[test]
#[ignore = "requires IXBY_COUNTDOWN_PROOFS from the original-format countdown CLI fixture"]
fn execution_chain_rejects_repeated_reversed_and_skipped_valid_segments() {
  let profile =
    FunctionalProfile::new([1, 0, 3, 3, 2, 0, 8, 4096, 64, 64], 83).unwrap();
  let mut counts = [1; 11];
  counts[Component::Execution as usize] = 3;
  let mut compiler =
    PagedTreeCompiler::new(profile, BatchClass::Shared, counts).unwrap();
  let node = compiler.compile_component(Component::Execution, 2).unwrap();
  let directory = PathBuf::from(
    std::env::var_os("IXBY_COUNTDOWN_PROOFS").expect("IXBY_COUNTDOWN_PROOFS"),
  );
  let leaves = (0..3)
    .map(|i| record(&directory, &format!("leaves/06/0000000/{i:010}")))
    .collect::<Vec<_>>();
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
  for pair in leaves.windows(2) {
    assert_eq!(pair[0].statement[..3], pair[1].statement[..3]);
    assert_eq!(pair[0].statement[30..], pair[1].statement[3..30]);
  }
  let pair = record(&directory, "nodes/06/0000000002/0000000/0000000000");
  let expected =
    [leaves[0].statement[..30].to_vec(), leaves[1].statement[30..].to_vec()]
      .concat();
  assert_eq!(pair.statement, expected);
  node.verify(&expected, &pair.proof).unwrap();
  for (name, a, b) in
    [("repeated", 0, 0), ("reversed", 1, 0), ("skipped", 0, 2)]
  {
    let error = node
      .prove(
        [&leaves[a].statement, &leaves[b].statement],
        [&leaves[a].proof, &leaves[b].proof],
      )
      .err()
      .expect("accepted nonadjacent genuine execution proofs");
    assert!(error.to_string().contains("advice constraints"), "{error:#}");
    eprintln!("{name} genuine execution segment rejected: {error:#}");
  }
  drop(node);
  let node = compiler.compile_component(Component::Execution, 3).unwrap();
  let root = record(&directory, "nodes/06/0000000003/0000000/0000000000");
  let expected =
    [leaves[0].statement[..30].to_vec(), leaves[2].statement[30..].to_vec()]
      .concat();
  assert_eq!(root.statement, expected);
  node.verify(&expected, &root.proof).unwrap();
  assert_eq!(expected[3], F128::ZERO);
  assert_eq!(expected[36], F128::new(0, 83));
  for at in 0..57 {
    for high in [false, true] {
      let mut wrong = expected.clone();
      if high {
        wrong[at].hi ^= 1 << 63;
      } else {
        wrong[at].lo ^= 1;
      }
      assert!(node.verify(&wrong, &root.proof).is_err());
    }
  }
  eprintln!(
    "three genuine execution batches: both recursive levels verify; all 57 low/high expected-word mutations reject"
  );
}
