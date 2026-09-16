use super::*;
use std::{
  io::{Read, Write},
  path::{Path, PathBuf},
  time::Instant,
};

const ROOT: &str =
  "96ed4322c7e4db289b876848e885d02afd2958f829135d5108b565ce9d493c05";
const LENGTH: u64 = 1_016_587;
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
fn write_new(path: &Path, bytes: &[u8]) {
  std::fs::OpenOptions::new()
    .create_new(true)
    .write(true)
    .open(path)
    .unwrap()
    .write_all(bytes)
    .unwrap();
}
fn read_statement(path: &Path) -> GrammarBatchStatement {
  let bytes = read(path, 63 * 16);
  assert_eq!(bytes.len(), 63 * 16);
  let words = bytes
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| ixby_flock::hash::pack_bytes(word))
    .collect::<Vec<_>>();
  GrammarBatchStatement::from_words(&words).unwrap()
}
fn join(
  left: &GrammarBatchStatement,
  right: &GrammarBatchStatement,
) -> GrammarBatchStatement {
  assert_eq!(left.final_state(), right.initial());
  let mut words = *left.words();
  words[33..].copy_from_slice(&right.words()[33..]);
  GrammarBatchStatement::from_words(&words).unwrap()
}
fn frames(count: usize) -> Vec<(GrammarBatchStatement, Vec<u8>)> {
  let directory =
    PathBuf::from(std::env::var_os("IXBY_CSLIB_FRAME_DIR").unwrap());
  let root = blake3::Hash::from_hex(ROOT).unwrap();
  let mut state = [F128::ZERO; 30];
  state[0] = F128::new(0, LENGTH);
  (0..count)
    .map(|index| {
      let bytes = read(
        &directory.join(format!("program-{index:06}.frame")),
        8 * 1024 * 1024,
      );
      assert_eq!(
        bytes.len(),
        484 + u32::from_le_bytes(bytes[..4].try_into().unwrap()) as usize
      );
      let end = std::array::from_fn(|i| {
        ixby_flock::hash::pack_bytes(&bytes[4 + 16 * i..20 + 16 * i])
      });
      let statement =
        GrammarBatchStatement::new(LENGTH, *root.as_bytes(), state, end)
          .unwrap();
      state = end;
      (statement, bytes[484..].to_vec())
    })
    .collect()
}
fn prove(
  node: &CompiledGrammarNode,
  left: &(GrammarBatchStatement, Vec<u8>),
  right: &(GrammarBatchStatement, Vec<u8>),
) -> (GrammarBatchStatement, Vec<u8>) {
  let statement = join(&left.0, &right.0);
  let start = Instant::now();
  let bytes = node.prove([&left.0, &right.0], [&left.1, &right.1]).unwrap();
  eprintln!(
    "tree node {} proved {:?}, {} bytes",
    node.core.leaves,
    start.elapsed(),
    bytes.len()
  );
  let start = Instant::now();
  node.verify(&statement, &bytes).unwrap();
  eprintln!("tree node {} verified {:?}", node.core.leaves, start.elapsed());
  (statement, bytes)
}
fn compile(
  compiler: &mut GrammarTreeCompiler,
  leaves: usize,
) -> CompiledGrammarNode {
  let start = Instant::now();
  let node = compiler.compile(leaves).unwrap();
  eprintln!(
    "tree setup {:?}: {:?}; identity {}",
    start.elapsed(),
    node.geometry(),
    blake3::Hash::from(node.identity())
  );
  node
}

#[test]
#[ignore = "proof-free geometry census, IXBY_TREE_LEAVES selects the approved count"]
fn grammar_tree_setup_geometry() {
  let leaves: usize =
    std::env::var("IXBY_TREE_LEAVES").unwrap().parse().unwrap();
  let mut compiler = GrammarTreeCompiler::new(GrammarKind::Program).unwrap();
  let _node = compile(&mut compiler, leaves);
}

#[test]
#[ignore = "requires five retained CSLib frames and IXBY_TREE_PROOF_OUT"]
fn retained_five_batches_fold_across_three_levels() {
  let mut compiler = GrammarTreeCompiler::new(GrammarKind::Program).unwrap();
  let pair = compile(&mut compiler, 2);
  let four = compile(&mut compiler, 4);
  let five = compile(&mut compiler, 5);
  let leaves = frames(5);
  let left = prove(&pair, &leaves[0], &leaves[1]);
  let right = prove(&pair, &leaves[2], &leaves[3]);
  assert!(
    pair
      .prove([&leaves[0].0, &leaves[0].0], [&leaves[0].1, &leaves[0].1])
      .is_err()
  );
  let first_four = prove(&four, &left, &right);
  let result = prove(&five, &first_four, &leaves[4]);
  assert!(four.verify(&result.0, &result.1).is_err());
  let output = PathBuf::from(std::env::var_os("IXBY_TREE_PROOF_OUT").unwrap());
  write_new(&output, &result.1);
  let statement = output.with_extension("statement");
  write_new(
    &statement,
    &result
      .0
      .words()
      .iter()
      .flat_map(|&v| crate::f128::bytes(v))
      .collect::<Vec<_>>(),
  );
  drop(pair);
  drop(four);
  drop(five);
  drop(compiler);
  drop(leaves);
  let status = std::process::Command::new(std::env::current_exe().unwrap())
    .args(["--exact", "tree::tests::root_receiver", "--ignored", "--nocapture"])
    .env_clear()
    .env("RAYON_NUM_THREADS", "4")
    .env("IXBY_TREE_ROOT", &output)
    .env("IXBY_TREE_EXPECTED", &statement)
    .env("IXBY_TREE_LEAVES", "5")
    .status()
    .unwrap();
  assert!(status.success(), "fresh grammar tree receiver rejected");
}

#[test]
#[ignore = "fresh receiver: only final root, expected statement and expected leaf count"]
fn root_receiver() {
  let count: usize =
    std::env::var("IXBY_TREE_LEAVES").unwrap().parse().unwrap();
  let bytes = read(
    &PathBuf::from(std::env::var_os("IXBY_TREE_ROOT").unwrap()),
    MAX_GRAMMAR_TREE_BYTES,
  );
  let statement = read_statement(&PathBuf::from(
    std::env::var_os("IXBY_TREE_EXPECTED").unwrap(),
  ));
  let start = Instant::now();
  let mut compiler = GrammarTreeCompiler::new(GrammarKind::Program).unwrap();
  let node = compiler.compile(count).unwrap().into_verifier();
  drop(compiler);
  eprintln!(
    "fresh tree verifier compiled {:?}; identity {}",
    start.elapsed(),
    blake3::Hash::from(node.identity())
  );
  let start = Instant::now();
  node.verify(&statement, &bytes).unwrap();
  eprintln!(
    "fresh final tree verification {:?}; leaves={count}, bytes={}, no child proofs supplied",
    start.elapsed(),
    bytes.len()
  );
  for position in [1, 3 + 29, 33 + 29] {
    let mut words = *statement.words();
    words[position] += F128::ONE;
    assert!(
      node
        .verify(&GrammarBatchStatement::from_words(&words).unwrap(), &bytes)
        .is_err()
    );
  }
  let mut bundle: Bundle = codec().deserialize(&bytes).unwrap();
  bundle.root_advice[0] += F128::ONE;
  assert!(
    node.verify(&statement, &codec().serialize(&bundle).unwrap()).is_err()
  );
  let mut bundle: Bundle = codec().deserialize(&bytes).unwrap();
  bundle.leaves += 1;
  assert!(
    node.verify(&statement, &codec().serialize(&bundle).unwrap()).is_err()
  );
  let mut trailing = bytes.clone();
  trailing.push(0);
  assert!(node.verify(&statement, &trailing).is_err());
  assert!(node.verify(&statement, &bytes[..bytes.len() - 1]).is_err());
}
