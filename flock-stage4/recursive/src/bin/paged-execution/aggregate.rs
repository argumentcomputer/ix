//! Canonical component chains followed by all eleven ordered component roots
//! and the endpoint relation. Only the final statement digest is published.
use super::Store;
use crate::store::{join, node_name, words_bytes};
use anyhow::{Result, ensure};
use flock_prover::field::F128;
use ix_flock_recursion::{
  CompiledPagedNode, PagedNodeProof, PagedTreeCompiler,
};
use ixby_flock::ixby::ixbf_decode::paged::endpoints::{
  Component, FACT_WORDS, PUBLIC_WORDS,
};
use serde_json::json;
use std::time::Instant;

fn prove_node(
  store: &Store,
  name: &str,
  node: &CompiledPagedNode,
  expected: &[F128],
  left: &PagedNodeProof,
  right: &PagedNodeProof,
) -> Result<()> {
  store.prove(
    name,
    expected,
    || {
      let p = node.prove(
        [&left.statement, &right.statement],
        [&left.proof, &right.proof],
      )?;
      ensure!(
        p.statement == expected,
        "recursive statement publication differs"
      );
      Ok(p.proof)
    },
    |p| node.verify(expected, p),
  )
}
fn chain_job(
  store: &Store,
  node: &CompiledPagedNode,
  c: Component,
  start: usize,
  left_count: usize,
  right_count: usize,
) -> Result<()> {
  let left = store.get(&node_name(c, start, left_count), c.range().len())?;
  let right = store
    .get(&node_name(c, start + left_count, right_count), c.range().len())?;
  let expected = join(c, &left.statement, &right.statement)?;
  prove_node(
    store,
    &node_name(c, start, left_count + right_count),
    node,
    &expected,
    &left,
    &right,
  )
}
fn chain(
  compiler: &mut PagedTreeCompiler,
  store: &Store,
  c: Component,
) -> Result<()> {
  let count = compiler.counts()[c as usize];
  if count == 1 {
    return Ok(());
  }
  let mut width = 2;
  while width <= count {
    let started = Instant::now();
    let node = compiler.compile_component(c, width)?;
    eprintln!(
      "{}",
      json!({"event":"chain_setup","component":c as usize,"leaves":width,
      "seconds":started.elapsed().as_secs_f64(),"geometry":node.geometry()})
    );
    for i in 0..count / width {
      chain_job(store, &node, c, i * width, width / 2, width / 2)?;
    }
    if width > count / 2 {
      break;
    }
    width *= 2;
  }
  let mut forest = Vec::new();
  let mut start = 0;
  while start < count {
    let leaves = 1usize << (count - start).ilog2();
    forest.push((start, leaves));
    start += leaves;
  }
  let (mut start, mut leaves) = forest.pop().unwrap();
  while let Some((first, n)) = forest.pop() {
    ensure!(first + n == start, "component forest adjacency");
    let node = compiler.compile_component(c, n + leaves)?;
    chain_job(store, &node, c, first, n, leaves)?;
    start = first;
    leaves += n;
  }
  ensure!(start == 0 && leaves == count, "incomplete component tree");
  Ok(())
}
fn facts(
  compiler: &mut PagedTreeCompiler,
  store: &Store,
  first: usize,
  end: usize,
) -> Result<PagedNodeProof> {
  if first + 1 == end {
    let c = Component::ALL[first];
    return store
      .get(&node_name(c, 0, compiler.counts()[first]), c.range().len());
  }
  let middle = first + (1usize << (end - first - 1).ilog2());
  let left = facts(compiler, store, first, middle)?;
  let right = facts(compiler, store, middle, end)?;
  let expected =
    [left.statement.as_slice(), right.statement.as_slice()].concat();
  let started = Instant::now();
  let node = compiler.compile_components(first, end)?;
  let name = format!("facts-{first:02}-{end:02}");
  eprintln!(
    "{}",
    json!({"event":"facts_setup","name":name,
    "seconds":started.elapsed().as_secs_f64(),"geometry":node.geometry()})
  );
  prove_node(store, &name, &node, &expected, &left, &right)?;
  store.get(&name, expected.len())
}
pub(super) fn complete(
  compiler: &mut PagedTreeCompiler,
  store: &Store,
  expected: [F128; 2],
) -> Result<serde_json::Value> {
  let started = Instant::now();
  // Preflight the exact final setup before producing any recursive proofs.
  // Cached cores survive; large emission graphs are rebuilt only as needed.
  let node = compiler.compile_complete()?;
  let identity = blake3::Hash::from(node.identity()).to_hex().to_string();
  let geometry = node.geometry();
  eprintln!(
    "{}",
    json!({"event":"complete_setup","identity":identity,
    "seconds":started.elapsed().as_secs_f64(),"geometry":geometry})
  );
  if store.directory().join("root.flock").exists()
    && store.directory().join("root.statement").exists()
  {
    let root = store.get("root", 2)?;
    ensure!(root.statement == expected, "cached root statement differs");
    let checking = Instant::now();
    node.verify(&expected, &root.proof)?;
    return Ok(json!({"accepted":true,"reused_root":true,
      "claim":"complete original-format paged execution", "counts":compiler.counts(),
      "proof_bytes":root.proof.len(),"identity":identity,"geometry":geometry,
      "elapsed_seconds":started.elapsed().as_secs_f64(),
      "verification_seconds":checking.elapsed().as_secs_f64()}));
  }
  drop(node);
  for c in Component::ALL {
    chain(compiler, store, c)?;
  }
  let facts = facts(compiler, store, 0, 11)?;
  let endpoints = store.get("endpoints", PUBLIC_WORDS)?;
  ensure!(
    facts.statement.len() == FACT_WORDS
      && facts.statement == endpoints.statement[..FACT_WORDS],
    "complete endpoint facts differ"
  );
  ensure!(
    endpoints.statement[FACT_WORDS..] == expected,
    "endpoint statement differs from the externally expected digest"
  );
  let node = compiler.compile_complete()?;
  prove_node(store, "root", &node, &expected, &facts, &endpoints)?;
  let root = store.get("root", 2)?;
  let verifier = node.into_execution_verifier()?;
  let checking = Instant::now();
  verifier.verify(expected, &root.proof)?;
  store.save_bytes("expected.statement", &words_bytes(&expected))?;
  let result = json!({"accepted":true,"claim":"complete original-format paged execution",
    "counts":compiler.counts(),"proof_bytes":root.proof.len(),"identity":identity,
    "geometry":geometry,"elapsed_seconds":started.elapsed().as_secs_f64(),
    "verification_seconds":checking.elapsed().as_secs_f64()});
  // Timing records are per invocation; retained cryptographic files are fixed.
  Ok(result)
}
