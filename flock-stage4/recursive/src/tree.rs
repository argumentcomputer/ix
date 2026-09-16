//! Finite, proof-free compilation of the canonical grammar aggregation tree.
//! A node with N leaves splits at the largest power of two below N. Setups
//! depend on grammar and leaf count, never on a file, proof, state, or advice.
use crate::{
  accumulator::{PublishedRoot, collect_claims, fresh_tables, publish_roots},
  backend::{NativeBuilder, NativeGraph},
  fold::{Claim, FoldPlan, Groups, StaticTable, TableKey},
  pair::{ChildWires, emit_child},
  proof::{Slots, count, emit_stable, prove_native},
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder},
  field::F128,
  lincheck::CscCircuit,
  matrix_fold::{MatrixClaim, Weight},
  pcs::{Commitment, PcsParams},
  proof::R1csProofCircuitMerged,
  union::UnionInstance,
  verifier,
};
use ixby_flock::ixby::{
  io::PublicLayout,
  ixbf_decode::{
    GrammarKind,
    stream::batch::{CompiledGrammarBatch, GrammarBatchStatement},
  },
};
use ixby_stage4_exec::{
  CompiledFlockReplay, FlockVerifierSetup, GrammarBatchReplayWitness,
  compile_flock_replay,
};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, sync::Arc};

const DOMAIN: &[u8] = b"IxBy/Flock/grammar-tree/native/v0\0";
const MAGIC: [u8; 8] = *b"IXFSTR00";
const APPLICATION: usize = 63;
pub const MAX_GRAMMAR_TREE_BYTES: u64 = 32 * 1024 * 1024;
/// A policy bound, chosen by the caller before any proof is read.
pub const MAX_GRAMMAR_TREE_LEAVES: usize = 1 << 16;

fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_GRAMMAR_TREE_BYTES)
    .reject_trailing_bytes()
}
#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  identity: [u8; 32],
  leaves: u64,
  root_advice: Vec<F128>,
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}
struct NodeCore {
  leaves: usize,
  kind: GrammarKind,
  shape: CircuitShape,
  public: PublicLayout,
  params: PcsParams,
  domain: Vec<u8>,
  identity: [u8; 32],
  roots: Vec<PublishedRoot>,
  tables: BTreeMap<TableKey, StaticTable>,
  outputs: usize,
  lincheck: CscCircuit,
}
enum ChildOwner {
  Leaf(Arc<CompiledGrammarBatch>),
  Node(Arc<NodeCore>),
}
struct ChildSetup {
  owner: ChildOwner,
  fresh: BTreeMap<TableKey, StaticTable>,
}
impl FlockVerifierSetup for NodeCore {
  fn verifier_shape(&self) -> &CircuitShape {
    &self.shape
  }
  fn public_template(&self) -> &PublicLayout {
    &self.public
  }
  fn pcs_params(&self) -> &PcsParams {
    &self.params
  }
  fn transcript_domain(&self) -> Vec<u8> {
    self.domain.clone()
  }
  fn registry_digest(&self) -> [u8; 32] {
    self.shape.registry.digest()
  }
  fn circuit_digest(&self) -> [u8; 32] {
    self.shape.circuit.digest()
  }
}
impl ChildSetup {
  fn kind(&self) -> GrammarKind {
    match &self.owner {
      ChildOwner::Leaf(s) => s.kind(),
      ChildOwner::Node(s) => s.kind,
    }
  }
  fn setup(&self) -> &dyn FlockVerifierSetup {
    match &self.owner {
      ChildOwner::Leaf(s) => s.as_ref(),
      ChildOwner::Node(s) => s.as_ref(),
    }
  }
  fn leaves(&self) -> usize {
    match &self.owner {
      ChildOwner::Leaf(_) => 1,
      ChildOwner::Node(s) => s.leaves,
    }
  }
  fn identity(&self) -> [u8; 32] {
    match &self.owner {
      ChildOwner::Leaf(s) => {
        let mut h = blake3::Hasher::new();
        h.update(&s.transcript_domain());
        h.update(&s.verifier_shape().registry.digest());
        h.update(&s.verifier_shape().circuit.digest());
        h.update(&s.public_template().digest());
        *h.finalize().as_bytes()
      },
      ChildOwner::Node(s) => s.identity,
    }
  }
}
impl FlockVerifierSetup for ChildSetup {
  fn verifier_shape(&self) -> &CircuitShape {
    self.setup().verifier_shape()
  }
  fn public_template(&self) -> &PublicLayout {
    self.setup().public_template()
  }
  fn pcs_params(&self) -> &PcsParams {
    self.setup().pcs_params()
  }
  fn transcript_domain(&self) -> Vec<u8> {
    self.setup().transcript_domain()
  }
  fn registry_digest(&self) -> [u8; 32] {
    self.setup().registry_digest()
  }
  fn circuit_digest(&self) -> [u8; 32] {
    self.setup().circuit_digest()
  }
}
/// Reuses each immutable subtree setup during a bounded aggregation run.
pub struct GrammarTreeCompiler {
  children: BTreeMap<usize, Arc<ChildSetup>>,
}
impl GrammarTreeCompiler {
  pub fn new(kind: GrammarKind) -> Result<Self> {
    let leaf = Arc::new(CompiledGrammarBatch::compile(kind)?);
    let fresh = fresh_tables(leaf.as_ref())?;
    let child = Arc::new(ChildSetup { owner: ChildOwner::Leaf(leaf), fresh });
    Ok(Self { children: BTreeMap::from([(1, child)]) })
  }
  /// Obtain a root verifier from approved setup, without retaining proving
  /// graphs. The caller selects the exact count before reading proof bytes.
  pub fn verifier(&mut self, leaves: usize) -> Result<GrammarRootVerifier> {
    ensure!(
      (2..=MAX_GRAMMAR_TREE_LEAVES).contains(&leaves),
      "grammar tree leaf count outside policy"
    );
    let child = self.child(leaves)?;
    let ChildOwner::Node(core) = &child.owner else { unreachable!() };
    Ok(GrammarRootVerifier { core: core.clone() })
  }
  fn child(&mut self, leaves: usize) -> Result<Arc<ChildSetup>> {
    if let Some(child) = self.children.get(&leaves) {
      return Ok(child.clone());
    }
    let node = self.compile(leaves)?;
    drop(node);
    Ok(self.children[&leaves].clone())
  }
  /// Exact leaf count is trusted application setup, never a proof header input.
  pub fn compile(&mut self, leaves: usize) -> Result<CompiledGrammarNode> {
    ensure!(
      (2..=MAX_GRAMMAR_TREE_LEAVES).contains(&leaves),
      "grammar tree leaf count outside policy"
    );
    let left = 1usize << (leaves - 1).ilog2();
    let children = [self.child(left)?, self.child(leaves - left)?];
    let node = CompiledGrammarNode::compile(children)?;
    if let Some(previous) = self.children.get(&leaves) {
      ensure!(
        previous.identity() == node.core.identity,
        "recompiled grammar tree identity"
      );
    } else {
      let fresh = fresh_tables(node.core.as_ref())?;
      self.children.insert(
        leaves,
        Arc::new(ChildSetup {
          owner: ChildOwner::Node(node.core.clone()),
          fresh,
        }),
      );
    }
    Ok(node)
  }
}

#[derive(Clone, Debug, Serialize)]
pub struct GrammarNodeGeometry {
  pub leaves: usize,
  pub children: [usize; 2],
  pub variables: usize,
  pub arithmetic_operations: usize,
  pub packing_rows: usize,
  pub blake3_compressions: usize,
  pub row_variables: usize,
  pub dense_variables: usize,
  pub root_families: usize,
  pub root_advice_words: usize,
}
pub struct CompiledGrammarNode {
  core: Arc<NodeCore>,
  children: [CompiledFlockReplay<Arc<ChildSetup>>; 2],
  graph: NativeGraph,
  folds: FoldPlan,
  slots: Slots,
  nu: usize,
}
impl CompiledGrammarNode {
  fn compile(children: [Arc<ChildSetup>; 2]) -> Result<Self> {
    let started = std::time::Instant::now();
    let trace = std::env::var_os("IXBY_TRACE_COMPILE").is_some();
    let progress = |phase| {
      if trace {
        eprintln!("tree compile {phase}: {:?}", started.elapsed());
      }
    };
    let kind = children[0].kind();
    ensure!(children[1].kind() == kind, "grammar tree child kind mismatch");
    let leaves = children[0].leaves() + children[1].leaves();
    let left = 1usize << (leaves - 1).ilog2();
    ensure!(children[0].leaves() == left, "noncanonical grammar tree split");
    let children = children.map(compile_flock_replay);
    let [left, right] = children;
    let children = [left?, right?];
    progress("replays");
    let mut b = NativeBuilder::new(true);
    let (application, groups) = emit_children(&mut b, &children, None)?;
    progress("child constraints");
    let folds = FoldPlan::compile(&groups)?;
    progress("fold transcript plan");
    let roots = folds.emit(&mut b, &groups)?;
    progress("fold constraints");
    let roots = publish(&mut b, application, roots)?;
    let tables =
      groups.into_iter().map(|(k, (t, _))| (k, t)).collect::<BTreeMap<_, _>>();
    let (count, nu, params) = count(&b.graph)?;
    progress("count");
    let mut shape = ShapeBuilder::new(nu);
    let (slots, public) = emit_stable(&mut shape, &b.graph, nu)?;
    progress("shape emission");
    let shape = shape
      .finish()
      .map_err(|e| anyhow::anyhow!("grammar tree shape: {e:?}"))?;
    progress("shape finish");
    count.ensure_matches(&shape)?;
    let (registry, counts) = count.registry(nu);
    ensure!(
      registry.digest() == shape.registry.digest() && counts == shape.counts,
      "grammar tree count/shape registry"
    );
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    ensure!(
      union.dense_m() == params.m
        && union.commit_lanes(params.log_batch_size) == params.num_lanes,
      "grammar tree PCS geometry"
    );
    let mut h = blake3::Hasher::new();
    h.update(DOMAIN);
    h.update(&u64::try_from(leaves)?.to_le_bytes());
    for child in &children {
      h.update(&child.setup().identity());
      h.update(&child.identity());
    }
    h.update(&shape.registry.digest());
    h.update(&shape.circuit.digest());
    h.update(&public.digest());
    h.update(&u64::try_from(params.m)?.to_le_bytes());
    h.update(&u64::try_from(params.log_batch_size)?.to_le_bytes());
    h.update(&[u8::from(params.num_lanes.is_some())]);
    h.update(&u64::try_from(params.num_lanes.unwrap_or(0))?.to_le_bytes());
    h.update(b"Slim128/Blake3/FoldGrinding(1,2)");
    for root in &roots {
      h.update(&root.key.encode());
    }
    let identity = *h.finalize().as_bytes();
    let mut domain = DOMAIN.to_vec();
    domain.extend(identity);
    let ty = &shape.registry.boolean_types()[0];
    let lincheck =
      CscCircuit::from_matrices(&ty.a_0, &ty.b_0).with_const_pin(ty.const_pin);
    let core = Arc::new(NodeCore {
      leaves,
      kind,
      shape,
      public,
      params,
      domain,
      identity,
      roots,
      tables,
      outputs: b.graph.published.len(),
      lincheck,
    });
    Ok(Self { core, children, graph: b.graph, folds, slots, nu })
  }
  pub fn identity(&self) -> [u8; 32] {
    self.core.identity
  }
  pub fn geometry(&self) -> GrammarNodeGeometry {
    GrammarNodeGeometry {
      leaves: self.core.leaves,
      children: self.children.each_ref().map(|c| c.setup().leaves()),
      variables: self.graph.variables,
      arithmetic_operations: self.graph.macs.len(),
      packing_rows: self.graph.packs.len(),
      blake3_compressions: self.graph.compressions.len(),
      row_variables: self.nu,
      dense_variables: self.core.params.m,
      root_families: self.core.roots.len(),
      root_advice_words: self.core.outputs - APPLICATION,
    }
  }
  pub fn prove(
    &self,
    statements: [&GrammarBatchStatement; 2],
    proofs: [&[u8]; 2],
  ) -> Result<Vec<u8>> {
    let left = replay_child(&self.children[0], statements[0], proofs[0])?;
    let right = replay_child(&self.children[1], statements[1], proofs[1])?;
    let mut b = NativeBuilder::new(false);
    let (application, groups) =
      emit_children(&mut b, &self.children, Some([&left, &right]))?;
    let roots = self.folds.emit(&mut b, &groups)?;
    let roots = publish(&mut b, application, roots)?;
    ensure!(
      b.graph == self.graph && roots == self.core.roots,
      "grammar tree advice graph differs from setup"
    );
    b.check()
      .map_err(|e| anyhow::anyhow!("grammar tree advice constraints: {e}"))?;
    let (proof, commitment, outputs) = prove_native(
      &self.core.shape,
      &self.slots,
      &self.core.public,
      self.nu,
      &self.core.params,
      &self.core.lincheck,
      b,
      &self.core.domain,
    )?;
    let bundle = Bundle {
      magic: MAGIC,
      identity: self.core.identity,
      leaves: u64::try_from(self.core.leaves)?,
      root_advice: outputs[APPLICATION..].to_vec(),
      commitment,
      proof,
    };
    let bytes = codec().serialize(&bundle)?;
    ensure!(
      bytes.len() as u64 <= MAX_GRAMMAR_TREE_BYTES,
      "grammar tree proof size"
    );
    Ok(bytes)
  }
  pub fn verify(
    &self,
    expected: &GrammarBatchStatement,
    proof: &[u8],
  ) -> Result<()> {
    self.core.verify(expected, proof)
  }
  /// Release proving graphs and child replay blueprints after preprocessing.
  pub fn into_verifier(self) -> GrammarRootVerifier {
    GrammarRootVerifier { core: self.core }
  }
}
pub struct GrammarRootVerifier {
  core: Arc<NodeCore>,
}
impl GrammarRootVerifier {
  pub fn identity(&self) -> [u8; 32] {
    self.core.identity
  }
  pub fn leaves(&self) -> usize {
    self.core.leaves
  }
  pub fn verify(
    &self,
    expected: &GrammarBatchStatement,
    proof: &[u8],
  ) -> Result<()> {
    self.core.verify(expected, proof)
  }
  /// Verify one complete file. The caller supplies its expected source digest,
  /// length and (for transports) the context from a verified Program.
  pub fn verify_complete(
    &self,
    expected: &GrammarBatchStatement,
    context: &[F128; 15],
    proof: &[u8],
  ) -> Result<()> {
    self.core.verify(expected, proof)?;
    expected.check_complete(self.core.kind, context)
  }
}
impl NodeCore {
  fn decode(
    &self,
    expected: &GrammarBatchStatement,
    bytes: &[u8],
  ) -> Result<(Bundle, Vec<F128>, Vec<F128>)> {
    ensure!(
      bytes.len() as u64 <= MAX_GRAMMAR_TREE_BYTES,
      "grammar tree proof size"
    );
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC
        && bundle.identity == self.identity
        && bundle.leaves == self.leaves as u64,
      "grammar tree setup/revision/count"
    );
    ensure!(
      bundle.root_advice.len() == self.outputs - APPLICATION,
      "grammar tree root advice width"
    );
    ensure!(
      codec().serialize(&bundle)? == bytes,
      "noncanonical grammar tree bundle"
    );
    let mut outputs = expected.words().to_vec();
    outputs.extend_from_slice(&bundle.root_advice);
    let public = self.public.instantiate(&outputs)?;
    Ok((bundle, public, outputs))
  }
  fn verify(
    &self,
    expected: &GrammarBatchStatement,
    bytes: &[u8],
  ) -> Result<()> {
    let (bundle, public, outputs) = self.decode(expected, bytes)?;
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut ch = FsChallenger::with_chained_blake3(&self.domain);
    verifier::verify_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &public,
      &[&self.lincheck],
      &bundle.commitment,
      &bundle.proof,
      &self.params,
      &mut ch,
    )
    .map_err(|e| anyhow::anyhow!("grammar tree Flock proof rejected: {e:?}"))?;
    for (i, root) in self.roots.iter().enumerate() {
      let claim = MatrixClaim {
        row: Weight::eq(root.row.iter().map(|&i| outputs[i]).collect()),
        col: Weight::eq(root.column.iter().map(|&i| outputs[i]).collect()),
        value: outputs[root.value],
      };
      ensure!(
        self.tables[&root.key].check(&claim),
        "grammar tree root family {i} rejected"
      );
    }
    Ok(())
  }
}
fn replay_child(
  replay: &CompiledFlockReplay<Arc<ChildSetup>>,
  expected: &GrammarBatchStatement,
  bytes: &[u8],
) -> Result<GrammarBatchReplayWitness> {
  match &replay.setup().owner {
    ChildOwner::Leaf(leaf) => {
      let verified = leaf.verify_for_replay(expected, bytes)?;
      replay.replay_proof(
        verified.public_values(),
        verified.commitment(),
        verified.proof(),
      )
    },
    ChildOwner::Node(node) => {
      // Replay checks the child Flock proof conditionally. Every inherited
      // root is read from its authenticated public vector and constrained
      // into this node's folds; the final verifier discharges those tables.
      let (bundle, public, _) = node.decode(expected, bytes)?;
      replay.replay_proof(&public, &bundle.commitment, &bundle.proof)
    },
  }
}
fn child_claims(
  b: &mut NativeBuilder,
  setup: &ChildSetup,
  child: &ChildWires,
  groups: &mut Groups,
) -> Result<()> {
  let inherited = match &setup.owner {
    ChildOwner::Leaf(_) => None,
    ChildOwner::Node(node) => {
      Some((node.roots.as_slice(), &node.tables, node.outputs))
    },
  };
  collect_claims(b, &setup.fresh, child, groups, inherited)
}
fn emit_children(
  b: &mut NativeBuilder,
  replays: &[CompiledFlockReplay<Arc<ChildSetup>>; 2],
  advice: Option<[&GrammarBatchReplayWitness; 2]>,
) -> Result<(Vec<usize>, Groups)> {
  let left = emit_child(b, &replays[0], advice.map(|a| a[0]))?;
  let right = emit_child(b, &replays[1], advice.map(|a| a[1]))?;
  ensure!(
    left.application.len() >= APPLICATION
      && right.application.len() >= APPLICATION,
    "grammar tree application width"
  );
  for (child, replay) in [&left, &right].into_iter().zip(replays) {
    if replay.setup().leaves() == 1 {
      // A linear combination of endpoint differences equals one iff at
      // least one word changes. Coefficients are private advice, not setup.
      let zero = b.constant(F128::ZERO);
      let one = b.constant(F128::ONE);
      let mut total = zero;
      let mut chosen = false;
      for i in 0..30 {
        let a = child.application[3 + i].word(b);
        let c = child.application[33 + i].word(b);
        let delta = b.add(a, c);
        let value = b.values[delta];
        let coefficient = if !chosen && value != F128::ZERO {
          chosen = true;
          value.inv()
        } else {
          F128::ZERO
        };
        let coefficient = b.alloc(coefficient);
        let term = b.multiply(delta, coefficient);
        total = b.add(total, term);
      }
      b.equal(total, one);
    }
  }
  for i in 0..3 {
    let a = left.application[i].word(b);
    let c = right.application[i].word(b);
    b.equal(a, c);
  }
  for i in 0..30 {
    let a = left.application[33 + i].word(b);
    let c = right.application[3 + i].word(b);
    b.equal(a, c);
  }
  let application = left.application[..33]
    .iter()
    .chain(&right.application[33..63])
    .map(|v| v.word(b))
    .collect();
  let mut groups = BTreeMap::new();
  child_claims(b, replays[0].setup(), &left, &mut groups)?;
  child_claims(b, replays[1].setup(), &right, &mut groups)?;
  Ok((application, groups))
}
fn publish(
  b: &mut NativeBuilder,
  application: Vec<usize>,
  roots: Vec<(TableKey, Claim)>,
) -> Result<Vec<PublishedRoot>> {
  ensure!(application.len() == APPLICATION, "grammar tree output width");
  publish_roots(b, application, roots)
}

#[cfg(test)]
mod tests;
