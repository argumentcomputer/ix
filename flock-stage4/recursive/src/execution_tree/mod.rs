//! Recursive chains, ordered component joins, and the closing execution proof.
//! All setups, classes, counts and public layouts are approved before proof
//! bytes are read. Every deferred fixed-table claim survives to the root.
mod layout;
mod leaf;
mod matrices;
#[cfg(test)]
mod tests;
use crate::{
  accumulator::{PublishedRoot, collect_claims, fresh_tables, publish_roots},
  backend::{NativeBuilder, NativeGraph},
  fold::{FoldPlan, Groups, StaticTable, TableKey},
  pair::emit_child,
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
  ixbf_decode::paged::endpoints::{Component, FACT_WORDS, FunctionalProfile},
  paged_exec::BatchClass,
};
use ixby_stage4_exec::{
  CompiledFlockReplay, FlockVerifierSetup, GrammarBatchReplayWitness,
  compile_flock_replay,
};
use layout::{Layout, Relation, chain};
use leaf::Leaf;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, sync::Arc};

const DOMAIN: &[u8] = b"IxBy/Flock/paged-execution-tree/native/v0\0";
const MAGIC: [u8; 8] = *b"IXFPTR00";
pub const MAX_PAGED_TREE_BYTES: u64 = 32 * 1024 * 1024;
/// New protocol policy; the existing grammar tree's 65,536 bound is unchanged.
pub const MAX_PAGED_CHAIN_LEAVES: usize = 1 << 31;
fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_PAGED_TREE_BYTES)
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
struct Core {
  leaves: usize,
  layout: Layout,
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
enum Owner {
  Leaf(Arc<Leaf>),
  Node(Arc<Core>),
}
struct ChildSetup {
  owner: Owner,
  fresh: BTreeMap<TableKey, StaticTable>,
}
impl ChildSetup {
  fn setup(&self) -> &dyn FlockVerifierSetup {
    match &self.owner {
      Owner::Leaf(s) => s.as_ref(),
      Owner::Node(s) => s.as_ref(),
    }
  }
  fn layout(&self) -> Layout {
    match &self.owner {
      Owner::Leaf(s) => s.layout(),
      Owner::Node(s) => s.layout,
    }
  }
  fn leaves(&self) -> usize {
    match &self.owner {
      Owner::Leaf(_) => 1,
      Owner::Node(s) => s.leaves,
    }
  }
  fn identity(&self) -> [u8; 32] {
    if let Owner::Node(s) = &self.owner {
      return s.identity;
    }
    let mut h = blake3::Hasher::new();
    h.update(DOMAIN);
    h.update(b"leaf");
    h.update(&self.layout().encode());
    h.update(&self.transcript_domain());
    h.update(&self.registry_digest());
    h.update(&self.circuit_digest());
    h.update(&self.public_template().digest());
    *h.finalize().as_bytes()
  }
}
impl FlockVerifierSetup for Core {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Key {
  Component(Component, usize),
  Facts(usize, usize),
  Endpoints,
  Complete,
}

pub struct PagedTreeCompiler {
  profile: FunctionalProfile,
  class: BatchClass,
  counts: [usize; 11],
  children: BTreeMap<Key, Arc<ChildSetup>>,
}
impl PagedTreeCompiler {
  pub fn new(
    profile: FunctionalProfile,
    class: BatchClass,
    counts: [usize; 11],
  ) -> Result<Self> {
    ensure!(
      counts.iter().all(|n| (1..=MAX_PAGED_CHAIN_LEAVES).contains(n)),
      "paged component count outside policy"
    );
    ensure!(
      counts[Component::ConstructorIds as usize] == 1,
      "constructor IDs are one complete component"
    );
    counts.iter().try_fold(1usize, |sum, &n| {
      sum
        .checked_add(n)
        .ok_or_else(|| anyhow::anyhow!("total paged leaf count overflow"))
    })?;
    Ok(Self { profile, class, counts, children: BTreeMap::new() })
  }
  pub fn counts(&self) -> &[usize; 11] {
    &self.counts
  }
  pub fn profile(&self) -> &FunctionalProfile {
    &self.profile
  }
  pub fn batch_class(&self) -> BatchClass {
    self.class
  }
  fn component_key(&self, c: Component) -> Key {
    Key::Component(c, self.counts[c as usize])
  }
  fn child(&mut self, key: Key) -> Result<Arc<ChildSetup>> {
    if let Some(s) = self.children.get(&key) {
      return Ok(s.clone());
    }
    let leaf = match key {
      Key::Component(c, 1) => Some(Leaf::component(c, self.class)?),
      Key::Endpoints => Some(Leaf::endpoints(self.profile.clone())?),
      Key::Facts(first, end) if end == first + 1 => {
        return self.child(self.component_key(Component::ALL[first]));
      },
      _ => None,
    };
    if let Some(leaf) = leaf {
      let fresh = fresh_tables(&leaf)?;
      let child =
        Arc::new(ChildSetup { owner: Owner::Leaf(Arc::new(leaf)), fresh });
      self.children.insert(key, child.clone());
      return Ok(child);
    }
    drop(self.compile(key)?);
    Ok(self.children[&key].clone())
  }
  fn compile(&mut self, key: Key) -> Result<CompiledPagedNode> {
    let (relation, keys) = match key {
      Key::Component(c, n) => {
        ensure!(
          (2..=self.counts[c as usize]).contains(&n) && chain(c).is_some(),
          "invalid component subtree count"
        );
        let left = 1usize << (n - 1).ilog2();
        (
          Relation::Chain,
          [Key::Component(c, left), Key::Component(c, n - left)],
        )
      },
      Key::Facts(first, end) => {
        ensure!(
          first < end && end <= 11 && end - first >= 2,
          "invalid component range"
        );
        let middle = first + (1usize << (end - first - 1).ilog2());
        (Relation::Concat, [Key::Facts(first, middle), Key::Facts(middle, end)])
      },
      Key::Complete => (Relation::Close, [Key::Facts(0, 11), Key::Endpoints]),
      Key::Endpoints => anyhow::bail!("endpoint is a Stage 3 leaf"),
    };
    let children = [self.child(keys[0])?, self.child(keys[1])?];
    let node = CompiledPagedNode::compile(relation, children)?;
    if let Some(previous) = self.children.get(&key) {
      ensure!(
        previous.identity() == node.identity(),
        "recompiled paged node identity differs"
      );
    } else {
      let fresh = fresh_tables(node.core.as_ref())?;
      self.children.insert(
        key,
        Arc::new(ChildSetup { owner: Owner::Node(node.core.clone()), fresh }),
      );
    }
    Ok(node)
  }
  pub fn compile_component(
    &mut self,
    component: Component,
    leaves: usize,
  ) -> Result<CompiledPagedNode> {
    self.compile(Key::Component(component, leaves))
  }
  pub fn compile_components(
    &mut self,
    first: usize,
    end: usize,
  ) -> Result<CompiledPagedNode> {
    self.compile(Key::Facts(first, end))
  }
  pub fn compile_complete(&mut self) -> Result<CompiledPagedNode> {
    self.compile(Key::Complete)
  }
  /// Contains only the compiled final relation and its approved fixed tables.
  pub fn verifier(&mut self) -> Result<PagedExecutionVerifier> {
    let child = self.child(Key::Complete)?;
    let Owner::Node(core) = &child.owner else { unreachable!() };
    Ok(PagedExecutionVerifier { core: core.clone() })
  }
}

#[derive(Clone, Debug, Serialize)]
pub struct PagedNodeGeometry {
  pub leaves: usize,
  pub children: [usize; 2],
  pub application_words: usize,
  pub variables: usize,
  pub arithmetic_operations: usize,
  pub packing_rows: usize,
  pub blake3_compressions: usize,
  pub row_variables: usize,
  pub dense_variables: usize,
  pub root_families: usize,
  pub root_advice_words: usize,
}
pub struct PagedNodeProof {
  pub statement: Vec<F128>,
  pub proof: Vec<u8>,
}
pub struct CompiledPagedNode {
  core: Arc<Core>,
  relation: Relation,
  children: [CompiledFlockReplay<Arc<ChildSetup>>; 2],
  graph: NativeGraph,
  folds: FoldPlan,
  slots: Slots,
  nu: usize,
}
pub struct PagedExecutionVerifier {
  core: Arc<Core>,
}

impl CompiledPagedNode {
  fn compile(relation: Relation, setups: [Arc<ChildSetup>; 2]) -> Result<Self> {
    let layout = relation.layout(setups[0].layout(), setups[1].layout())?;
    let leaves = setups[0]
      .leaves()
      .checked_add(setups[1].leaves())
      .ok_or_else(|| anyhow::anyhow!("paged node count overflow"))?;
    if relation == Relation::Chain {
      ensure!(
        setups[0].leaves() == 1usize << (leaves - 1).ilog2(),
        "noncanonical component chain split"
      );
    }
    let [left, right] = setups.map(compile_flock_replay);
    let children = [left?, right?];
    let mut b = NativeBuilder::new(true);
    let (application, groups) =
      emit_children(&mut b, relation, &children, None)?;
    ensure!(
      application.len() == layout.width(),
      "paged node application width"
    );
    let folds = FoldPlan::compile(&groups)?;
    let roots = folds.emit(&mut b, &groups)?;
    let roots = publish_roots(&mut b, application, roots)?;
    let tables =
      groups.into_iter().map(|(k, (t, _))| (k, t)).collect::<BTreeMap<_, _>>();
    let (counter, nu, params) = count(&b.graph)?;
    let mut shape = ShapeBuilder::new(nu);
    let (slots, public) = emit_stable(&mut shape, &b.graph, nu)?;
    let shape =
      shape.finish().map_err(|e| anyhow::anyhow!("paged tree shape: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    let (registry, counts) = counter.registry(nu);
    ensure!(
      registry.digest() == shape.registry.digest() && counts == shape.counts,
      "paged tree count/shape registry"
    );
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    ensure!(
      union.dense_m() == params.m
        && union.commit_lanes(params.log_batch_size) == params.num_lanes,
      "paged tree PCS geometry"
    );
    let mut h = blake3::Hasher::new();
    h.update(DOMAIN);
    h.update(&[relation as u8]);
    h.update(&layout.encode());
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
    let core = Arc::new(Core {
      leaves,
      layout,
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
    Ok(Self { core, relation, children, graph: b.graph, folds, slots, nu })
  }
  pub fn identity(&self) -> [u8; 32] {
    self.core.identity
  }
  pub fn geometry(&self) -> PagedNodeGeometry {
    PagedNodeGeometry {
      leaves: self.core.leaves,
      children: self.children.each_ref().map(|c| c.setup().leaves()),
      application_words: self.core.layout.width(),
      variables: self.graph.variables,
      arithmetic_operations: self.graph.macs.len(),
      packing_rows: self.graph.packs.len(),
      blake3_compressions: self.graph.compressions.len(),
      row_variables: self.nu,
      dense_variables: self.core.params.m,
      root_families: self.core.roots.len(),
      root_advice_words: self.core.outputs - self.core.layout.width(),
    }
  }
  pub fn prove(
    &self,
    statements: [&[F128]; 2],
    proofs: [&[u8]; 2],
  ) -> Result<PagedNodeProof> {
    let left = replay_child(&self.children[0], statements[0], proofs[0])?;
    let right = replay_child(&self.children[1], statements[1], proofs[1])?;
    let mut b = NativeBuilder::new(false);
    let (application, groups) = emit_children(
      &mut b,
      self.relation,
      &self.children,
      Some([&left, &right]),
    )?;
    let roots = self.folds.emit(&mut b, &groups)?;
    let roots = publish_roots(&mut b, application, roots)?;
    ensure!(
      b.graph == self.graph && roots == self.core.roots,
      "paged tree advice graph differs from setup"
    );
    b.check()
      .map_err(|e| anyhow::anyhow!("paged tree advice constraints: {e}"))?;
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
    let width = self.core.layout.width();
    let bundle = Bundle {
      magic: MAGIC,
      identity: self.core.identity,
      leaves: u64::try_from(self.core.leaves)?,
      root_advice: outputs[width..].to_vec(),
      commitment,
      proof,
    };
    let proof = codec().serialize(&bundle)?;
    ensure!(
      proof.len() as u64 <= MAX_PAGED_TREE_BYTES,
      "paged tree proof size"
    );
    Ok(PagedNodeProof { statement: outputs[..width].to_vec(), proof })
  }
  pub fn verify(&self, expected: &[F128], bytes: &[u8]) -> Result<()> {
    self.core.verify(expected, bytes)
  }
  pub fn into_execution_verifier(self) -> Result<PagedExecutionVerifier> {
    ensure!(
      self.core.layout == Layout::Execution,
      "node is not the complete execution relation"
    );
    Ok(PagedExecutionVerifier { core: self.core })
  }
}
impl PagedExecutionVerifier {
  pub fn identity(&self) -> [u8; 32] {
    self.core.identity
  }
  pub fn verify(
    &self,
    statement_digest: [F128; 2],
    proof: &[u8],
  ) -> Result<()> {
    ensure!(
      self.core.layout == Layout::Execution,
      "complete execution verifier layout"
    );
    self.core.verify(&statement_digest, proof)
  }
}
impl Core {
  fn decode(
    &self,
    expected: &[F128],
    bytes: &[u8],
  ) -> Result<(Bundle, Vec<F128>, Vec<F128>)> {
    ensure!(
      expected.len() == self.layout.width(),
      "paged tree expected statement width"
    );
    ensure!(
      bytes.len() as u64 <= MAX_PAGED_TREE_BYTES,
      "paged tree proof size"
    );
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC
        && bundle.identity == self.identity
        && bundle.leaves == self.leaves as u64,
      "paged tree setup/revision/count"
    );
    ensure!(
      bundle.root_advice.len() == self.outputs - self.layout.width(),
      "paged tree root advice width"
    );
    ensure!(
      codec().serialize(&bundle)? == bytes,
      "noncanonical paged tree bundle"
    );
    let mut outputs = expected.to_vec();
    outputs.extend(&bundle.root_advice);
    let public = self.public.instantiate(&outputs)?;
    Ok((bundle, public, outputs))
  }
  fn verify(&self, expected: &[F128], bytes: &[u8]) -> Result<()> {
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
    .map_err(|e| anyhow::anyhow!("paged tree Flock proof rejected: {e:?}"))?;
    for (i, root) in self.roots.iter().enumerate() {
      let claim = MatrixClaim {
        row: Weight::eq(root.row.iter().map(|&i| outputs[i]).collect()),
        col: Weight::eq(root.column.iter().map(|&i| outputs[i]).collect()),
        value: outputs[root.value],
      };
      ensure!(
        self.tables[&root.key].check(&claim),
        "paged tree root family {i} rejected"
      );
    }
    Ok(())
  }
}
fn replay_child(
  replay: &CompiledFlockReplay<Arc<ChildSetup>>,
  expected: &[F128],
  bytes: &[u8],
) -> Result<GrammarBatchReplayWitness> {
  match &replay.setup().owner {
    Owner::Leaf(leaf) => leaf.replay(replay, expected, bytes),
    Owner::Node(node) => {
      // Inherited roots stay conditional here and are constrained into all
      // parent folds. The root verifier discharges the actual fixed tables.
      let (bundle, public, _) = node.decode(expected, bytes)?;
      replay.replay_proof(&public, &bundle.commitment, &bundle.proof)
    },
  }
}
fn emit_children(
  b: &mut NativeBuilder,
  relation: Relation,
  replays: &[CompiledFlockReplay<Arc<ChildSetup>>; 2],
  advice: Option<[&GrammarBatchReplayWitness; 2]>,
) -> Result<(Vec<usize>, Groups)> {
  let children = [
    emit_child(b, &replays[0], advice.map(|a| a[0]))?,
    emit_child(b, &replays[1], advice.map(|a| a[1]))?,
  ];
  let layouts = replays.each_ref().map(|c| c.setup().layout());
  let layout = relation.layout(layouts[0], layouts[1])?;
  for (child, replay) in children.iter().zip(replays) {
    ensure!(
      child.application.len() == replay.setup().public_template().outputs(),
      "paged child application width"
    );
    if let Owner::Leaf(_) = &replay.setup().owner
      && let Layout::Component(c) = replay.setup().layout()
      && let Some((shared, boundary)) = chain(c)
    {
      let zero = b.constant(F128::ZERO);
      let one = b.constant(F128::ONE);
      let mut total = zero;
      let mut chosen = false;
      for i in 0..boundary {
        let a = child.application[shared + i].word(b);
        let c = child.application[shared + boundary + i].word(b);
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
  let a = &children[0].application;
  let c = &children[1].application;
  let application: Vec<usize> = match relation {
    Relation::Chain => {
      let Layout::Component(kind) = layout else { unreachable!() };
      let (shared, boundary) = chain(kind).unwrap();
      for i in 0..shared {
        let a = a[i].word(b);
        let c = c[i].word(b);
        b.equal(a, c);
      }
      for i in 0..boundary {
        let a = a[shared + boundary + i].word(b);
        let c = c[shared + i].word(b);
        b.equal(a, c);
      }
      a[..shared + boundary]
        .iter()
        .chain(&c[shared + boundary..shared + 2 * boundary])
        .map(|v| v.word(b))
        .collect()
    },
    Relation::Concat => a[..layouts[0].width()]
      .iter()
      .chain(&c[..layouts[1].width()])
      .map(|v| v.word(b))
      .collect(),
    Relation::Close => {
      for i in 0..FACT_WORDS {
        let a = a[i].word(b);
        let c = c[i].word(b);
        b.equal(a, c);
      }
      c[FACT_WORDS..FACT_WORDS + 2].iter().map(|v| v.word(b)).collect()
    },
  };
  ensure!(application.len() == layout.width(), "paged publication width");
  let mut groups = BTreeMap::new();
  for (child, replay) in children.iter().zip(replays) {
    let inherited = match &replay.setup().owner {
      Owner::Leaf(_) => None,
      Owner::Node(node) => {
        Some((node.roots.as_slice(), &node.tables, node.outputs))
      },
    };
    collect_claims(b, &replay.setup().fresh, child, &mut groups, inherited)?;
  }
  Ok((application, matrices::canonicalize(groups)?))
}
