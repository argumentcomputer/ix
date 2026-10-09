//! Validated verifier generation. Keys and profiles are trusted construction
//! inputs; proof normalization is untrusted and never assigns the statement.
use std::{
  fmt,
  sync::atomic::{AtomicU64, Ordering},
};

use p3_field::TwoAdicField;

use super::ByteGadgets;
use super::ExpandedPcsWitness;
use super::FixedPcsShape;
use super::FixedVerifierInputs;
use multi_stark::batch::BatchMessage;
use multi_stark::batch::BatchProof;
use multi_stark::config::StarkGenericConfig;
use multi_stark::expr::Source;
use multi_stark::graph::Node;
use multi_stark::lookup::MAX_LOOKUP_GROUP;
use multi_stark::lookup::logup_constraint_count;
use multi_stark::lookup::stage2_width;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;
use multi_stark::plonkish::Witness;
use multi_stark::prover::Proof;
use multi_stark::system::Circuit as StarkCircuit;
use multi_stark::system::System;
use multi_stark::types::CommitmentParameters;
use multi_stark::types::GoldilocksBlake3Config as Config;
use multi_stark::types::Val;

/// A verifier-only key. No preprocessed matrices or PCS prover data are retained.
/// The caller must obtain this key from a trusted source; proof-supplied keys
/// are not authenticated merely by constructing this object.
pub struct VerifierKey {
  system: System<Config>,
}

impl VerifierKey {
  /// Consume a verifier-side System (its optional matrices may already be None).
  pub fn new(mut system: System<Config>) -> Self {
    for c in &mut system.circuits {
      c.preprocessed = None;
    }
    Self { system }
  }

  /// Copy metadata and commitments without copying any preprocessed matrices.
  pub fn from_system(system: &System<Config>) -> Self {
    let circuits = system
      .circuits
      .iter()
      .map(|c| StarkCircuit {
        graph: c.graph.clone(),
        main_width: c.main_width,
        preprocessed: None,
        preprocessed_width: c.preprocessed_width,
        preprocessed_height: c.preprocessed_height,
        num_lookups: c.num_lookups,
        stage_2_width: c.stage_2_width,
        num_publics: c.num_publics,
        lookup_group_size: c.lookup_group_size,
        constraint_count: c.constraint_count,
        max_constraint_degree: c.max_constraint_degree,
      })
      .collect();
    Self::new(System {
      config: Config::new(
        CommitmentParameters {
          log_blowup: system.config.log_blowup(),
          cap_height: system.config.cap_height(),
        },
        system.config.fri_parameters(),
      ),
      circuits,
      preprocessed_commit: system.preprocessed_commit.clone(),
      preprocessed_indices: system.preprocessed_indices.clone(),
    })
  }

  pub fn system(&self) -> &System<Config> {
    &self.system
  }
}

#[derive(serde::Serialize, Clone, Copy, Debug, PartialEq, Eq)]
pub enum Envelope {
  Ordinary,
  SingleBatch,
}

/// Log heights use active-circuit order; activation uses canonical key order.
/// Statement dimensions are fixed, but values need not be.
#[derive(serde::Serialize, Clone, Debug, PartialEq, Eq)]
pub struct ProofProfile {
  pub envelope: Envelope,
  pub active: Vec<bool>,
  pub log_degrees: Vec<u8>,
  pub claim_lengths: Vec<usize>,
  pub message_lengths: Vec<usize>,
  pub max_field_retries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifierError {
  Unsupported(&'static str),
  Profile(&'static str),
  Circuit { index: usize, field: &'static str },
  Limit { resource: &'static str, required: usize, limit: usize },
  Statement(&'static str),
  Encoding(String),
  Proof(String),
  Assignment(String),
}
impl fmt::Display for VerifierError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{self:?}")
  }
}
impl std::error::Error for VerifierError {}

/// Explicit pre-allocation limits. These bound structural work, not peak RSS.
#[derive(Clone, Copy, Debug)]
pub struct VerifierLimits {
  pub max_circuits: usize,
  pub max_graph_nodes: usize,
  pub max_queries: usize,
  pub max_field_retries: usize,
  pub max_statement_values: usize,
  pub max_proof_values: usize,
}
impl Default for VerifierLimits {
  fn default() -> Self {
    Self {
      max_circuits: 4096,
      max_graph_nodes: 10_000_000,
      max_queries: 256,
      max_field_retries: 16,
      max_statement_values: 1_000_000,
      max_proof_values: 100_000_000,
    }
  }
}

/// Exact number of external proof field values, including digest bytes and
/// auxiliary challenge coordinates, before hash hints and arithmetic gates.
/// Actual lowering costs are reported by CircuitStats and MultiStarkLayout.
#[derive(Clone, Copy, Debug)]
pub struct ResourceEstimate {
  pub proof_values: usize,
  pub statement_values: usize,
  pub graph_nodes: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct ImplementationOptions {
  pub compact_blake3: bool,
}
impl Default for ImplementationOptions {
  fn default() -> Self {
    Self { compact_blake3: true }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message<T> {
  pub args: Vec<T>,
  pub multiplicity: T,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Statement<T> {
  pub claims: Vec<Vec<T>>,
  pub messages: Vec<Message<T>>,
}

/// Wire bindings are explicitly caller-owned. The enclosing circuit must expose
/// or constrain them; unconstrained private wires prove an existential claim.
#[derive(Clone, Copy, Debug)]
pub enum StatementBinding {
  Constant(Val),
  Wire(Value),
}
#[derive(Clone, Copy, Debug)]
pub enum StatementSlot {
  Constant(Val),
  Public,
}

/// Proof data never participates in construction. For ordinary proofs the
/// statement owner supplies the claims used for transcript normalization.
pub enum ProofEnvelope<'a> {
  Ordinary { proof: &'a Proof<Config>, claims: &'a [Vec<Val>] },
  SingleBatch(&'a BatchProof<Config>),
}

pub struct VerifierPlan<'a> {
  key: &'a VerifierKey,
  profile: ProofProfile,
  shape: FixedPcsShape,
  estimate: ResourceEstimate,
  id: u64,
}

pub struct VerifierInputs {
  proof: FixedVerifierInputs,
  statement: Statement<StatementBinding>,
  plan_id: u64,
}
impl VerifierInputs {
  pub fn proof(&self) -> &FixedVerifierInputs {
    &self.proof
  }
  pub fn statement(&self) -> &Statement<StatementBinding> {
    &self.statement
  }

  /// Convenience for standalone inputs. Derived caller-owned wires must be
  /// assigned by their owner instead. Constants are checked, never overwritten.
  pub fn assign_statement(
    &self,
    witness: &mut Witness<'_, Val>,
    values: &Statement<Val>,
  ) -> Result<(), VerifierError> {
    check_statement_pair(&self.statement, values)?;
    for (&binding, &value) in
      statement_values(&self.statement).zip(statement_values(values))
    {
      match binding {
        StatementBinding::Constant(expected) if expected != value => {
          return Err(VerifierError::Statement("constant binding differs"));
        },
        StatementBinding::Constant(_) => {},
        StatementBinding::Wire(wire) => witness
          .set(wire, value)
          .map_err(|e| VerifierError::Assignment(e.to_string()))?,
      }
    }
    Ok(())
  }
}

/// Private normalized data prevents callers from mixing malformed path shapes
/// with another plan. Assignment supplies proof wires only, never statements.
pub struct PreparedProof {
  expanded: ExpandedPcsWitness,
  plan_id: u64,
}
impl PreparedProof {
  pub fn query_indices(&self) -> &[usize] {
    &self.expanded.query_indices
  }
  pub fn assign_proof(
    &self,
    witness: &mut Witness<'_, Val>,
    inputs: &VerifierInputs,
  ) -> Result<(), VerifierError> {
    if self.plan_id != inputs.plan_id {
      return Err(VerifierError::Proof("different verifier plan".into()));
    }
    self
      .expanded
      .assign_proof(witness, &inputs.proof)
      .map_err(VerifierError::Assignment)
  }
}

fn statement_values<T>(s: &Statement<T>) -> impl Iterator<Item = &T> {
  s.claims.iter().flatten().chain(
    s.messages
      .iter()
      .flat_map(|m| m.args.iter().chain(std::iter::once(&m.multiplicity))),
  )
}
fn check_statement_pair<T, U>(
  a: &Statement<T>,
  b: &Statement<U>,
) -> Result<(), VerifierError> {
  if a.claims.len() != b.claims.len()
    || a.messages.len() != b.messages.len()
    || a.claims.iter().zip(&b.claims).any(|(a, b)| a.len() != b.len())
    || a
      .messages
      .iter()
      .zip(&b.messages)
      .any(|(a, b)| a.args.len() != b.args.len())
  {
    return Err(VerifierError::Statement("statement dimensions differ"));
  }
  Ok(())
}
fn map_statement<T, U>(
  s: Statement<T>,
  mut f: impl FnMut(T) -> U,
) -> Statement<U> {
  Statement {
    claims: s
      .claims
      .into_iter()
      .map(|c| c.into_iter().map(&mut f).collect())
      .collect(),
    messages: s
      .messages
      .into_iter()
      .map(|m| Message {
        args: m.args.into_iter().map(&mut f).collect(),
        multiplicity: f(m.multiplicity),
      })
      .collect(),
  }
}
fn limit(
  resource: &'static str,
  required: usize,
  bound: usize,
) -> Result<(), VerifierError> {
  if required > bound {
    Err(VerifierError::Limit { resource, required, limit: bound })
  } else {
    Ok(())
  }
}
fn sum(
  values: impl IntoIterator<Item = usize>,
) -> Result<usize, VerifierError> {
  values.into_iter().try_fold(0usize, |a, b| {
    a.checked_add(b).ok_or(VerifierError::Profile("dimension overflow"))
  })
}

impl<'a> VerifierPlan<'a> {
  pub fn validate(
    key: &'a VerifierKey,
    profile: ProofProfile,
    limits: VerifierLimits,
  ) -> Result<Self, VerifierError> {
    let system = key.system();
    let fri = system.config.fri_parameters();
    if system.config.cap_height() != 0 {
      return Err(VerifierError::Unsupported("nonzero commitment cap"));
    }
    if fri.max_log_arity != 1 || fri.log_final_poly_len != 0 {
      return Err(VerifierError::Unsupported(
        "requires binary FRI and a constant final polynomial",
      ));
    }
    if fri.commit_proof_of_work_bits >= 64 || fri.query_proof_of_work_bits >= 64
    {
      return Err(VerifierError::Unsupported("grinding bits >= 64"));
    }
    if fri.num_queries == 0 {
      return Err(VerifierError::Profile("zero FRI queries"));
    }
    limit("queries", fri.num_queries, limits.max_queries)?;
    if profile.max_field_retries.checked_add(1).is_none() {
      return Err(VerifierError::Profile("retry budget overflow"));
    }
    limit(
      "field retries",
      profile.max_field_retries,
      limits.max_field_retries,
    )?;
    limit("circuits", system.circuits.len(), limits.max_circuits)?;
    if profile.active.len() != system.circuits.len()
      || profile.active.iter().filter(|&&a| a).count()
        != profile.log_degrees.len()
    {
      return Err(VerifierError::Profile("activation/height dimensions"));
    }
    let max_log = profile
      .log_degrees
      .iter()
      .max()
      .copied()
      .ok_or(VerifierError::Profile("no active circuits"))?;
    let lde_log = usize::from(max_log)
      .checked_add(system.config.log_blowup())
      .ok_or(VerifierError::Profile("LDE overflow"))?;
    if lde_log > Val::TWO_ADICITY || lde_log >= usize::BITS as usize {
      return Err(VerifierError::Profile("LDE exceeds field domain"));
    }
    if profile.envelope == Envelope::Ordinary
      && !profile.message_lengths.is_empty()
    {
      return Err(VerifierError::Profile(
        "ordinary proofs have no batch messages",
      ));
    }
    limit(
      "statement records",
      sum([profile.claim_lengths.len(), profile.message_lengths.len()])?,
      limits.max_statement_values,
    )?;
    let statement_values = sum(
      profile
        .claim_lengths
        .iter()
        .copied()
        .chain(profile.message_lengths.iter().copied())
        .chain([profile.message_lengths.len()]),
    )?;
    limit("statement values", statement_values, limits.max_statement_values)?;
    let graph_nodes = sum(system.circuits.iter().map(|c| c.graph.nodes.len()))?;
    limit("graph nodes", graph_nodes, limits.max_graph_nodes)?;
    if system.preprocessed_indices.len() != system.circuits.len() {
      return Err(VerifierError::Profile("preprocessing map length"));
    }
    if system.preprocessed_commit.as_ref().map(|c| c.roots().len()) != Some(1) {
      return Err(VerifierError::Unsupported(
        "requires a root-only preprocessed commitment",
      ));
    }
    let mut prep_index = 0;
    let mut logs = profile.log_degrees.iter();
    for (i, c) in system.circuits.iter().enumerate() {
      validate_circuit(c, i)?;
      let log = if profile.active[i] { logs.next().copied() } else { None };
      if c.quotient_degree() > system.config.max_quotient_degree() {
        return Err(VerifierError::Circuit {
          index: i,
          field: "quotient degree exceeds PCS",
        });
      }
      if let Some(log) = log
        && (usize::from(log) > system.config.max_log_degree()
          || usize::from(log) + c.quotient_degree().ilog2() as usize
            > system.config.max_log_quotient_domain())
      {
        return Err(VerifierError::Circuit {
          index: i,
          field: "trace/quotient domain exceeds PCS",
        });
      }
      if c.preprocessed_width > 0 {
        if log.is_none()
          || Some(c.preprocessed_height)
            != log.and_then(|l| 1usize.checked_shl(u32::from(l)))
        {
          return Err(VerifierError::Circuit {
            index: i,
            field: "preprocessing activation/height",
          });
        }
        if system.preprocessed_indices[i] != Some(prep_index) {
          return Err(VerifierError::Circuit {
            index: i,
            field: "preprocessing matrix order",
          });
        }
        prep_index += 1;
      } else if c.preprocessed_height != 0
        || system.preprocessed_indices[i].is_some()
      {
        return Err(VerifierError::Circuit {
          index: i,
          field: "unexpected preprocessing",
        });
      }
    }
    if prep_index == 0 {
      return Err(VerifierError::Unsupported("absent preprocessing"));
    }
    let mut shape = FixedPcsShape::from_profile(
      system,
      &profile.active,
      &profile.log_degrees,
    );
    shape.max_field_retries = profile.max_field_retries;
    // Calculate external wire counts with checked arithmetic before allocating a circuit.
    let widths = sum(shape.widths.iter().flatten().copied())?;
    let ood = sum(shape.widths.iter().enumerate().flat_map(|(batch, ws)| {
      ws.iter().map(move |&w| w.saturating_mul(if batch == 2 { 2 } else { 4 }))
    }))?;
    let rounds = usize::from(max_log);
    let path_bytes = sum(
      shape
        .heights
        .iter()
        .map(|h| h.iter().max().copied().unwrap_or(0))
        .chain((0..rounds).map(|r| lde_log - r - 1)),
    )?
    .checked_mul(32)
    .ok_or(VerifierError::Profile("path overflow"))?;
    let per_query = sum([widths, path_bytes, rounds * 2])?;
    let proof_values = sum([
      8,
      96,
      ood,
      shape.log_degrees.len().saturating_mul(2),
      rounds * 33,
      3,
      per_query
        .checked_mul(fri.num_queries)
        .ok_or(VerifierError::Profile("query overflow"))?,
    ])?;
    limit("proof values", proof_values, limits.max_proof_values)?;
    static NEXT_PLAN: AtomicU64 = AtomicU64::new(1);
    Ok(Self {
      key,
      profile,
      shape,
      estimate: ResourceEstimate {
        proof_values,
        statement_values,
        graph_nodes,
      },
      id: NEXT_PLAN.fetch_add(1, Ordering::Relaxed),
    })
  }
  /// Protocol identity including key, shape and constant statement bindings.
  /// Public values are intentionally absent so one circuit can be reused.
  pub fn identity(
    &self,
    schema: &Statement<StatementSlot>,
  ) -> Result<[u8; 32], VerifierError> {
    use p3_field::PrimeField64;
    use p3_symmetric::CryptographicHasher;
    self.check_statement(schema)?;
    let constants: Vec<_> = statement_values(schema)
      .map(|s| match s {
        StatementSlot::Constant(v) => Some(v.as_canonical_u64()),
        StatementSlot::Public => None,
      })
      .collect();
    let encoded = bincode::serde::encode_to_vec(
      (
        "multi-stark/verifier-plan/v1",
        self.key.fingerprint()?,
        &self.profile,
        constants,
      ),
      bincode::config::standard(),
    )
    .map_err(|e| VerifierError::Encoding(e.to_string()))?;
    Ok(p3_blake3::Blake3.hash_iter(encoded))
  }

  /// Cache identity additionally binds compiler and lowering provenance and
  /// layout options. Callers must supply their actual version/options strings.
  pub fn build_identity(
    &self,
    schema: &Statement<StatementSlot>,
    options: ImplementationOptions,
    compiler: &str,
    lowering_version: &str,
    layout_options: &str,
  ) -> Result<[u8; 32], VerifierError> {
    use p3_symmetric::CryptographicHasher;
    let encoded = bincode::serde::encode_to_vec(
      (
        self.identity(schema)?,
        "plonkish-gadgets/v1",
        env!("CARGO_PKG_VERSION"),
        options.compact_blake3,
        compiler,
        lowering_version,
        layout_options,
      ),
      bincode::config::standard(),
    )
    .map_err(|e| VerifierError::Encoding(e.to_string()))?;
    Ok(p3_blake3::Blake3.hash_iter(encoded))
  }

  pub fn profile(&self) -> &ProofProfile {
    &self.profile
  }
  pub fn shape(&self) -> &FixedPcsShape {
    &self.shape
  }
  pub fn resources(&self) -> ResourceEstimate {
    self.estimate
  }

  fn check_statement<T>(&self, s: &Statement<T>) -> Result<(), VerifierError> {
    if s
      .claims
      .iter()
      .map(Vec::len)
      .ne(self.profile.claim_lengths.iter().copied())
      || s
        .messages
        .iter()
        .map(|m| m.args.len())
        .ne(self.profile.message_lengths.iter().copied())
    {
      return Err(VerifierError::Statement("statement does not match profile"));
    }
    Ok(())
  }

  /// Compose a complete verifier with explicitly caller-owned bindings.
  pub fn constrain(
    &self,
    b: &mut CircuitBuilder<Val>,
    statement: Statement<StatementBinding>,
    options: ImplementationOptions,
  ) -> Result<VerifierInputs, VerifierError> {
    self.check_statement(&statement)?;
    if options.compact_blake3 {
      b.enable_compact_blake3();
    } else if b.compact_blake3_enabled() {
      return Err(VerifierError::Unsupported(
        "builder already uses compact hashes",
      ));
    }
    let wires = map_statement(statement.clone(), |v| match v {
      StatementBinding::Constant(c) => b.constant(c),
      StatementBinding::Wire(w) => w,
    });
    let bytes = ByteGadgets::new(b);
    let proof = match self.profile.envelope {
      Envelope::Ordinary => super::constrain_fixed_verifier(
        b,
        &bytes,
        self.key.system(),
        &self.shape,
        wires.claims,
      ),
      Envelope::SingleBatch => super::batch::constrain_bound_batch_verifier(
        b,
        &bytes,
        self.key.system(),
        &self.shape,
        wires.claims,
        &wires.messages,
      ),
    };
    Ok(VerifierInputs { proof, statement, plan_id: self.id })
  }

  /// Standalone public order: claims in order, then each message's arguments
  /// followed by its multiplicity. Constant slots are omitted from publics.
  pub fn build(
    &self,
    schema: Statement<StatementSlot>,
    options: ImplementationOptions,
  ) -> Result<(Circuit<Val>, VerifierInputs), VerifierError> {
    self.check_statement(&schema)?;
    let mut b = CircuitBuilder::new();
    let mut index = 0;
    let bindings = map_statement(schema, |s| match s {
      StatementSlot::Constant(c) => StatementBinding::Constant(c),
      StatementSlot::Public => {
        let w = b.public_input(format!("statement[{index}]"));
        index += 1;
        StatementBinding::Wire(w)
      },
    });
    let inputs = self.constrain(&mut b, bindings, options)?;
    Ok((b.finish(), inputs))
  }

  pub fn expand_witness(
    &self,
    proof: ProofEnvelope<'_>,
  ) -> Result<PreparedProof, VerifierError> {
    let expanded = match (self.profile.envelope, proof) {
      (Envelope::Ordinary, ProofEnvelope::Ordinary { proof, claims }) => {
        if claims
          .iter()
          .map(Vec::len)
          .ne(self.profile.claim_lengths.iter().copied())
        {
          return Err(VerifierError::Statement("claim dimensions"));
        }
        super::expand_pcs_witness(
          self.key.system(),
          &self.shape,
          proof,
          &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        )
      },
      (Envelope::SingleBatch, ProofEnvelope::SingleBatch(batch)) => {
        if batch.preamble.headers.len() != 1 || batch.proofs.len() != 1 {
          return Err(VerifierError::Proof(
            "expected exactly one shard".into(),
          ));
        }
        let statement = Statement {
          claims: batch.preamble.headers[0].claims.clone(),
          messages: batch
            .preamble
            .messages
            .iter()
            .map(|m| Message {
              args: m.args.clone(),
              multiplicity: m.multiplicity,
            })
            .collect(),
        };
        self.check_statement(&statement)?;
        let messages: Vec<_> = statement
          .messages
          .into_iter()
          .map(|m| BatchMessage { args: m.args, multiplicity: m.multiplicity })
          .collect();
        super::expand_single_batch_witness(
          self.key.system(),
          &self.shape,
          batch,
          &messages,
        )
      },
      _ => return Err(VerifierError::Proof("wrong proof envelope".into())),
    }
    .map_err(VerifierError::Proof)?;
    Ok(PreparedProof { expanded, plan_id: self.id })
  }

  /// Count frontend operations without retaining their constraints or recipes.
  /// This is not an estimate of foreign-field or R1CS expansion.
  pub fn estimate(
    &self,
    schema: Statement<StatementSlot>,
    options: ImplementationOptions,
  ) -> Result<multi_stark::plonkish::CircuitStats, VerifierError> {
    self.check_statement(&schema)?;
    let mut b = CircuitBuilder::counting();
    let mut index = 0;
    let bindings = map_statement(schema, |s| match s {
      StatementSlot::Constant(c) => StatementBinding::Constant(c),
      StatementSlot::Public => {
        let w = b.public_input(format!("statement[{index}]"));
        index += 1;
        StatementBinding::Wire(w)
      },
    });
    self.constrain(&mut b, bindings, options)?;
    Ok(b.stats())
  }
}

pub(super) fn validate_circuit(
  c: &StarkCircuit<Val>,
  index: usize,
) -> Result<(), VerifierError> {
  let err = |field| VerifierError::Circuit { index, field };
  if !(1..=MAX_LOOKUP_GROUP).contains(&c.lookup_group_size) {
    return Err(err("lookup group size"));
  }
  if c.num_lookups != c.graph.lookups.len()
    || c.stage_2_width != stage2_width(c.num_lookups, c.lookup_group_size, 2)
    || c.num_publics != 8
  {
    return Err(err("lookup/public widths"));
  }
  let g = &c.graph;
  if g.nodes.len() != g.degrees.len() || g.lookup_prefix_len > g.nodes.len() {
    return Err(err("graph dimensions"));
  }
  for (i, n) in g.nodes.iter().enumerate() {
    let degree = |id: multi_stark::graph::NodeId| {
      g.degrees
        .get(id.index())
        .filter(|_| id.index() < i)
        .copied()
        .ok_or_else(|| err("graph topology"))
    };
    let d = match *n {
      Node::Const(_) | Node::IsTransition => 0,
      Node::Public(p) => {
        if p as usize >= c.num_publics {
          return Err(err("public index"));
        }
        0
      },
      Node::IsFirstRow | Node::IsLastRow => 1,
      Node::Var(col) => {
        let width = match col.source {
          Source::Main => c.main_width,
          Source::Stage2 => c.stage_2_width,
          Source::Preprocessed => c.preprocessed_width,
        };
        if col.index as usize >= width {
          return Err(err("column index"));
        }
        1
      },
      Node::Add(a, b) | Node::Sub(a, b) => degree(a)?.max(degree(b)?),
      Node::Mul(a, b) => degree(a)?
        .checked_add(degree(b)?)
        .ok_or_else(|| err("degree overflow"))?,
      Node::Neg(a) => degree(a)?,
    };
    if g.degrees[i] != d {
      return Err(err("node degree"));
    }
  }
  if g.zeros.iter().any(|n| n.index() >= g.nodes.len())
    || g.lookups.iter().any(|l| {
      l.args
        .iter()
        .chain(std::iter::once(&l.multiplicity))
        .any(|n| n.index() >= g.lookup_prefix_len)
    })
  {
    return Err(err("graph roots"));
  }
  let mut lookup_degree = 1u64;
  for group in g.lookups.chunks(c.lookup_group_size) {
    let degrees: Vec<_> = group
      .iter()
      .map(|l| {
        l.args
          .iter()
          .map(|n| u64::from(g.degrees[n.index()]))
          .max()
          .unwrap_or(0)
      })
      .collect();
    let sum: u64 = degrees.iter().sum();
    lookup_degree = lookup_degree.max(sum + 1);
    for (l, &degree) in group.iter().zip(&degrees) {
      lookup_degree = lookup_degree
        .max(u64::from(g.degrees[l.multiplicity.index()]) + sum - degree);
    }
  }
  let lookup_degree = u32::try_from(lookup_degree)
    .map_err(|_overflow| err("lookup degree overflow"))?;
  let max = g.zeros.iter().map(|n| g.degrees[n.index()]).max().unwrap_or(0);
  if g.max_constraint_degree != max
    || c.max_constraint_degree != max.max(lookup_degree) as usize
    || c.constraint_count
      != g.zeros.len()
        + logup_constraint_count(c.num_lookups, c.lookup_group_size, 2)
  {
    return Err(err("constraint metadata"));
  }
  Ok(())
}
