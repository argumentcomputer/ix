//! Packed-SHPLONK proving of the packed CompressGL stage and of the packed
//! chain entry.
//!
//! A stage that verifies a packed proof folds with a weight squeezed from that
//! verifier's final transcript ([`fold_packed`]). The chain policy
//! ([`PackedPolicy`], `IXAUKG01`) authorizes the packed CompressGL key
//! ([`PackedGlProver`]) at stage one and one later key: on the L3 pipeline the
//! fixed-key narrow stage's ([`PACKED_NARROW_FIXED_ENTRY`]).
//! [`PackedProver`] proves [`PACKED_CHAIN_ENTRY`] artifacts, whose Lean source
//! is no longer exported; it remains for existing CompressGL chain drivers.

use super::*;
use crate::{
  aiur_backend::{
    compress_gl as gl,
    kzg::{check_shape, circuit_inputs_with_budget},
    kzg_packed_advice as packed_wire, wide,
  },
  kzg::{VerifierParams, packed_shplonk::PackedShplonkConfig},
  pipeline::SetupConfig,
};
use multi_stark::traits::TwoAdicField;
use multi_stark::{
  expr::Source,
  lookup::LookupValues,
  system::{CircuitInputs, ProverKey, System, SystemWitness},
};
use p3_matrix::{Matrix, dense::RowMajorMatrix};

pub const PACKED_CHAIN_ENTRY: &str = "CompressBNPacked::chain_v1";
/// Stage one of a packed chain, verifying the CompressGL proof under the
/// CompressGL key fixed in the program's tables (`CompressNarrowFixed`). Its
/// public call is the policy digest, stage and statement.
pub const PACKED_NARROW_FIXED_ENTRY: &str = "CompressNarrowFixed::step_v1";
pub const PACKED_CHAIN_POLICY_MAGIC: &[u8; 8] = b"IXAUKG01";
const PACKED_SETUP_SEED: &[u8] = b"compress-bn-packed-shplonk-v1";

pub type PackedProof = packed_wire::Proof;

/// Authorized predecessor keys of a packed chain (`IXAUKG01`): the packed
/// CompressGL key for stage one and one key for every later stage.
pub struct PackedPolicy {
  anchors: [u8; 128],
  gl: ([u8; 32], u32),
  bn: ([u8; 32], u32),
}

impl PackedPolicy {
  pub fn chain(
    parameters: &VerifierParams,
    gl: ([u8; 32], u32),
    bn: ([u8; 32], u32),
  ) -> Result<Self, String> {
    let column = wire::Policy::new(parameters, gl.0, gl.1, bn.0, bn.1)?;
    Ok(Self { anchors: *column.anchor_bytes(), gl, bn })
  }

  /// Parse a two-key chain policy, checking its anchors against
  /// `parameters`: the canonical encoding round-trips exactly.
  pub fn from_chain_bytes(
    parameters: &VerifierParams,
    bytes: &[u8],
  ) -> Result<Self, String> {
    let fields = bytes
      .strip_prefix(PACKED_CHAIN_POLICY_MAGIC.as_slice())
      .filter(|rest| rest.len() == 128 + 2 * (32 + 4))
      .ok_or("not a canonical IXAUKG01 chain policy")?;
    let key = |offset: usize| -> ([u8; 32], u32) {
      let digest = fields[offset..offset + 32].try_into().unwrap_or([0; 32]);
      let entry = u32::from_le_bytes(
        fields[offset + 32..offset + 36].try_into().unwrap_or([0; 4]),
      );
      (digest, entry)
    };
    let policy = Self::chain(parameters, key(128), key(128 + 36))?;
    if policy.to_bytes() != bytes {
      return Err("chain policy anchors differ from the parameters".into());
    }
    Ok(policy)
  }

  pub fn anchor_bytes(&self) -> &[u8; 128] {
    &self.anchors
  }

  /// The stage-one (CompressGL) key digest and physical entry.
  pub const fn gl(&self) -> ([u8; 32], u32) {
    self.gl
  }

  /// The steady-state key digest and physical entry.
  pub const fn bn(&self) -> ([u8; 32], u32) {
    self.bn
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = PACKED_CHAIN_POLICY_MAGIC.to_vec();
    bytes.extend(self.anchors);
    for (digest, entry) in [&self.gl, &self.bn] {
      bytes.extend(digest);
      bytes.extend(entry.to_le_bytes());
    }
    bytes
  }

  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }
}

/// Public parameters of a packed CompressBN key. Every field is part of the
/// verifying key: the pack capacity bounds both trace heights and
/// `width·height` per pack, and the lookup budget fixes each circuit's lookup
/// grouping.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct PackedCapacity {
  pub log_cap: u8,
  pub quotient_degree: usize,
  /// See [`crate::aiur_backend::kzg::circuit_inputs_with_budget`]; `None`
  /// keeps every circuit's quotient degree at its group-size-one value.
  pub lookup_quotient_budget: Option<usize>,
}

impl PackedCapacity {
  pub fn cap(self) -> Result<usize, String> {
    if self.log_cap < 1
      || usize::from(self.log_cap) > <Scalar as TwoAdicField>::TWO_ADICITY
      || !self.quotient_degree.is_power_of_two()
      || self.lookup_quotient_budget.is_some_and(|b| !b.is_power_of_two())
    {
      return Err("invalid packed BN254 capacity".into());
    }
    Ok(1usize << self.log_cap)
  }

  /// Load `2^log_cap` proving powers through the release setup loader.
  /// Ignition prefixes are checked against the released anchors there.
  pub fn config(
    self,
    setup: &SetupConfig,
  ) -> Result<PackedShplonkConfig, String> {
    let cap = self.cap()?;
    let source =
      setup.for_stage::<crate::kzg::Bn254>(PACKED_SETUP_SEED, cap).map_err(|e| e.to_string())?;
    let srs = source.srs(cap, false).map_err(|e| e.to_string())?;
    Ok(PackedShplonkConfig::with_max_trace_len(
      Arc::new(srs),
      cap,
      self.quotient_degree,
    ))
  }
}

pub struct PackedProven {
  pub proof: PackedProof,
  /// Padded main cells of the committed traces, after sharding.
  pub main_cells: usize,
  /// `(compiler circuit, shard heights)` of every circuit with several copies.
  pub shards: Vec<(usize, Vec<usize>)>,
  /// Source-wire bytes read by the packed Aiur verifier.
  pub source_proof: Vec<u8>,
  pub source_claims: Vec<u8>,
  pub claim: Vec<Scalar>,
  pub public: PublicInputs,
  pub accumulator: Accumulator,
  pub profile: Profile,
  pub trace_seconds: f64,
  pub proving_seconds: f64,
  pub verification_seconds: f64,
}

/// The packed system of one [`PACKED_CHAIN_ENTRY`] [`Wrapper`] with its key,
/// transcript-bound to the digest of its unbound source-wire key as the
/// per-column backend binds its own.
pub struct PackedProver<'w> {
  wrapper: &'w Wrapper,
  capacity: PackedCapacity,
  copies: Vec<usize>,
  system: System<PackedShplonkConfig>,
  key: ProverKey<PackedShplonkConfig>,
  key_bytes: Vec<u8>,
}

impl<'w> PackedProver<'w> {
  pub fn new(
    wrapper: &'w Wrapper,
    capacity: PackedCapacity,
    config: PackedShplonkConfig,
  ) -> Result<Self, String> {
    Self::with_copies(wrapper, capacity, config, None)
  }

  /// `copies[i]` system circuits for compiler circuit `i` (one if `None`).
  /// Only function circuits may have several copies: their constraints and
  /// lookups are row-local, so rows split across copies, each zero-padded,
  /// satisfy the same constraints and LogUp balance as one trace. ROM and
  /// fixed-table circuits constrain consecutive rows or a fixed height.
  pub fn with_copies(
    wrapper: &'w Wrapper,
    capacity: PackedCapacity,
    config: PackedShplonkConfig,
    copies: Option<Vec<usize>>,
  ) -> Result<Self, String> {
    if wrapper.entry_name != PACKED_CHAIN_ENTRY {
      return Err("packed proving needs the packed chain entry".into());
    }
    let PackedSystem { system, key, key_bytes, copies } =
      PackedSystem::new(wrapper.plan(), capacity, config, copies)?;
    Ok(Self { wrapper, capacity, copies, system, key, key_bytes })
  }

  /// Source-wire key bytes; the policy pins their BLAKE3 digest.
  pub fn key_bytes(&self) -> &[u8] {
    &self.key_bytes
  }

  pub fn key_digest(&self) -> [u8; 32] {
    *blake3::hash(&self.key_bytes).as_bytes()
  }

  pub fn parameters(&self) -> &VerifierParams {
    self.system.config.pcs().parameters()
  }

  pub fn system(&self) -> &System<PackedShplonkConfig> {
    &self.system
  }

  pub fn copies(&self) -> &[usize] {
    &self.copies
  }

  pub const fn entry(&self) -> u32 {
    self.wrapper.entry
  }

  /// The two-key policy authorizing the packed CompressGL key `gl` for stage
  /// one and this chain program's key for every later stage.
  pub fn chain_policy(
    &self,
    gl: &PackedGlProver<'_>,
  ) -> Result<PackedPolicy, String> {
    if source_anchors(gl.key_bytes())? != source_anchors(&self.key_bytes)? {
      return Err("packed programs use different setups".into());
    }
    PackedPolicy::chain(
      self.parameters(),
      (gl.key_digest(), gl.entry()?),
      (self.key_digest(), self.entry()),
    )
  }

  pub fn profile(&self, execution: &Executed<'_>) -> Result<Profile, String> {
    self
      .wrapper
      .profile_with_budget(execution, self.capacity.lookup_quotient_budget)
  }

  pub fn prove(
    &self,
    execution: &Executed<'_>,
    limits: TraceLimits,
  ) -> Result<PackedProven, String> {
    let wrapper = self.wrapper;
    let profile = self.profile(execution)?;
    limits
      .check_streaming(&profile, self.system.config.uses_streaming_lookups())?;
    if profile.max_height > self.capacity.cap()?
      || profile.quotient_degree > self.capacity.quotient_degree
    {
      return Err(format!(
        "CompressBN trace exceeds the packed capacity: height {} / {}, quotient degree {} / {}",
        profile.max_height,
        self.capacity.cap()?,
        profile.quotient_degree,
        self.capacity.quotient_degree,
      ));
    }
    let input = execution.input;
    let policy = &input.policy;
    let gl = (policy.gl.digest, policy.gl.entry);
    let bn = (policy.bn.digest, policy.bn.entry);
    if !policy.gl_packed {
      return Err("chain proving needs a packed CompressGL policy".into());
    }
    let configured = PackedPolicy::chain(self.parameters(), gl, bn)?;
    let own = &policy.bn;
    if configured.digest() != *input.public.policy.as_bytes()
      || self.key_digest() != own.digest
      || wrapper.entry != own.entry
      || source_anchors(&self.key_bytes)? != policy.anchors
    {
      return Err(
        "packed CompressBN proving key differs from the trusted policy".into(),
      );
    }
    let args = input.public.arguments();
    let claim = wrapper.claim(input.public, &execution.accumulator)?;
    let proven = prove_packed(
      &self.system,
      &self.key,
      &Compiler::with_lookup_budget(
        &wrapper.plan,
        self.capacity.lookup_quotient_budget,
      )?,
      None,
      &self.copies,
      &execution.record,
      wrapper.entry_name,
      &args,
      &claim,
    )?;
    Ok(PackedProven {
      main_cells: proven.main_cells,
      shards: proven.shards,
      source_proof: packed_wire::proof_bytes(&proven.proof)?,
      source_claims: wire::claims_bytes(std::slice::from_ref(&claim))?,
      proof: proven.proof,
      claim,
      public: input.public,
      accumulator: execution.accumulator.clone(),
      profile,
      trace_seconds: proven.trace_seconds,
      proving_seconds: proven.proving_seconds,
      verification_seconds: proven.verification_seconds,
    })
  }

  /// Native verification against an independently expected public claim.
  pub fn verify(
    &self,
    claim: &[Scalar],
    proof: &PackedProof,
  ) -> Result<(), String> {
    verify_packed(&self.system, claim, proof)
  }
}

/// A packed system with its prover key and source-wire key bytes, after
/// expanding circuit copies.
struct PackedSystem {
  system: System<PackedShplonkConfig>,
  key: ProverKey<PackedShplonkConfig>,
  key_bytes: Vec<u8>,
  copies: Vec<usize>,
}

impl PackedSystem {
  /// The packed system of a compiler plan, transcript-bound to the digest of
  /// its unbound source-wire key. Every circuit's quotient degree and fixed
  /// table must fit `capacity`.
  fn new(
    plan: &TracePlan<'static, Bn254>,
    capacity: PackedCapacity,
    config: PackedShplonkConfig,
    copies: Option<Vec<usize>>,
  ) -> Result<Self, String> {
    let inputs =
      circuit_inputs_with_budget(plan, capacity.lookup_quotient_budget)?;
    let functions =
      Compiler::with_lookup_budget(plan, capacity.lookup_quotient_budget)?
        .function_circuits();
    Self::from_inputs(inputs, functions, capacity, config, copies)
  }

  /// [`Self::new`] over given circuits, the first `functions` of them
  /// function circuits.
  fn from_inputs(
    inputs: Vec<CircuitInputs<Scalar>>,
    functions: usize,
    capacity: PackedCapacity,
    config: PackedShplonkConfig,
    copies: Option<Vec<usize>>,
  ) -> Result<Self, String> {
    if config.pcs().parameters().max_trace_len() != capacity.cap()?
      || config.max_quotient_degree() != capacity.quotient_degree
    {
      return Err("packed configuration differs from its capacity".into());
    }
    let params = extension_params::<PackedShplonkConfig>();
    for input in &inputs {
      let graph = input
        .compile_graph(&params)
        .map_err(|error| format!("invalid compiler circuit: {error:?}"))?;
      let degree = graph
        .max_constraint_degree
        .max(logup_max_degree(&graph, input.lookup_group_size))
        as usize;
      let quotient = (degree.max(2) - 1)
        .checked_next_power_of_two()
        .ok_or("quotient degree overflow")?;
      if quotient > capacity.quotient_degree {
        return Err(format!(
          "circuit quotient degree {quotient} exceeds the packed capacity {}",
          capacity.quotient_degree
        ));
      }
      if let Some(fixed) = &input.preprocessed {
        let height = fixed.values.len() / fixed.width;
        if height > capacity.cap()? {
          return Err("fixed table exceeds the packed capacity".into());
        }
      }
    }
    let copies = copies.unwrap_or_else(|| vec![1; inputs.len()]);
    if copies.len() != inputs.len()
      || copies.contains(&0)
      || copies.iter().enumerate().any(|(i, &k)| k > 1 && i >= functions)
    {
      return Err("packed copies must cover every circuit, and only function circuits may have several".into());
    }
    let inputs: Vec<_> = inputs
      .into_iter()
      .zip(&copies)
      .flat_map(|(input, &k)| std::iter::repeat_n(input, k))
      .collect();
    let (mut system, key) = System::new(config, inputs);
    let unbound = packed_wire::key_bytes_with_copies(&system, &copies)?;
    system.config =
      system.config.clone().with_key_digest(*blake3::hash(&unbound).as_bytes());
    let key_bytes = packed_wire::key_bytes_with_copies(&system, &copies)?;
    Ok(Self { system, key, key_bytes, copies })
  }
}

struct ProvenTraces {
  proof: PackedProof,
  main_cells: usize,
  shards: Vec<(usize, Vec<usize>)>,
  trace_seconds: f64,
  proving_seconds: f64,
  verification_seconds: f64,
}

/// Populate, shard and prove the traces of one execution, then verify the
/// proof natively against `claim`.
#[allow(clippy::too_many_arguments)]
fn prove_packed(
  system: &System<PackedShplonkConfig>,
  key: &ProverKey<PackedShplonkConfig>,
  compiler: &Compiler<'_, 'static>,
  stage: Option<&wide::Stage>,
  copies: &[usize],
  record: &Execution<Bn254>,
  entry: &str,
  args: &[Scalar],
  claim: &[Scalar],
) -> Result<ProvenTraces, String> {
  let started = Instant::now();
  let traces = compiler.generate(record, entry, args)?;
  let traces = match stage {
    Some(stage) => stage.traces(traces)?,
    None => traces,
  };
  let (traces, shards) = if copies.iter().all(|&k| k == 1) {
    (traces, vec![])
  } else {
    let raw = compiler.raw_row_counts(record)?;
    let raw = match stage {
      Some(stage) => stage.rows(&raw),
      None => raw,
    };
    shard(traces, copies, &raw)?
  };
  let main_cells = traces.iter().map(|t| t.height() * t.width()).sum();
  let lookups = if system.config.uses_streaming_lookups() {
    // The prover rebuilds lookup tuples from committed columns.
    traces
      .iter()
      .zip(&system.circuits)
      .map(|(trace, circuit)| {
        let widths: Vec<_> =
          circuit.graph.lookups.iter().map(|l| l.args.len()).collect();
        LookupValues::shape_only(trace.height(), &widths)
      })
      .collect()
  } else {
    SystemWitness::from_stage_1(traces.clone(), system).lookups
  };
  let witness = SystemWitness { traces, lookups };
  let (active, degrees) = trace_shape(&witness)?;
  check_shape(system, &active, &degrees)?;
  let trace_seconds = started.elapsed().as_secs_f64();
  system.config.set_main_next_rows(
    (0..active.len())
      .filter(|&circuit| active[circuit])
      .map(|circuit| system.opens_next_row(circuit, Source::Main))
      .collect(),
  );
  let started = Instant::now();
  let proof = system.prove(key, claim, witness);
  let proving_seconds = started.elapsed().as_secs_f64();
  let started = Instant::now();
  verify_packed(system, claim, &proof)?;
  Ok(ProvenTraces {
    proof,
    main_cells,
    shards,
    trace_seconds,
    proving_seconds,
    verification_seconds: started.elapsed().as_secs_f64(),
  })
}

fn verify_packed(
  system: &System<PackedShplonkConfig>,
  claim: &[Scalar],
  proof: &PackedProof,
) -> Result<(), String> {
  check_shape(system, &proof.active, &proof.log_degrees)?;
  system
    .verify(claim, proof)
    .map_err(|error| format!("packed verification failed: {error:?}"))
}

/// Native reference for `CompressBNPacked::fold` at the stage `public`, whose
/// predecessor proof `proof` of `system` (key digest `key_digest`) carries
/// `previous`. Verifies the proof, squeezes the weight from the verifier's
/// final transcript and returns it with `pair + weight·previous`, where
/// `pair` is the proof's deferred opening pair.
pub fn fold_packed(
  system: &System<PackedShplonkConfig>,
  claim: &[Scalar],
  proof: &PackedProof,
  public: PublicInputs,
  key_digest: &[u8; 32],
  previous: &Accumulator,
) -> Result<(Scalar, Accumulator), String> {
  use ark_ec::CurveGroup;
  let verified = crate::kzg::packed_shplonk::capture_verification(|| {
    verify_packed(system, claim, proof)
  })?;
  let previous = previous.points();
  let weight = wire::transcript_fold_challenge(
    &verified.transcript.0,
    public.policy.as_bytes(),
    public.statement.as_bytes(),
    public.stage.get(),
    key_digest,
    &previous,
    &verified.pair,
  )?;
  let folded =
    [0, 1].map(|i| (verified.pair[i] + previous[i] * weight.0).into_affine());
  Ok((weight, Accumulator::from_points(&folded)?))
}

/// A packed-SHPLONK prover of the CompressGL program, whose key the chain
/// policy authorizes for stage one of [`PACKED_CHAIN_ENTRY`]. Its public call
/// is CompressGL's own 18-word call.
pub struct PackedGlProver<'w> {
  wrapper: &'w gl::Wrapper,
  capacity: PackedCapacity,
  stage: Option<wide::Stage>,
  copies: Vec<usize>,
  system: System<PackedShplonkConfig>,
  key: ProverKey<PackedShplonkConfig>,
  key_bytes: Vec<u8>,
}

pub struct PackedGlProven {
  pub proof: PackedProof,
  /// Padded main cells of the committed traces, after sharding.
  pub main_cells: usize,
  pub shards: Vec<(usize, Vec<usize>)>,
  pub source_proof: Vec<u8>,
  pub source_claims: Vec<u8>,
  pub claim: Vec<Scalar>,
  pub trace_seconds: f64,
  pub proving_seconds: f64,
  pub verification_seconds: f64,
}

impl<'w> PackedGlProver<'w> {
  /// See [`PackedProver::with_copies`] for `copies`.
  pub fn with_copies(
    wrapper: &'w gl::Wrapper,
    capacity: PackedCapacity,
    config: PackedShplonkConfig,
    copies: Option<Vec<usize>>,
  ) -> Result<Self, String> {
    let PackedSystem { system, key, key_bytes, copies } =
      PackedSystem::new(wrapper.plan(), capacity, config, copies)?;
    Ok(Self { wrapper, capacity, stage: None, copies, system, key, key_bytes })
  }

  /// The prover of the circuits exported by `wide_export` ([`wide::Stage`],
  /// in its table order), filled from the compiler's witness traces.
  /// `copies` index the stage's tables.
  pub fn from_wide(
    wrapper: &'w gl::Wrapper,
    capacity: PackedCapacity,
    config: PackedShplonkConfig,
    stage: wide::Stage,
    copies: Option<Vec<usize>>,
  ) -> Result<Self, String> {
    let PackedSystem { system, key, key_bytes, copies } =
      PackedSystem::from_inputs(
        stage.inputs.clone(),
        stage.function_circuits,
        capacity,
        config,
        copies,
      )?;
    Ok(Self {
      wrapper,
      capacity,
      stage: Some(stage),
      copies,
      system,
      key,
      key_bytes,
    })
  }

  pub fn key_bytes(&self) -> &[u8] {
    &self.key_bytes
  }

  pub fn key_digest(&self) -> [u8; 32] {
    *blake3::hash(&self.key_bytes).as_bytes()
  }

  pub fn parameters(&self) -> &VerifierParams {
    self.system.config.pcs().parameters()
  }

  pub fn system(&self) -> &System<PackedShplonkConfig> {
    &self.system
  }

  pub fn copies(&self) -> &[usize] {
    &self.copies
  }

  pub fn stage(&self) -> Option<&wide::Stage> {
    self.stage.as_ref()
  }

  /// Physical entry ID of `CompressGL::verify_root`, as its claim names it.
  pub fn entry(&self) -> Result<u32, String> {
    let claim =
      self.wrapper.plan().public_claim(gl::ENTRY, &[Bn254.zero(); 16], &[])?;
    u32::try_from(Bn254.try_to_u64(claim[1])?)
      .map_err(|_error| "CompressGL callable exceeds u32".into())
  }

  pub fn compiler(&self) -> Result<Compiler<'_, 'static>, String> {
    Compiler::with_lookup_budget(
      self.wrapper.plan(),
      self.capacity.lookup_quotient_budget,
    )
  }

  pub fn prove(
    &self,
    execution: &gl::Executed<'_>,
  ) -> Result<PackedGlProven, String> {
    let compiler = self.compiler()?;
    let heights = compiler.row_counts(execution.record())?;
    if heights.iter().any(|&h| h > self.capacity.cap().unwrap_or(0)) {
      return Err("CompressGL trace exceeds the packed capacity".into());
    }
    if let Some(stage) = &self.stage {
      stage.check_rom(&compiler.raw_row_counts(execution.record())?)?;
    }
    let claim = self.wrapper.claim(execution.input().statement())?;
    let proven = prove_packed(
      &self.system,
      &self.key,
      &compiler,
      self.stage.as_ref(),
      &self.copies,
      execution.record(),
      gl::ENTRY,
      execution.args(),
      &claim,
    )?;
    Ok(PackedGlProven {
      main_cells: proven.main_cells,
      shards: proven.shards,
      source_proof: packed_wire::proof_bytes(&proven.proof)?,
      source_claims: wire::claims_bytes(std::slice::from_ref(&claim))?,
      proof: proven.proof,
      claim,
      trace_seconds: proven.trace_seconds,
      proving_seconds: proven.proving_seconds,
      verification_seconds: proven.verification_seconds,
    })
  }

  pub fn verify(
    &self,
    claim: &[Scalar],
    proof: &PackedProof,
  ) -> Result<(), String> {
    verify_packed(&self.system, claim, proof)
  }
}

/// At most `pieces` powers of two, largest first, covering `rows`: the
/// leading bits of `rows`, the remainder rounded up to a power of two.
pub fn decompose(rows: usize, pieces: usize) -> Vec<usize> {
  let mut heights = vec![];
  let mut left = rows;
  while left != 0 {
    if heights.len() + 1 == pieces || left.is_power_of_two() {
      heights.push(left.next_power_of_two());
      break;
    }
    let top = 1 << left.ilog2();
    heights.push(top);
    left -= top;
  }
  heights
}

/// Copy counts from a reference execution's raw rows per compiler circuit.
/// A function circuit gets `k ≤ max_copies` copies when splitting its rows
/// greedily into `k` powers of two saves at least `min_saving` padded main
/// cells net of the next stage's cost for every extra active copy:
/// `column_cost` per committed column (opened, hashed and folded) and
/// `node_cost` per constraint-graph node (evaluated once per copy).
pub fn plan_copies(
  compiler: &Compiler<'_, '_>,
  raw_rows: &[usize],
  max_copies: usize,
  min_saving: usize,
  column_cost: usize,
  node_cost: usize,
) -> Vec<usize> {
  plan_copies_of(
    compiler.inputs(),
    compiler.function_circuits(),
    raw_rows,
    max_copies,
    min_saving,
    column_cost,
    node_cost,
  )
}

/// [`plan_copies`] over given circuits, the first `functions` of them
/// function circuits, with `raw_rows` in their order.
pub fn plan_copies_of(
  inputs: &[CircuitInputs<Scalar>],
  functions: usize,
  raw_rows: &[usize],
  max_copies: usize,
  min_saving: usize,
  column_cost: usize,
  node_cost: usize,
) -> Vec<usize> {
  let params = extension_params::<PackedShplonkConfig>();
  let degree = params.degree;
  inputs
    .iter()
    .zip(raw_rows)
    .enumerate()
    .map(|(index, (input, &rows))| {
      if index >= functions || rows == 0 {
        return 1;
      }
      let columns = input.main_width
        + stage2_width(input.lookups.len(), input.lookup_group_size, degree);
      let nodes = input.compile_graph(&params).map_or(0, |g| g.nodes.len());
      let copy_cost = columns * column_cost + nodes * node_cost;
      let padded = rows.next_power_of_two();
      let mut best = (1, 0usize);
      for k in 2..=max_copies {
        let heights = decompose(rows, k);
        let saved = (padded - heights.iter().sum::<usize>()) * input.main_width;
        let net = saved.saturating_sub((heights.len() - 1) * copy_cost);
        if net > best.1 {
          best = (k, net);
        }
      }
      if best.1 >= min_saving { best.0 } else { 1 }
    })
    .collect()
}

/// Splits each multi-copy circuit's real rows across its copies, largest
/// shard first, each zero-padded to its power-of-two height; copies left
/// over are inactive (height zero).
fn shard(
  traces: Vec<RowMajorMatrix<Scalar>>,
  copies: &[usize],
  raw_rows: &[usize],
) -> Result<(Vec<RowMajorMatrix<Scalar>>, Vec<(usize, Vec<usize>)>), String> {
  use p3_maybe_rayon::prelude::*;
  let mut out = Vec::with_capacity(copies.iter().sum());
  let mut shards = vec![];
  for (index, ((trace, &k), &rows)) in
    traces.into_iter().zip(copies).zip(raw_rows).enumerate()
  {
    if k == 1 {
      out.push(trace);
      continue;
    }
    let width = trace.width;
    if rows > trace.height() {
      return Err("sharded circuit has fewer trace rows than executed".into());
    }
    let heights = decompose(rows, k);
    let Some(&first) = heights.first() else {
      out.extend((0..k).map(|_| RowMajorMatrix::new(vec![], width)));
      shards.push((index, heights));
      continue;
    };
    // The pieces are copied out of the trace, the first piece included
    // when it is shorter than the trace: shrinking a multi-GB allocation in
    // place copies it on one thread under some allocators (mimalloc).
    // Rows past `rows` are zero in every piece.
    let mut values = trace.values;
    let mut start = first.min(rows);
    let mut rest = Vec::with_capacity(heights.len() - 1);
    for &height in &heights[1..] {
      let end = (start + height).min(rows);
      let mut piece: Vec<Scalar> =
        values[start * width..end * width].par_iter().copied().collect();
      piece.resize(height * width, Bn254.zero());
      rest.push(RowMajorMatrix::new(piece, width));
      start = end;
    }
    if values.len() > first * width {
      values = values[..first * width].par_iter().copied().collect();
    }
    if rows < first {
      values[rows * width..]
        .par_iter_mut()
        .for_each(|value| *value = Bn254.zero());
    }
    out.push(RowMajorMatrix::new(values, width));
    out.extend(rest);
    for _ in heights.len()..k {
      out.push(RowMajorMatrix::new(vec![], width));
    }
    shards.push((index, heights));
  }
  Ok((out, shards))
}

fn trace_shape(
  witness: &SystemWitness<Scalar>,
) -> Result<(Vec<bool>, Vec<u8>), String> {
  let mut active = Vec::with_capacity(witness.traces.len());
  let mut degrees = vec![];
  for trace in &witness.traces {
    let height = trace.height();
    active.push(height != 0);
    if height != 0 {
      if !height.is_power_of_two() {
        return Err("trace height is not a power of two".into());
      }
      degrees.push(u8::try_from(height.ilog2()).map_err(|_e| "trace height")?);
    }
  }
  Ok((active, degrees))
}
