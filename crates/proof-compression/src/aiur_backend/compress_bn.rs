//! Artifact-pinned execution and proving of the Aiur KZG compression step.
//!
//! Policy and statement digests are independently expected public inputs.
//! Source-wire bytes are candidate advice, authenticated again by the program.
//! Each proof carries a deferred accumulator; terminal pairing verification is
//! required before accepting the compression chain.

use super::{
  Bn254,
  compress_gl::CircuitSize,
  fq, g1,
  kzg::{Backend, Compiler, MAX_TOTAL_ROWS, VerifyingKey},
  kzg_advice as wire,
};
use crate::kzg::{
  KzgConfig, Scalar, TranscriptKind, VerifierParams,
  curve::{G1Affine, PairingCurve},
};
use aiur::{
  Execution, artifact::WidePackage, budget::RecordPool, field::FieldBackend,
  hints::HintChannels, maps::MapOverrides, trace::TracePlan,
};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::CanonicalDeserialize;
use multi_stark::{
  config::ProofConfig,
  lookup::{logup_max_degree, stage2_width},
  system::extension_params,
};
use serde::Serialize;
use std::{num::NonZeroU32, sync::Arc, time::Instant};

pub const ENTRY: &str = "CompressBN::compress_v1";
pub const ARGUMENTS: usize = 17;
pub const CLAIM_WORDS: usize = 23;
const POLICY_BYTES: usize = 8 + 128 + 32 + 4 + 32 + 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolicyDigest([u8; 32]);

impl PolicyDigest {
  /// The pin must come from trusted chain configuration, never its proof package.
  pub const fn from_trusted(bytes: [u8; 32]) -> Self {
    Self(bytes)
  }

  pub const fn as_bytes(&self) -> &[u8; 32] {
    &self.0
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StatementDigest([u8; 32]);

impl StatementDigest {
  pub const fn new(bytes: [u8; 32]) -> Self {
    Self(bytes)
  }

  pub fn from_root(
    statement: &stark_verifier::compress_wrap::Statement,
  ) -> Self {
    Self(*blake3::hash(&statement.preimage()).as_bytes())
  }

  pub const fn as_bytes(&self) -> &[u8; 32] {
    &self.0
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage(NonZeroU32);

impl Stage {
  pub const FIRST: Self = Self(NonZeroU32::MIN);

  pub fn new(value: u32) -> Result<Self, String> {
    NonZeroU32::new(value)
      .map(Self)
      .ok_or_else(|| "CompressBN stage must be a positive u32".into())
  }

  pub const fn get(self) -> u32 {
    self.0.get()
  }

  pub fn next(self) -> Result<Self, String> {
    self
      .get()
      .checked_add(1)
      .ok_or("CompressBN stage overflow".into())
      .and_then(Self::new)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicInputs {
  pub policy: PolicyDigest,
  pub stage: Stage,
  pub statement: StatementDigest,
}

impl PublicInputs {
  pub fn arguments(self) -> [Scalar; ARGUMENTS] {
    let mut args = [Bn254.zero(); ARGUMENTS];
    args[..8].copy_from_slice(&wire::digest_words(self.policy.as_bytes()));
    args[8] = Bn254.from_u64(u64::from(self.stage.get()));
    args[9..].copy_from_slice(&wire::digest_words(self.statement.as_bytes()));
    args
  }
}

/// Two canonical compressed G1 points packed into four little-endian u128s.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Accumulator([Scalar; 4]);

impl Accumulator {
  pub fn from_words(words: &[Scalar]) -> Result<Self, String> {
    let points = wire::decode_accumulator(words)?;
    let canonical = wire::accumulator_words(&points)?;
    if canonical != words {
      return Err("noncanonical CompressBN accumulator".into());
    }
    Ok(Self(canonical))
  }

  pub fn from_points(points: &[G1Affine; 2]) -> Result<Self, String> {
    Self::from_words(&wire::accumulator_words(points)?)
  }

  pub const fn words(&self) -> &[Scalar; 4] {
    &self.0
  }

  pub fn points(&self) -> [G1Affine; 2] {
    wire::decode_accumulator(&self.0).expect("validated accumulator")
  }

  /// Discharge the carried equation natively under independently trusted
  /// anchors. Acceptance also requires a verified proof binding these words
  /// to the expected policy, stage and root statement.
  pub fn check_pairing(
    &self,
    parameters: &VerifierParams,
  ) -> Result<(), String> {
    let anchors = [parameters.g2, parameters.tau_g2];
    if anchors.iter().any(|point| {
      point.is_zero()
        || !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
    }) {
      return Err("invalid CompressBN pairing anchors".into());
    }
    if !PairingCurve::multi_pairing(self.points(), anchors).is_zero() {
      return Err("CompressBN deferred pairing equation failed".into());
    }
    Ok(())
  }
}

struct AuthorizedKey {
  digest: [u8; 32],
  entry: u32,
}

struct Policy {
  anchors: [u8; 128],
  gl: AuthorizedKey,
  bn: AuthorizedKey,
}

impl Policy {
  fn decode(bytes: &[u8], expected: PolicyDigest) -> Result<Self, String> {
    if bytes.len() != POLICY_BYTES || !bytes.starts_with(wire::POLICY_MAGIC) {
      return Err("invalid CompressBN policy encoding".into());
    }
    if blake3::hash(bytes).as_bytes() != expected.as_bytes() {
      return Err("CompressBN policy differs from the trusted pin".into());
    }
    let key = |offset| AuthorizedKey {
      digest: bytes[offset..offset + 32].try_into().unwrap(),
      entry: u32::from_le_bytes(
        bytes[offset + 32..offset + 36].try_into().unwrap(),
      ),
    };
    Ok(Self {
      anchors: bytes[8..136].try_into().unwrap(),
      gl: key(136),
      bn: key(172),
    })
  }

  fn predecessor(&self, stage: Stage) -> &AuthorizedKey {
    if stage == Stage::FIRST { &self.gl } else { &self.bn }
  }
}

/// Bounded source-wire advice with independently authenticated policy and key.
/// Construction checks the public-call envelope; Aiur verifies the proof body.
pub struct Input {
  public: PublicInputs,
  policy: Policy,
  wire: wire::Inputs,
}

impl Input {
  pub fn from_source(
    expected: PublicInputs,
    key: Vec<u8>,
    claims: Vec<u8>,
    proof: Vec<u8>,
    policy: Vec<u8>,
  ) -> Result<Self, String> {
    if [&key, &claims, &proof, &policy]
      .iter()
      .any(|bytes| bytes.len() > wire::MAX_BYTES)
    {
      return Err("CompressBN source input exceeds 64 MiB".into());
    }
    let authorized = Policy::decode(&policy, expected.policy)?;
    let predecessor = authorized.predecessor(expected.stage);
    if blake3::hash(&key).as_bytes() != &predecessor.digest {
      return Err(
        "CompressBN predecessor key differs from the trusted policy".into(),
      );
    }
    if source_anchors(&key)? != authorized.anchors {
      return Err(
        "CompressBN predecessor and policy have different SRS anchors".into(),
      );
    }
    check_previous(&claims, expected, predecessor.entry)?;
    if !proof.starts_with(wire::PROOF_MAGIC) {
      return Err("invalid CompressBN source proof tag".into());
    }
    Ok(Self {
      public: expected,
      policy: authorized,
      wire: wire::Inputs::new(key, claims, proof, policy)?,
    })
  }

  pub const fn public_inputs(&self) -> PublicInputs {
    self.public
  }

  pub const fn source(&self) -> &wire::Inputs {
    &self.wire
  }
}

pub struct Wrapper {
  plan: TracePlan<'static, Bn254>,
  maps: MapOverrides<Scalar>,
  artifact_digest: [u8; 32],
  entry: u32,
}

pub struct Executed<'a> {
  input: &'a Input,
  record: Execution<Bn254>,
  accumulator: Accumulator,
  artifact_digest: [u8; 32],
  execution_seconds: f64,
}

impl Executed<'_> {
  pub const fn input(&self) -> &Input {
    self.input
  }

  pub const fn record(&self) -> &Execution<Bn254> {
    &self.record
  }

  pub const fn accumulator(&self) -> &Accumulator {
    &self.accumulator
  }
}

#[derive(Clone, Debug, Serialize)]
pub struct FunctionRows {
  pub name: String,
  pub chip: String,
  pub rows: usize,
}

/// Exact padded trace sizes before witness population. Polynomial transforms,
/// commitments, quotient workspaces and allocator slack require additional RAM.
#[derive(Clone, Debug, Serialize)]
pub struct Profile {
  pub artifact_blake3: String,
  pub policy_blake3: String,
  pub statement_blake3: String,
  pub stage: u32,
  pub instructions: u64,
  pub record: aiur::execute::RecordStorage,
  pub circuits: Vec<CircuitSize>,
  pub function_rows: Vec<FunctionRows>,
  pub max_height: usize,
  pub total_rows: u64,
  pub main_cells: usize,
  pub fixed_cells: usize,
  pub stage2_accumulator_cells: usize,
  pub concrete_lookup_cells: usize,
  pub main_fixed_lookup_bytes: usize,
  pub quotient_degree: usize,
  pub execution_seconds: f64,
  pub planning_seconds: f64,
}

impl Profile {
  /// Materialized lookup tuples coexist with the trace matrices when lookup
  /// streaming is disabled. Prover workspaces and allocator slack are separate.
  pub fn trace_bytes(&self, config: &KzgConfig) -> Result<usize, String> {
    let concrete = if config.uses_streaming_lookups() {
      0
    } else {
      self
        .concrete_lookup_cells
        .checked_mul(size_of::<Scalar>())
        .ok_or("concrete lookup byte count overflow")?
    };
    self
      .main_fixed_lookup_bytes
      .checked_add(concrete)
      .ok_or_else(|| "trace byte count overflow".into())
  }
}

#[derive(Clone, Copy, Debug)]
pub struct TraceLimits {
  pub max_height: usize,
  pub max_total_rows: u64,
  pub max_trace_bytes: usize,
}

impl TraceLimits {
  pub fn check(
    self,
    profile: &Profile,
    config: &KzgConfig,
  ) -> Result<(), String> {
    if !self.max_height.is_power_of_two()
      || self.max_height > 1 << 28
      || self.max_total_rows == 0
      || self.max_total_rows > MAX_TOTAL_ROWS
      || self.max_trace_bytes == 0
    {
      return Err("invalid CompressBN trace limits".into());
    }
    let trace_bytes = profile.trace_bytes(config)?;
    if profile.max_height > self.max_height
      || profile.total_rows > self.max_total_rows
      || trace_bytes > self.max_trace_bytes
    {
      return Err(format!(
        "CompressBN trace exceeds the admitted resource limits: height {} / {}, rows {} / {}, trace bytes {} / {}",
        profile.max_height,
        self.max_height,
        profile.total_rows,
        self.max_total_rows,
        trace_bytes,
        self.max_trace_bytes,
      ));
    }
    Ok(())
  }
}

/// Portable host transport and the distinct semantic source-wire projection.
/// The source digest and physical entry ID are inputs to trusted chain policy.
pub struct VerifyingKeys {
  pub portable: Vec<u8>,
  pub source: Vec<u8>,
  pub entry: u32,
}

impl VerifyingKeys {
  pub fn source_digest(&self) -> [u8; 32] {
    *blake3::hash(&self.source).as_bytes()
  }
}

pub struct Proven {
  pub keys: VerifyingKeys,
  pub proof: Vec<u8>,
  pub source_proof: Vec<u8>,
  pub source_claims: Vec<u8>,
  pub claim: Vec<Scalar>,
  pub public: PublicInputs,
  pub accumulator: Accumulator,
  pub profile: Profile,
  pub setup_seconds: f64,
  pub trace_seconds: f64,
  pub proving_seconds: f64,
  pub verification_seconds: f64,
}

impl Wrapper {
  /// Authenticate compiler output before parsing; structural validity alone
  /// cannot identify the intended verification program.
  pub fn from_bytes(
    bytes: &[u8],
    expected_digest: &[u8; 32],
  ) -> Result<Self, String> {
    let artifact_digest = *blake3::hash(bytes).as_bytes();
    if &artifact_digest != expected_digest {
      return Err("CompressBN artifact differs from the trusted pin".into());
    }
    let package = WidePackage::decode(bytes)?;
    let trace =
      package.trace.ok_or("CompressBN needs a compiler trace artifact")?;
    let mut program = package.program.check_with(Bn254)?;
    program.track_depth(&trace)?;
    program.entry(ENTRY)?;
    let plan = TracePlan::new(Arc::new(program), trace)?;
    let claim = plan.public_claim(
      ENTRY,
      &[Bn254.zero(); ARGUMENTS],
      &[Bn254.zero(); 4],
    )?;
    if claim.len() != CLAIM_WORDS || claim[0] != Bn254.one() {
      return Err(
        "CompressBN needs the version-one 23-word public call".into(),
      );
    }
    let entry = u32::try_from(Bn254.try_to_u64(claim[1])?)
      .map_err(|_error| "CompressBN callable exceeds u32")?;
    let mut maps = MapOverrides::new();
    aiur::library::u8::register_maps(plan.program(), &mut maps)?;
    Ok(Self { plan, maps, artifact_digest, entry })
  }

  pub const fn artifact_digest(&self) -> &[u8; 32] {
    &self.artifact_digest
  }

  pub const fn plan(&self) -> &TracePlan<'static, Bn254> {
    &self.plan
  }

  pub const fn entry(&self) -> u32 {
    self.entry
  }

  pub fn claim(
    &self,
    public: PublicInputs,
    accumulator: &Accumulator,
  ) -> Result<Vec<Scalar>, String> {
    self.plan.public_claim(ENTRY, &public.arguments(), accumulator.words())
  }

  /// Trusted proving powers, public capacity and transcript settings come from
  /// the caller. A shorter loaded SRS prefix must retain the same public cap.
  pub fn verifying_key(
    &self,
    config: KzgConfig,
  ) -> Result<VerifyingKeys, String> {
    check_config(&config)?;
    check_proving_capacity(&config, 2)?;
    let compiler = Compiler::new(&self.plan)?;
    let fixed_height = compiler
      .inputs()
      .iter()
      .filter_map(|input| input.preprocessed.as_ref())
      .map(|matrix| matrix.values.len() / matrix.width)
      .max()
      .unwrap_or(2)
      .max(2);
    check_proving_capacity(&config, fixed_height)?;
    let backend = Backend::new(&self.plan, config)?;
    self.encode_key(&backend.verifying_key()?)
  }

  fn encode_key(&self, key: &VerifyingKey) -> Result<VerifyingKeys, String> {
    Ok(VerifyingKeys {
      portable: key.to_bytes()?,
      source: wire::key_bytes(key)?,
      entry: self.entry,
    })
  }

  /// The reservation bounds resident interpreter storage, including temporary
  /// growth. Artifact bytes, source advice and prover workspaces are separate.
  pub fn execute<'a>(
    &self,
    input: &'a Input,
    max_record_bytes: usize,
  ) -> Result<Executed<'a>, String> {
    if max_record_bytes == 0 {
      return Err("CompressBN record limit must be positive".into());
    }
    let started = Instant::now();
    let mut hints = HintChannels::new();
    aiur::library::u32::register(&mut hints, Bn254)?;
    aiur::library::u64::register(&mut hints, Bn254)?;
    fq::register(&mut hints)?;
    g1::register(&mut hints)?;
    wire::register(&mut hints)?;
    input.wire.register(&mut hints)?;
    let prepared = self
      .plan
      .program()
      .prepare_hint_channels(&[], &hints)?
      .with_map_overrides(&self.maps)?;
    let pool = RecordPool::new(max_record_bytes, max_record_bytes);
    let reservation = pool
      .try_admit()
      .map_err(|error| error.to_string())?
      .ok_or("CompressBN record reservation unavailable")?;
    let record = prepared
      .execute_reserved(ENTRY, input.public.arguments().to_vec(), &reservation)
      .map_err(|error| error.to_string())?;
    reservation.finish_execution();
    let accumulator = Accumulator::from_words(&record.output)?;
    Ok(Executed {
      input,
      record,
      accumulator,
      artifact_digest: self.artifact_digest,
      execution_seconds: started.elapsed().as_secs_f64(),
    })
  }

  pub fn profile(&self, execution: &Executed<'_>) -> Result<Profile, String> {
    if execution.artifact_digest != self.artifact_digest {
      return Err(
        "CompressBN execution belongs to another compiler artifact".into(),
      );
    }
    let started = Instant::now();
    let compiler = Compiler::new(&self.plan)?;
    let heights = compiler.row_counts(&execution.record)?;
    let params = extension_params::<KzgConfig>();
    let mut circuits = Vec::with_capacity(heights.len());
    let (mut main_cells, mut fixed_cells, mut stage2_cells, mut concrete_cells) =
      (0, 0, 0, 0);
    let mut total_rows = 0u64;
    let mut max_height = 2;
    let mut quotient_degree = 1;
    for ((input, name), height) in
      compiler.inputs().iter().zip(compiler.names()).zip(heights)
    {
      let graph = input
        .compile_graph(&params)
        .map_err(|error| format!("{name}: {error:?}"))?;
      let degree = graph
        .max_constraint_degree
        .max(logup_max_degree(&graph, input.lookup_group_size))
        as usize;
      let quotient = (degree.max(2) - 1)
        .checked_next_power_of_two()
        .ok_or("quotient degree overflow")?;
      let fixed_width =
        input.preprocessed.as_ref().map_or(0, |matrix| matrix.width);
      let lookup_width = stage2_width(
        input.lookups.len(),
        input.lookup_group_size,
        params.degree,
      );
      let concrete_lookup_width =
        graph.lookups.iter().try_fold(0usize, |sum, lookup| {
          sum.checked_add(lookup.args.len() + 1).ok_or("lookup width overflow")
        })?;
      add_cells(&mut main_cells, height, input.main_width)?;
      add_cells(&mut fixed_cells, height, fixed_width)?;
      add_cells(&mut stage2_cells, height, lookup_width)?;
      add_cells(&mut concrete_cells, height, concrete_lookup_width)?;
      total_rows = total_rows
        .checked_add(
          u64::try_from(height).map_err(|_error| "row count overflow")?,
        )
        .ok_or("row count overflow")?;
      max_height = max_height.max(height);
      quotient_degree = quotient_degree.max(quotient);
      circuits.push(CircuitSize {
        name: name.clone(),
        height,
        main_width: input.main_width,
        fixed_width,
        lookup_width,
        concrete_lookup_width,
        quotient_degree: quotient,
      });
    }
    let trace_bytes = main_cells
      .checked_add(fixed_cells)
      .and_then(|cells| cells.checked_add(stage2_cells))
      .and_then(|cells| cells.checked_mul(size_of::<Scalar>()))
      .ok_or("trace byte count overflow")?;
    let public = execution.input.public;
    let function_rows = self
      .plan
      .function_chips()
      .iter()
      .enumerate()
      .map(|(index, &chip)| {
        Ok(FunctionRows {
          name: self.plan.program().program().functions[index].name.clone(),
          chip: self.plan.artifact().chips[chip].name.clone(),
          rows: execution
            .record
            .queries
            .callable_rows(index)
            .ok_or("missing function query count")?,
        })
      })
      .collect::<Result<Vec<_>, String>>()?;
    Ok(Profile {
      artifact_blake3: hex(self.artifact_digest),
      policy_blake3: hex(*public.policy.as_bytes()),
      statement_blake3: hex(*public.statement.as_bytes()),
      stage: public.stage.get(),
      instructions: execution.record.instructions,
      record: execution.record.storage_usage(),
      circuits,
      function_rows,
      max_height,
      total_rows,
      main_cells,
      fixed_cells,
      stage2_accumulator_cells: stage2_cells,
      concrete_lookup_cells: concrete_cells,
      main_fixed_lookup_bytes: trace_bytes,
      quotient_degree,
      execution_seconds: execution.execution_seconds,
      planning_seconds: started.elapsed().as_secs_f64(),
    })
  }

  pub fn preflight(
    &self,
    execution: &Executed<'_>,
    config: &KzgConfig,
    limits: TraceLimits,
  ) -> Result<Profile, String> {
    let profile = self.profile(execution)?;
    limits.check(&profile, config)?;
    Ok(profile)
  }

  /// Resource and policy checks precede witness population. This proof attests
  /// to the deferred verification step, not to the final pairing equation.
  pub fn prove(
    &self,
    execution: &Executed<'_>,
    config: KzgConfig,
    limits: TraceLimits,
  ) -> Result<Proven, String> {
    let profile = self.preflight(execution, &config, limits)?;
    check_config(&config)?;
    if profile.max_height > config.pcs().verifier_params().max_trace_len()
      || profile.quotient_degree > config.max_quotient_degree()
    {
      return Err(format!(
        "CompressBN trace exceeds the KZG capacity: height {} / {}, quotient degree {} / {}",
        profile.max_height,
        config.pcs().verifier_params().max_trace_len(),
        profile.quotient_degree,
        config.max_quotient_degree(),
      ));
    }
    let policy = &execution.input.policy;
    let configured_policy = wire::Policy::new(
      config.pcs().verifier_params(),
      policy.gl.digest,
      policy.gl.entry,
      policy.bn.digest,
      self.entry,
    )?;
    if configured_policy.digest() != *execution.input.public.policy.as_bytes() {
      return Err(
        "CompressBN proving configuration differs from the trusted policy"
          .into(),
      );
    }
    check_proving_capacity(&config, profile.max_height)?;
    let started = Instant::now();
    let backend = Backend::new(&self.plan, config)?;
    let portable = backend.verifying_key()?;
    let keys = self.encode_key(&portable)?;
    if keys.source_digest() != execution.input.policy.bn.digest
      || self.entry != execution.input.policy.bn.entry
      || source_anchors(&keys.source)? != execution.input.policy.anchors
    {
      return Err(
        "CompressBN proving key differs from the trusted policy".into(),
      );
    }
    let setup_seconds = started.elapsed().as_secs_f64();
    let args = execution.input.public.arguments();
    let started = Instant::now();
    let witness = backend.generate(&execution.record, ENTRY, &args)?;
    let trace_seconds = started.elapsed().as_secs_f64();
    let started = Instant::now();
    let proof =
      backend.prove(ENTRY, &args, execution.accumulator.words(), witness)?;
    let proving_seconds = started.elapsed().as_secs_f64();
    let started = Instant::now();
    let claim = self.claim(execution.input.public, &execution.accumulator)?;
    let proof_bytes = portable.encode_proof(&proof)?;
    portable.verify_bytes(&claim, &proof_bytes)?;
    let verification_seconds = started.elapsed().as_secs_f64();
    Ok(Proven {
      keys,
      proof: proof_bytes,
      source_proof: wire::proof_bytes(&proof)?,
      source_claims: wire::claims_bytes(std::slice::from_ref(&claim))?,
      claim,
      public: execution.input.public,
      accumulator: execution.accumulator.clone(),
      profile,
      setup_seconds,
      trace_seconds,
      proving_seconds,
      verification_seconds,
    })
  }
}

fn check_config(config: &KzgConfig) -> Result<(), String> {
  if config.transcript_kind() != TranscriptKind::Blake3
    || config.max_log_degree() + config.max_quotient_degree().ilog2() as usize
      > 28
  {
    return Err(
      "CompressBN needs BLAKE3 and an admissible BN254 KZG capacity".into(),
    );
  }
  Ok(())
}

fn check_proving_capacity(
  config: &KzgConfig,
  required: usize,
) -> Result<(), String> {
  let loaded = config
    .pcs()
    .proving_capacity()
    .ok_or("CompressBN proving requires a loaded SRS prefix")?;
  if loaded < required {
    return Err(format!(
      "CompressBN loaded SRS prefix is too short: required {required} powers, loaded {loaded}",
    ));
  }
  Ok(())
}

fn source_anchors(key: &[u8]) -> Result<[u8; 128], String> {
  if !key.starts_with(wire::KEY_MAGIC) {
    return Err("invalid CompressBN source key tag".into());
  }
  let seed_bytes = u32::from_le_bytes(
    key.get(8..12).ok_or("truncated source key")?.try_into().unwrap(),
  ) as usize;
  let offset = 12usize
    .checked_add(seed_bytes)
    .and_then(|n| n.checked_add(8 + 32))
    .ok_or("source key offset overflow")?;
  key
    .get(offset..)
    .and_then(|bytes| bytes.get(..128))
    .ok_or_else(|| "truncated source key anchors".into())
    .map(|bytes| bytes.try_into().unwrap())
}

fn check_previous(
  bytes: &[u8],
  public: PublicInputs,
  entry: u32,
) -> Result<(), String> {
  let width = if public.stage == Stage::FIRST { 18 } else { CLAIM_WORDS };
  let encoded_width = u32::try_from(width)
    .map_err(|_error| "CompressBN claim width overflow")?
    .to_le_bytes();
  if bytes.len() != 16 + 32 * width
    || !bytes.starts_with(wire::CLAIMS_MAGIC)
    || bytes[8..12] != 1u32.to_le_bytes()
    || bytes[12..16] != encoded_width
  {
    return Err(
      "CompressBN predecessor must have one exact version-one call".into(),
    );
  }
  let words: Vec<_> = bytes[16..]
    .as_chunks::<32>()
    .0
    .iter()
    .map(|bytes| {
      ark_bn254::Fr::deserialize_compressed(bytes.as_slice())
        .map(Scalar)
        .map_err(|error| error.to_string())
    })
    .collect::<Result<_, _>>()?;
  let mut expected = vec![Bn254.one(), Bn254.from_u64(u64::from(entry))];
  if public.stage == Stage::FIRST {
    expected.extend([Bn254.zero(); 8]);
  } else {
    expected.extend(wire::digest_words(public.policy.as_bytes()));
    expected.push(Bn254.from_u64(u64::from(public.stage.get() - 1)));
  }
  expected.extend(wire::digest_words(public.statement.as_bytes()));
  if words[..expected.len()] != expected {
    return Err("CompressBN predecessor call differs from the expected statement or stage".into());
  }
  if public.stage != Stage::FIRST {
    Accumulator::from_words(&words[expected.len()..])?;
  }
  Ok(())
}

fn add_cells(
  total: &mut usize,
  height: usize,
  width: usize,
) -> Result<(), String> {
  *total = height
    .checked_mul(width)
    .and_then(|n| total.checked_add(n))
    .ok_or("trace cell count overflow")?;
  Ok(())
}

fn hex(digest: [u8; 32]) -> String {
  blake3::Hash::from_bytes(digest).to_hex().to_string()
}
