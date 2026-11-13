//! A fixed GL-to-BN compression chain under independently pinned assets.
//!
//! Native acceptance verifies both the last outer proof and its carried pairing
//! equation. Intermediate BN proofs remain deferred; this interface does not
//! replace the terminal Aiur pairing program or its eventual PLONK proof.

use super::{
  Bn254, compress_bn as bn, compress_gl as gl,
  kzg::{Compiler, MAX_TOTAL_ROWS, VerifyingKey},
  kzg_advice as wire,
};
use crate::{
  kzg::{KzgConfig, Scalar, TranscriptKind, VerifierParams},
  pipeline::SetupConfig,
};
use aiur::{field::FieldBackend, trace::TracePlan};
use multi_stark::{config::ProofConfig, system::extension_params};
use serde::{Deserialize, Serialize};
use stark_verifier::compress_wrap::{Input, Statement};
use std::num::NonZeroU32;

const ENVELOPE_MAGIC: &[u8; 8] = b"IXAUCH01";
const MAX_ENVELOPE_BYTES: usize = wire::MAX_BYTES + 256;

/// Pins and public capacities are release configuration, never proof data.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StageConfiguration {
  pub artifact_blake3: [u8; 32],
  pub key_blake3: [u8; 32],
  pub max_log_height: u8,
  pub quotient_degree: usize,
}

impl StageConfiguration {
  pub const fn capacity(&self) -> gl::Capacity {
    gl::Capacity {
      max_log_height: self.max_log_height,
      quotient_degree: self.quotient_degree,
    }
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Configuration {
  pub gl: StageConfiguration,
  pub bn: StageConfiguration,
  pub bn_stages: NonZeroU32,
}

/// Trusted configuration authenticates every byte stream before its contents
/// participate in policy construction. Portable and source key hashes differ.
#[derive(Clone, Copy)]
pub struct Assets<'a> {
  pub gl_artifact: &'a [u8],
  pub gl_key: &'a [u8],
  pub bn_artifact: &'a [u8],
  pub bn_key: &'a [u8],
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Limits {
  pub max_record_bytes: usize,
  pub max_trace_bytes: usize,
  pub max_total_rows: u64,
}

impl Limits {
  fn validate(self) -> Result<(), String> {
    if self.max_record_bytes == 0
      || self.max_trace_bytes == 0
      || self.max_total_rows == 0
      || self.max_total_rows > MAX_TOTAL_ROWS
    {
      return Err("invalid chain resource limits".into());
    }
    Ok(())
  }

  fn traces(
    self,
    stage: &StageConfiguration,
  ) -> Result<bn::TraceLimits, String> {
    self.validate()?;
    Ok(bn::TraceLimits {
      max_height: stage.capacity().height()?,
      max_total_rows: self.max_total_rows,
      max_trace_bytes: self.max_trace_bytes,
    })
  }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Admission {
  pub gl: Limits,
  pub bn: Limits,
}

/// Candidate output only: the expected root statement, keys, policy and number
/// of stages must be supplied through a trusted `Verifier`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Envelope {
  pub stage: u32,
  pub accumulator: [Scalar; 4],
  pub proof: Vec<u8>,
}

impl Envelope {
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    if self.proof.len() > wire::MAX_BYTES {
      return Err("chain proof exceeds 64 MiB".into());
    }
    let mut bytes = ENVELOPE_MAGIC.to_vec();
    bytes.extend(
      bincode::serde::encode_to_vec(self, bincode::config::standard())
        .map_err(|error| error.to_string())?,
    );
    if bytes.len() > MAX_ENVELOPE_BYTES {
      return Err("chain envelope exceeds its byte limit".into());
    }
    Ok(bytes)
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    if bytes.len() > MAX_ENVELOPE_BYTES || !bytes.starts_with(ENVELOPE_MAGIC) {
      return Err("invalid chain envelope tag or size".into());
    }
    let (value, used): (Self, _) = bincode::serde::decode_from_slice(
      &bytes[8..],
      bincode::config::standard().with_limit::<67109120>(),
    )
    .map_err(|error| error.to_string())?;
    if used != bytes.len() - 8 || value.to_bytes()? != bytes {
      return Err("noncanonical or trailing chain envelope bytes".into());
    }
    bn::Accumulator::from_words(&value.accumulator)?;
    Ok(value)
  }
}

/// Loading a verifier needs no proving powers. Key pins authenticate fixed
/// commitments; preparing a prover also reproduces those commitments from the
/// pinned compiler artifacts and the selected SRS.
pub struct Verifier {
  configuration: Configuration,
  gl: gl::Wrapper,
  bn: bn::Wrapper,
  gl_key: VerifyingKey,
  bn_key: VerifyingKey,
  gl_source_key: Vec<u8>,
  bn_source_key: Vec<u8>,
  policy: wire::Policy,
}

impl Verifier {
  pub fn from_bytes(
    configuration: Configuration,
    assets: Assets<'_>,
  ) -> Result<Self, String> {
    configuration.gl.capacity().height()?;
    configuration.bn.capacity().height()?;
    let gl_key =
      VerifyingKey::from_bytes(assets.gl_key, &configuration.gl.key_blake3)?;
    let bn_key =
      VerifyingKey::from_bytes(assets.bn_key, &configuration.bn.key_blake3)?;
    check_key_configuration(&gl_key, &configuration.gl)?;
    check_key_configuration(&bn_key, &configuration.bn)?;
    common_setup(
      gl_key.system().config.pcs().verifier_params(),
      bn_key.system().config.pcs().verifier_params(),
    )?;
    let gl = gl::Wrapper::from_bytes(
      assets.gl_artifact,
      &configuration.gl.artifact_blake3,
    )?;
    let bn = bn::Wrapper::from_bytes(
      assets.bn_artifact,
      &configuration.bn.artifact_blake3,
    )?;
    check_program_key(gl.plan(), &gl_key)?;
    check_program_key(bn.plan(), &bn_key)?;
    let claim =
      gl.claim(&Statement { key_digest: [0; 32], claims_digest: [0; 32] })?;
    let gl_entry = u32::try_from(Bn254.try_to_u64(claim[1])?)
      .map_err(|_error| "GL physical entry exceeds u32")?;
    let gl_source_key = wire::key_bytes(&gl_key)?;
    let bn_source_key = wire::key_bytes(&bn_key)?;
    let policy = wire::Policy::new(
      bn_key.system().config.pcs().verifier_params(),
      *blake3::hash(&gl_source_key).as_bytes(),
      gl_entry,
      *blake3::hash(&bn_source_key).as_bytes(),
      bn.entry(),
    )?;
    Ok(Self {
      configuration,
      gl,
      bn,
      gl_key,
      bn_key,
      gl_source_key,
      bn_source_key,
      policy,
    })
  }

  pub const fn configuration(&self) -> &Configuration {
    &self.configuration
  }

  pub const fn policy(&self) -> &wire::Policy {
    &self.policy
  }

  pub fn parameters(&self) -> &VerifierParams {
    self.bn_key.system().config.pcs().verifier_params()
  }

  /// Authenticate a portable GL proof against the independently expected root
  /// before projecting it into source advice for the first BN stage.
  pub fn first_bn_input(
    &self,
    expected: &Statement,
    gl_proof: &[u8],
  ) -> Result<bn::Input, String> {
    let claim = self.gl.claim(expected)?;
    let proof = self.gl_key.decode_proof(gl_proof)?;
    self.gl_key.verify(&claim, &proof)?;
    bn::Input::from_source(
      self.public_inputs(expected, 1)?,
      self.gl_source_key.clone(),
      wire::claims_bytes(&[claim])?,
      wire::proof_bytes(&proof)?,
      self.policy.to_bytes(),
    )
  }

  fn public_inputs(
    &self,
    statement: &Statement,
    stage: u32,
  ) -> Result<bn::PublicInputs, String> {
    Ok(bn::PublicInputs {
      policy: bn::PolicyDigest::from_trusted(self.policy.digest()),
      stage: bn::Stage::new(stage)?,
      statement: bn::StatementDigest::from_root(statement),
    })
  }

  /// Complete native acceptance: the outer proof binds the accumulator to the
  /// expected original statement and fixed stage count, then its pairing closes
  /// every deferred predecessor check in the chain.
  pub fn verify(
    &self,
    expected: &Statement,
    envelope: &Envelope,
  ) -> Result<(), String> {
    if envelope.stage != self.configuration.bn_stages.get() {
      return Err("chain stage differs from the configured count".into());
    }
    let accumulator = bn::Accumulator::from_words(&envelope.accumulator)?;
    let public =
      self.public_inputs(expected, self.configuration.bn_stages.get())?;
    let claim = self.bn.claim(public, &accumulator)?;
    self.bn_key.verify_bytes(&claim, &envelope.proof)?;
    accumulator.check_pairing(self.parameters())
  }

  pub fn verify_bytes(
    &self,
    expected: &Statement,
    bytes: &[u8],
  ) -> Result<(), String> {
    self.verify(expected, &Envelope::from_bytes(bytes)?)
  }
}

pub struct Prover {
  verifier: Verifier,
  setup: SetupConfig,
  admission: Admission,
}

#[derive(Clone, Debug, Serialize)]
pub struct StageReport {
  /// Zero denotes GL; positive values denote the corresponding BN stage.
  pub stage: u32,
  pub instructions: u64,
  pub max_height: usize,
  pub total_rows: u64,
  pub trace_bytes: usize,
  pub execution_seconds: f64,
  pub setup_seconds: f64,
  pub trace_seconds: f64,
  pub proving_seconds: f64,
  pub verification_seconds: f64,
}

pub struct GlProven {
  pub proof: Vec<u8>,
  pub report: StageReport,
}

pub struct Proven {
  pub envelope: Envelope,
  pub stages: Vec<StageReport>,
}

impl Prover {
  /// Authenticate setup and reproduce both prepared keys before any root
  /// execution. Public caps may differ under Ignition; development setup
  /// identity requires the same cap for GL and BN.
  pub fn new(
    verifier: Verifier,
    setup: SetupConfig,
    admission: Admission,
  ) -> Result<Self, String> {
    admission.gl.validate()?;
    admission.bn.validate()?;
    if matches!(setup, SetupConfig::Development { .. })
      && verifier.configuration.gl.max_log_height
        != verifier.configuration.bn.max_log_height
    {
      return Err(
        "development GL and BN stages require a common public trace cap".into(),
      );
    }
    let gl_config = verifier.configuration.gl.capacity().config(&setup, 2)?;
    let bn_config = verifier.configuration.bn.capacity().config(&setup, 2)?;
    check_parameters(&gl_config, &verifier.gl_key)?;
    check_parameters(&bn_config, &verifier.bn_key)?;
    let gl_bytes = verifier
      .gl
      .verifying_key(&setup, verifier.configuration.gl.capacity())?;
    check_prepared_key(&gl_bytes, &verifier.configuration.gl)?;
    let height = fixed_height(verifier.bn.plan())?;
    let bn_keys = verifier.bn.verifying_key(
      verifier.configuration.bn.capacity().config(&setup, height)?,
    )?;
    check_prepared_key(&bn_keys.portable, &verifier.configuration.bn)?;
    Ok(Self { verifier, setup, admission })
  }

  pub const fn verifier(&self) -> &Verifier {
    &self.verifier
  }

  pub fn prove(
    &self,
    root: &Input,
    expected: &Statement,
  ) -> Result<Proven, String> {
    let gl = self.prove_gl(root, expected)?;
    let mut proven = self.prove_from_gl(expected, &gl.proof)?;
    proven.stages.insert(0, gl.report);
    Ok(proven)
  }

  pub fn prove_gl(
    &self,
    root: &Input,
    expected: &Statement,
  ) -> Result<GlProven, String> {
    if root.statement() != expected {
      return Err(
        "root input differs from the independently expected statement".into(),
      );
    }
    let execution = self
      .verifier
      .gl
      .execute_with_record_limit(root, self.admission.gl.max_record_bytes)?;
    let profile = self.verifier.gl.profile(&execution)?;
    let mut report = StageReport {
      stage: 0,
      instructions: profile.instructions,
      max_height: profile.max_height,
      total_rows: u64::try_from(profile.total_rows)
        .map_err(|_error| "GL row count overflow")?,
      trace_bytes: profile.main_fixed_lookup_bytes,
      execution_seconds: profile.execution_seconds,
      setup_seconds: 0.0,
      trace_seconds: 0.0,
      proving_seconds: 0.0,
      verification_seconds: 0.0,
    };
    self.admit_gl(&report)?;
    let proven = self.verifier.gl.prove_with_expected_key(
      &execution,
      &self.setup,
      self.verifier.configuration.gl.capacity(),
      &self.verifier.configuration.gl.key_blake3,
    )?;
    report.setup_seconds = proven.setup_seconds;
    report.trace_seconds = proven.trace_seconds;
    report.proving_seconds = proven.proving_seconds;
    report.verification_seconds = proven.verification_seconds;
    Ok(GlProven { proof: proven.proof, report })
  }

  /// Count the first BN execution without allocating proving traces. The record
  /// reservation still applies; trace admission is enforced by `prove_from_gl`.
  pub fn profile_from_gl(
    &self,
    expected: &Statement,
    gl_proof: &[u8],
  ) -> Result<bn::Profile, String> {
    let input = self.verifier.first_bn_input(expected, gl_proof)?;
    let execution =
      self.verifier.bn.execute(&input, self.admission.bn.max_record_bytes)?;
    self.verifier.bn.profile(&execution)
  }

  /// Resume a chain from an independently verified GL proof. Reports cover the
  /// BN stages generated by this call; the expected root remains caller data.
  pub fn prove_from_gl(
    &self,
    expected: &Statement,
    gl_proof: &[u8],
  ) -> Result<Proven, String> {
    let mut first = Some(self.verifier.first_bn_input(expected, gl_proof)?);
    let mut source: Option<Source> = None;
    let mut stages = vec![];
    let mut envelope = None;
    for stage in 1..=self.verifier.configuration.bn_stages.get() {
      let input = if let Some(first) = first.take() {
        first
      } else {
        let source = source.take().ok_or("missing BN predecessor")?;
        bn::Input::from_source(
          self.verifier.public_inputs(expected, stage)?,
          self.verifier.bn_source_key.clone(),
          source.claims,
          source.proof,
          self.verifier.policy.to_bytes(),
        )?
      };
      let execution =
        self.verifier.bn.execute(&input, self.admission.bn.max_record_bytes)?;
      let limits = self.admission.bn.traces(&self.verifier.configuration.bn)?;
      let planning_config =
        self.verifier.bn_key.system().config.clone().with_streaming_lookups();
      let profile =
        self.verifier.bn.preflight(&execution, &planning_config, limits)?;
      let config = self
        .verifier
        .configuration
        .bn
        .capacity()
        .config(&self.setup, profile.max_height)?;
      check_parameters(&config, &self.verifier.bn_key)?;
      let proven = self.verifier.bn.prove(&execution, config, limits)?;
      check_prepared_key(
        &proven.keys.portable,
        &self.verifier.configuration.bn,
      )?;
      stages.push(StageReport {
        stage,
        instructions: proven.profile.instructions,
        max_height: proven.profile.max_height,
        total_rows: proven.profile.total_rows,
        trace_bytes: proven.profile.main_fixed_lookup_bytes,
        execution_seconds: proven.profile.execution_seconds,
        setup_seconds: proven.setup_seconds,
        trace_seconds: proven.trace_seconds,
        proving_seconds: proven.proving_seconds,
        verification_seconds: proven.verification_seconds,
      });
      source = Some(Source {
        claims: proven.source_claims,
        proof: proven.source_proof,
      });
      envelope = Some(Envelope {
        stage,
        accumulator: *proven.accumulator.words(),
        proof: proven.proof,
      });
    }
    let envelope = envelope.ok_or("chain has no BN stages")?;
    self.verifier.verify(expected, &envelope)?;
    Ok(Proven { envelope, stages })
  }

  fn admit_gl(&self, report: &StageReport) -> Result<(), String> {
    let limits = self.admission.gl;
    let height = self.verifier.configuration.gl.capacity().height()?;
    if report.max_height > height
      || report.total_rows > limits.max_total_rows
      || report.trace_bytes > limits.max_trace_bytes
    {
      return Err(format!(
        "GL trace exceeds chain admission: height {} / {height}, rows {} / {}, trace bytes {} / {}",
        report.max_height,
        report.total_rows,
        limits.max_total_rows,
        report.trace_bytes,
        limits.max_trace_bytes
      ));
    }
    Ok(())
  }
}

struct Source {
  claims: Vec<u8>,
  proof: Vec<u8>,
}

fn check_key_configuration(
  key: &VerifyingKey,
  stage: &StageConfiguration,
) -> Result<(), String> {
  let config = &key.system().config;
  if !key.is_key_bound()
    || config.transcript_kind() != TranscriptKind::Blake3
    || config.pcs().verifier_params().max_trace_len()
      != stage.capacity().height()?
    || config.max_quotient_degree() != stage.quotient_degree
  {
    return Err(
      "chain key transcript or public capacity differs from configuration"
        .into(),
    );
  }
  Ok(())
}

fn common_setup(
  gl: &VerifierParams,
  bn: &VerifierParams,
) -> Result<(), String> {
  if gl.public_setup != bn.public_setup
    || gl.g1 != bn.g1
    || gl.g2 != bn.g2
    || gl.tau_g2 != bn.tau_g2
  {
    return Err(
      "chain keys have different public setup identities or anchors".into(),
    );
  }
  Ok(())
}

fn check_parameters(
  config: &KzgConfig,
  key: &VerifyingKey,
) -> Result<(), String> {
  if config
    .pcs()
    .verifier_params()
    .to_bytes()
    .map_err(|error| error.to_string())?
    != key
      .system()
      .config
      .pcs()
      .verifier_params()
      .to_bytes()
      .map_err(|error| error.to_string())?
    || config.max_quotient_degree() != key.system().config.max_quotient_degree()
    || config.transcript_kind() != key.system().config.transcript_kind()
  {
    return Err(
      "chain proving setup or public capacity differs from the trusted key"
        .into(),
    );
  }
  Ok(())
}

fn check_prepared_key(
  bytes: &[u8],
  stage: &StageConfiguration,
) -> Result<(), String> {
  if blake3::hash(bytes).as_bytes() != &stage.key_blake3 {
    return Err("prepared chain key differs from the trusted pin".into());
  }
  Ok(())
}

fn fixed_height(plan: &TracePlan<'_, Bn254>) -> Result<usize, String> {
  Ok(
    Compiler::new(plan)?
      .inputs()
      .iter()
      .filter_map(|input| input.preprocessed.as_ref())
      .map(|matrix| matrix.values.len() / matrix.width)
      .max()
      .unwrap_or(2)
      .max(2),
  )
}

fn check_program_key(
  plan: &TracePlan<'_, Bn254>,
  key: &VerifyingKey,
) -> Result<(), String> {
  let compiler = Compiler::new(plan)?;
  if compiler.inputs().len() != key.system().circuits.len() {
    return Err(
      "chain key circuit count differs from the compiler artifact".into(),
    );
  }
  let params = extension_params::<KzgConfig>();
  for (input, circuit) in compiler.inputs().iter().zip(&key.system().circuits) {
    let (width, height) =
      input.preprocessed.as_ref().map_or((0, 0), |matrix| {
        (matrix.width, matrix.values.len() / matrix.width)
      });
    if input.main_width != circuit.main_width
      || input.lookup_group_size != circuit.lookup_group_size
      || width != circuit.preprocessed_width
      || height != circuit.preprocessed_height
      || input
        .compile_graph(&params)
        .map_err(|error| format!("invalid chain compiler circuit: {error:?}"))?
        != circuit.graph
    {
      return Err(
        "chain key circuit differs from the compiler artifact".into(),
      );
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::{Srs, curve::G1Affine};

  fn envelope() -> Envelope {
    Envelope {
      stage: 1,
      accumulator: *bn::Accumulator::from_points(&[G1Affine::identity(); 2])
        .unwrap()
        .words(),
      proof: vec![1, 2, 3],
    }
  }

  #[test]
  fn envelope_is_bounded_canonical_and_contains_no_trust_pins() {
    let value = envelope();
    let bytes = value.to_bytes().unwrap();
    assert_eq!(
      Envelope::from_bytes(&bytes).unwrap().to_bytes().unwrap(),
      bytes
    );
    let json = serde_json::to_value(&value).unwrap();
    assert_eq!(json.as_object().unwrap().len(), 3);
    let mut trailing = bytes;
    trailing.push(0);
    assert!(Envelope::from_bytes(&trailing).is_err());
    let mut invalid = value;
    invalid.accumulator[0] =
      Scalar(ark_bn254::Fr::from(u128::MAX)) + Bn254.one();
    assert!(Envelope::from_bytes(&invalid.to_bytes().unwrap()).is_err());
    let mut oversized = ENVELOPE_MAGIC.to_vec();
    oversized.resize(MAX_ENVELOPE_BYTES + 1, 0);
    assert!(Envelope::from_bytes(&oversized).is_err());
  }

  #[test]
  fn common_setup_accepts_distinct_caps_but_not_distinct_anchors_or_identity() {
    let srs = Srs::unsafe_dev_setup_prefix(64, 255, b"chain-parameters");
    let a = VerifierParams::with_max_trace_len(&srs, 64);
    let b = VerifierParams::with_max_trace_len(&srs, 256);
    common_setup(&a, &b).unwrap();
    let other = VerifierParams::with_max_trace_len(
      &Srs::unsafe_dev_setup_prefix(64, 255, b"other-chain"),
      64,
    );
    assert!(common_setup(&a, &other).is_err());
    let mut changed = a.clone();
    changed.public_setup.id[0] ^= 1;
    assert!(common_setup(&a, &changed).is_err());
  }

  #[test]
  fn configuration_and_admission_reject_invalid_bounds() {
    assert!(
      serde_json::from_value::<NonZeroU32>(serde_json::json!(0)).is_err()
    );
    let base =
      Limits { max_record_bytes: 1, max_trace_bytes: 1, max_total_rows: 1 };
    base.validate().unwrap();
    for invalid in [
      Limits { max_record_bytes: 0, ..base },
      Limits { max_trace_bytes: 0, ..base },
      Limits { max_total_rows: MAX_TOTAL_ROWS + 1, ..base },
    ] {
      assert!(invalid.validate().is_err());
    }
  }
}
