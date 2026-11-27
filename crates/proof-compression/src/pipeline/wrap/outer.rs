//! Recursive KZG wrapper: staging and proving in one process, and the
//! portable verifier its packets are checked with.
#[cfg(any(feature = "plonk", feature = "groth16"))]
mod final_export;
#[cfg(any(feature = "plonk", feature = "groth16"))]
mod relation;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(in crate::pipeline) use final_export::describe as final_description;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(in crate::pipeline) use final_export::export as final_export;

use super::recursive::{self, RecursiveVerifier};
use super::{
  super::Result as PipelineResult,
  super::{
    claims::ClaimTemplate,
    fixed_cache,
    lowering::{self, Lowered},
    prover,
    setup::{SetupClass, SetupSource},
    statement::{self, Statement},
    storage,
  },
};
use crate::{
  kzg::{
    KzgCommitment, KzgConfig, TranscriptKind,
    compact::FixedProofCodec,
    curve::{Bn254, G2AffineOf, KzgCurve},
    field::CurveScalar,
  },
  recursive::{native_verifier::Built, pairing::PUBLIC_VALUES},
};
use multi_stark::{
  plonkish::{Assignment, MultiStarkCircuit},
  traits::{Field, TwoAdicField},
};
use std::{fs, marker::PhantomData, path::Path};

#[cfg(test)]
pub(super) const OUTER_SEED: &[u8] = Bn254::OUTER_SEED;
const RECURSIVE_PUBLIC_VALUES: usize = statement::WORDS + PUBLIC_VALUES;
/// Largest admitted recursive computation trace. The development public
/// degree of a staged verifying key covers exactly its own height.
pub(super) const MAX_TRACE_LEN: usize = lowering::RECURSIVE_HEIGHT;

#[derive(serde::Serialize, serde::Deserialize)]
struct Pairings {
  keys: Vec<u8>,
}

pub(crate) fn stage<C: KzgCurve>(
  built: Built<C>,
  assignment: Assignment<CurveScalar<C>>,
  dir: &Path,
  vk: &[u8],
  statement: &Statement,
  config: &super::super::StageConfig,
) -> storage::Result<()> {
  let frontend = Frontend::<C>::from_built(built, vk)?;
  frontend.stage(assignment, dir, statement, config)
}

/// A recursive circuit lowered into one computation trace and one merged
/// table, ready to stage any number of requests of its verifying key.
pub(crate) struct Frontend<C: KzgCurve = Bn254> {
  compiled: MultiStarkCircuit<CurveScalar<C>>,
  pairings: Pairings,
  vk: Vec<u8>,
}

impl<C: KzgCurve> Frontend<C> {
  /// The setup this circuit is proved under. Release (Ignition / Filecoin)
  /// parameters must also be the ones the inner pairing keys come from.
  fn setup(
    &self,
    config: &super::super::SetupConfig,
  ) -> storage::Result<SetupSource<C>> {
    let setup = config
      .for_stage::<C>(C::OUTER_SEED, self.compiled.main_height())?
      .with_transcript(TranscriptKind::Blake3);
    if matches!(setup.class(), SetupClass::Ignition | SetupClass::Filecoin)
      && decode_pairing_keys::<C>(&self.pairings)? != {
        let parameters = setup.verifier_params(2)?;
        [parameters.g2, parameters.tau_g2]
      }
    {
      return Err(
        "recursive inner pairing anchors differ from the released ceremony parameters".into(),
      );
    }
    Ok(setup)
  }

  /// The verifying key proofs of this circuit verify under, derived from its
  /// fixed setup alone; `prove` assembles the same key from the setup it
  /// commits.
  pub(crate) fn verifying_key(
    &self,
    config: &super::super::SetupConfig,
  ) -> storage::Result<VerifyingKey<C>> {
    let setup = self.setup(config)?;
    let height = self.compiled.main_height();
    let parts =
      prover::fixed_setup(&proving_config(&setup, height)?, &self.compiled)?;
    self.key_from_parts(&parts, &setup)
  }

  /// The verifying key, with the fixed preprocessing taken from or published
  /// to the fixed cache under `root` that `stage` uses for this circuit.
  pub(crate) fn prepared_key(
    &self,
    config: &super::super::SetupConfig,
    root: &Path,
  ) -> storage::Result<(VerifyingKey<C>, fixed_cache::Prepared)> {
    let setup = self.setup(config)?;
    let height = self.compiled.main_height();
    let cache = fixed_cache::FixedCache::from_identity_for::<C>(
      root,
      &cache_identity(&self.vk, &setup, height)?,
    );
    let (parts, prepared) =
      cache.prepare(&proving_config(&setup, height)?, &self.compiled)?;
    Ok((self.key_from_parts(&parts, &setup)?, prepared))
  }

  /// The frontend identity this circuit's fixed cache is keyed by.
  pub(crate) fn identity(&self) -> &[u8] {
    &self.vk
  }

  fn key_from_parts(
    &self,
    parts: &[prover::FixedSetup<C>],
    setup: &SetupSource<C>,
  ) -> storage::Result<VerifyingKey<C>> {
    let heights = parts
      .iter()
      .map(|(circuit, _)| circuit.preprocessed_height)
      .collect::<Vec<_>>();
    let setup_bytes = parts
      .iter()
      .map(|part| {
        bincode::serde::encode_to_vec(part, bincode::config::standard())
      })
      .collect::<Result<Vec<_>, _>>()?;
    VerifyingKey::new(
      heights.try_into().map_err(|_heights| "expected two partitions")?,
      setup_bytes.try_into().map_err(|_bytes| "expected two partitions")?,
      bincode::serde::encode_to_vec(
        &self.pairings,
        bincode::config::standard(),
      )?,
      setup,
    )
  }

  fn from_built(built: Built<C>, vk: &[u8]) -> storage::Result<Self> {
    Self::new(built.circuit, &built.pairing_keys, vk, MAX_TRACE_LEN)
  }

  pub(crate) fn new(
    circuit: multi_stark::plonkish::Circuit<CurveScalar<C>>,
    keys: &[G2AffineOf<C>],
    vk: &[u8],
    max_height: usize,
  ) -> storage::Result<Self> {
    use ark_serialize::CanonicalSerialize;
    if keys.len() != 2 {
      return Err("invalid recursive pairing keys".into());
    }
    let mut encoded = vec![];
    keys.serialize_compressed(&mut encoded)?;
    let compiled = lowering::lower_recursive::<C>(circuit, max_height)?;
    Ok(Self { compiled, pairings: Pairings { keys: encoded }, vk: vk.to_vec() })
  }

  /// Stage and prove one request, keeping the witness traces in memory.
  /// Fixed preprocessing comes from the cache when it already holds this
  /// verifying key and is published to it after the proof verifies.
  pub(crate) fn stage(
    self,
    assignment: Assignment<CurveScalar<C>>,
    dir: &Path,
    statement: &Statement,
    config: &super::super::StageConfig,
  ) -> storage::Result<()> {
    if assignment.public_values().len() != RECURSIVE_PUBLIC_VALUES
      || assignment.public_values()[..18]
        .iter()
        .zip(statement)
        .any(|(&value, &word)| value != CurveScalar::<C>::from_u64(word))
    {
      return Err(
        "recursive assignment differs from the first stage's statement".into(),
      );
    }
    let start = std::time::Instant::now();
    let height = self.compiled.main_height();
    let setup = self.setup(&config.setup)?;
    fs::create_dir_all(dir)?;
    setup.bind_stage(dir, height, 2)?;
    storage::save(&dir.join("pairings.bin"), &self.pairings)?;
    let cache = config
      .fixed_cache_for::<C>(dir, &cache_identity(&self.vk, &setup, height)?);
    let cached = cache.restore(dir)?;
    let manifest = storage::Manifest::<C>::for_compiled(
      &self.compiled,
      self.compiled.claims(assignment.public_values())?,
      cached.as_ref(),
    )?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    fs::write(dir.join("SECURITY.txt"), setup.security_description())?;
    eprintln!("Recursive staging complete: {:?}", start.elapsed());
    prove(
      dir,
      Lowered { compiled: self.compiled, assignment },
      &cache,
      &setup,
    )?;
    eprintln!("Recursive stage-and-prove complete: {:?}", start.elapsed());
    Ok(())
  }
}

/// The fixed-cache identity of a recursive or merge stage whose verifier
/// frontend is `vk`, under `setup` at computation height `height`.
fn cache_identity<C: KzgCurve>(
  vk: &[u8],
  setup: &SetupSource<C>,
  height: usize,
) -> storage::Result<Vec<u8>> {
  Ok([vk, &setup.identity(height, 2)?].concat())
}

/// The fixed cache under `root` of a recursive or merge stage whose verifier
/// frontend is `vk` and computation height `height`, as `Frontend::stage`
/// keys it.
pub(crate) fn fixed_cache<C: KzgCurve>(
  vk: &[u8],
  height: usize,
  config: &super::super::SetupConfig,
  root: &Path,
) -> storage::Result<fixed_cache::FixedCache> {
  let setup = config
    .for_stage::<C>(C::OUTER_SEED, height)?
    .with_transcript(TranscriptKind::Blake3);
  Ok(fixed_cache::FixedCache::from_identity_for::<C>(
    root,
    &cache_identity(vk, &setup, height)?,
  ))
}

fn pairing_keys<C: KzgCurve>(
  dir: &Path,
) -> storage::Result<Vec<G2AffineOf<C>>> {
  let vk: Pairings = storage::load(&dir.join("pairings.bin"))?;
  decode_pairing_keys::<C>(&vk)
}

fn decode_pairing_keys<C: KzgCurve>(
  vk: &Pairings,
) -> storage::Result<Vec<G2AffineOf<C>>> {
  use ark_ec::AffineRepr;
  use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
  if vk.keys.len() != 8 + 2 * C::G2_COMPRESSED_BYTES
    || vk.keys.get(..8) != Some(&2u64.to_le_bytes())
  {
    return Err("invalid pairing keys".into());
  }
  let mut input = vk.keys.as_slice();
  let keys = Vec::<G2AffineOf<C>>::deserialize_compressed(&mut input)?;
  if !input.is_empty()
    || keys.len() != 2
    || keys.iter().any(AffineRepr::is_zero)
  {
    return Err("invalid pairing keys".into());
  }
  let mut canonical = Vec::new();
  keys.serialize_compressed(&mut canonical)?;
  if canonical != vk.keys {
    return Err("noncanonical pairing keys".into());
  }
  Ok(keys)
}

fn pairing_bytes<C: KzgCurve>(
  publics: &[CurveScalar<C>],
) -> storage::Result<Vec<u8>> {
  recursive::pack_pairings::<C>(publics)
}
fn check_pairings<C: KzgCurve>(
  bytes: &[u8],
  keys: &[G2AffineOf<C>],
) -> storage::Result<()> {
  recursive::Pairings::<C> {
    keys: keys.try_into().map_err(|_keys| "pairing point count")?,
  }
  .verify_bytes(bytes)
}
fn packet_body<'a, C: KzgCurve>(
  packet: &'a [u8],
  vk: &[u8; 32],
  expected: &Statement,
) -> storage::Result<&'a [u8]> {
  let offset = 32 + statement::WORDS * 8;
  let pairing_bytes = 2 * C::G1_COMPRESSED_BYTES;
  if packet.len() < offset + pairing_bytes || packet[..32] != *vk {
    return Err("packet verifying key mismatch".into());
  }
  for (bytes, &word) in
    packet[32..offset].as_chunks::<8>().0.iter().zip(expected)
  {
    if u64::from_le_bytes(*bytes) != word {
      return Err("packet statement differs from the claim's".into());
    }
  }
  Ok(&packet[offset..])
}

#[cfg(any(test, feature = "plonk", feature = "groth16"))]
fn packet_claims<C: KzgCurve>(
  packet: &[u8],
  vk: &[u8; 32],
  pairing_count: usize,
  expected: &Statement,
) -> storage::Result<(Vec<Vec<CurveScalar<C>>>, usize)> {
  if pairing_count != 2 {
    return Err("pairing point count".into());
  }
  let pairing_bytes = 2 * C::G1_COMPRESSED_BYTES;
  let body = packet_body::<C>(packet, vk, expected)?;
  let mut public: Vec<_> =
    expected.iter().copied().map(CurveScalar::<C>::from_u64).collect();
  public.extend(recursive::unpack_pairings::<C>(&body[..pairing_bytes])?);
  let claims =
    ClaimTemplate::<CurveScalar<C>>::recursive(public.len()).claims(&public)?;
  Ok((claims, 32 + statement::WORDS * 8 + pairing_bytes))
}
fn verify_packet<C: KzgCurve>(
  system: &multi_stark::system::System<KzgConfig<C>>,
  codec: &FixedProofCodec<C>,
  packet: &[u8],
  vk: &[u8; 32],
  keys: &[G2AffineOf<C>],
  expected: &Statement,
) -> storage::Result<()> {
  let body = packet_body::<C>(packet, vk, expected)?;
  let pairings = recursive::Pairings::<C> {
    keys: keys.try_into().map_err(|_keys| "pairing point count")?,
  };
  recursive::verify_recursive_bytes(
    system,
    codec,
    &ClaimTemplate::<CurveScalar<C>>::recursive(RECURSIVE_PUBLIC_VALUES),
    &pairings,
    body,
    &expected
      .iter()
      .copied()
      .map(CurveScalar::<C>::from_u64)
      .collect::<Vec<_>>(),
  )
}

fn staged_publics<C: KzgCurve>(
  claims: &[Vec<CurveScalar<C>>],
  pairing_count: usize,
) -> storage::Result<Vec<CurveScalar<C>>> {
  if pairing_count != 2 {
    return Err("pairing point count".into());
  }
  ClaimTemplate::<CurveScalar<C>>::recursive(RECURSIVE_PUBLIC_VALUES)
    .public_values(claims)
}

/// The KZG configuration the recursive stage commits and proves under.
fn proving_config<C: KzgCurve>(
  setup: &SetupSource<C>,
  height: usize,
) -> storage::Result<KzgConfig<C>> {
  Ok(
    setup
      .config(height, 2, false)?
      .with_streaming_lookups()
      .with_streaming_quotient(),
  )
}

/// Commit the fixed and witness traces from memory, prove, verify the
/// packet and write it with the portable verifier. Fixed columns are
/// checkpointed because every proof of the verifying key shares them through the
/// cache; witness columns never touch disk.
fn prove<C: KzgCurve>(
  dir: &Path,
  lowered: Lowered<C>,
  cache: &fixed_cache::FixedCache,
  setup: &SetupSource<C>,
) -> storage::Result<()> {
  use multi_stark::config::ProofConfig;
  use std::time::Instant;
  let start = Instant::now();
  let manifest: storage::Manifest<C> =
    storage::load(&dir.join("manifest.bin"))?;
  if manifest.heights.len() != 2
    || manifest.widths.len() != 2
    || manifest.widths[0] != 3
    || manifest.widths[1] != 1
    || manifest.heights.iter().any(|h| {
      *h < 2
        || !h.is_power_of_two()
        || *h > 1 << 28
        || h.ilog2() as usize >= CurveScalar::<C>::TWO_ADICITY
    })
    || manifest.heights[1] > manifest.heights[0]
  {
    return Err("expected one computation trace and one merged table".into());
  }
  let count = manifest.heights.len();
  let height = manifest.heights[0];
  let compiled = &lowered.compiled;
  if compiled.num_circuits() != count
    || compiled.main_heights() != [height]
    || (0..count).any(|i| {
      compiled.trace_dimensions(i)
        != Some((manifest.heights[i], manifest.widths[i]))
    })
  {
    return Err(
      "compiled trace dimensions differ from the staged manifest".into(),
    );
  }
  let keys = pairing_keys::<C>(dir)?;
  let publics = staged_publics::<C>(&manifest.claims, keys.len())?;
  let point_bytes = pairing_bytes::<C>(&publics[18..])?;
  check_pairings::<C>(&point_bytes, &keys)?;
  let statement = statement::from_scalars(&publics[..18])?;
  let out = dir.join("kzg");
  fs::create_dir_all(&out)?;
  eprintln!("Preparing KZG parameters for 2^{} rows", height.ilog2());
  setup.check_binding(dir, height, 2)?;
  fs::write(out.join("SECURITY.txt"), setup.security_description())?;
  let setup_id = setup.identity(height, 2)?;
  let config_started = Instant::now();
  let mut config = proving_config(setup, height)?;
  if let Some(spill_dir) = KzgConfig::<C>::resolve_disk_spill_dir(&out)? {
    config = config.with_disk_spill(spill_dir);
  }
  let srs_config_load_seconds = config_started.elapsed().as_secs_f64();
  eprintln!("Outer KZG parameters ready: {:?}", start.elapsed());
  let fixed = cache.fixed_directory(dir)?;
  let prover::Proved { system, codec, bytes, .. } =
    lowered.commit(config, Some(&fixed), 0)?.prove(&manifest.claims)?;
  let output_span = tracing::info_span!("compression/write_output").entered();
  let verifier = VerifyingKey::<C>::new(
    [manifest.heights[0], manifest.heights[1]],
    [fs::read(out.join("setup-0.bin"))?, fs::read(out.join("setup-1.bin"))?],
    fs::read(dir.join("pairings.bin"))?,
    setup,
  )?;
  let vk = verifier.id();
  let mut packet = vk.to_vec();
  for word in statement {
    packet.extend(word.to_le_bytes());
  }
  packet.extend(point_bytes);
  packet.extend(&bytes);
  if packet.len() >= 3_000 {
    return Err(
      "final public-degree proof packet must be smaller than 3000 bytes".into(),
    );
  }
  let verify_start = Instant::now();
  tracing::info_span!("compression/verify_packet").in_scope(|| {
    verify_packet(&system, &codec, &packet, &vk, &keys, &statement)
  })?;
  let verify_seconds = verify_start.elapsed().as_secs_f64();
  let encoded = verifier.to_bytes()?;
  storage::write_atomic(&out.join("proof.compact.bin"), &bytes)?;
  storage::write_atomic(&dir.join("vk.bin"), &encoded)?;
  storage::write_atomic(&out.join("vk-id.bin"), &vk)?;
  storage::write_atomic(&out.join("packet.bin"), &packet)?;
  let public_setup = system.config.pcs().verifier_params().public_setup();
  let development = setup.class() == SetupClass::Development;
  let report = serde_json::json!({
    "curve": C::NAME,
    "proof_bytes": bytes.len(),
    "packet_bytes": packet.len(),
    "claim_bytes": 144,
    "pairing_bytes": 2 * C::G1_COMPRESSED_BYTES,
    "vk_bytes": 32,
    "vk_version": C::OUTER_VK_VERSION,
    "transcript": "blake3",
    "total_seconds": start.elapsed().as_secs_f64(),
    "verify_seconds": verify_seconds,
    "srs_config_load_seconds": srs_config_load_seconds,
    "native_verification_passed": true,
    "external_pairings_pass": true,
    "development_srs": development,
    "known_trapdoor": development,
    "setup": setup.class().label(),
    "public_setup_id": blake3::Hash::from_bytes(public_setup.id).to_hex().to_string(),
    "public_max_degree": public_setup.max_degree,
    "setup_id": blake3::Hash::from_bytes(setup_id).to_hex().to_string(),
    "vk_id": blake3::Hash::from_bytes(vk).to_hex().to_string(),
    "trace_heights": manifest.heights,
  });
  fs::write(
    out.join("prove-report.json"),
    serde_json::to_vec_pretty(&report)?,
  )?;
  eprintln!("{}", serde_json::to_string_pretty(&report)?);
  drop(output_span);
  cache.publish::<C>(dir)?;
  Ok(())
}

/// Recursive verifier metadata authenticated by a bundle or an independent digest.
#[derive(serde::Serialize, serde::Deserialize)]
#[serde(bound = "")]
pub(crate) struct VerifyingKey<C: KzgCurve = Bn254> {
  version: u32,
  heights: [usize; 2],
  setup: [Vec<u8>; 2],
  pairings: Vec<u8>,
  parameters: Vec<u8>,
  #[serde(skip)]
  _curve: PhantomData<C>,
}

fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> storage::Result<T> {
  if bytes.len() > 1 << 20 {
    return Err("verifying key too large".into());
  }
  let (value, consumed) = bincode::serde::decode_from_slice(
    bytes,
    bincode::config::standard().with_limit::<{ 1 << 20 }>(),
  )?;
  if consumed != bytes.len() {
    return Err("trailing verifying key bytes".into());
  }
  Ok(value)
}

impl<C: KzgCurve> VerifyingKey<C> {
  /// The key of a recursive circuit whose two partitions have `heights` and
  /// encoded fixed setups `setup`, proved under `source`.
  fn new(
    heights: [usize; 2],
    setup: [Vec<u8>; 2],
    pairings: Vec<u8>,
    source: &SetupSource<C>,
  ) -> storage::Result<Self> {
    Ok(Self {
      version: C::OUTER_VK_VERSION,
      heights,
      setup,
      pairings,
      parameters: source.verifier_params(heights[0])?.to_bytes()?,
      _curve: PhantomData,
    })
  }

  pub(crate) fn to_bytes(&self) -> storage::Result<Vec<u8>> {
    Ok(bincode::serde::encode_to_vec(self, bincode::config::standard())?)
  }

  pub(crate) fn from_bytes(bytes: &[u8]) -> PipelineResult<Self> {
    Ok(Self::prepared_from_bytes(bytes)?.0)
  }

  /// Decode a key and its prepared verifier, preparing it once.
  pub(crate) fn prepared_from_bytes(
    bytes: &[u8],
  ) -> PipelineResult<(Self, PreparedVerifyingKey<C>)> {
    let vk: Self = decode(bytes)?;
    let prepared = vk.prepare()?;
    Ok((vk, prepared))
  }

  pub(crate) fn id(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    // The label predates the verifying-key naming and is part of every
    // published id; changing it would re-key every bundled verifying key.
    let namespace = C::OUTER_VK_NAMESPACE;
    hash.update(format!("{namespace}/v{}", self.version).as_bytes());
    hash.update(C::OUTER_SEED);
    hash.update(&self.parameters);
    hash.update(&(self.heights[0] as u64).to_le_bytes());
    for setup in &self.setup {
      hash.update(setup);
    }
    hash.update(&self.pairings);
    *hash.finalize().as_bytes()
  }

  fn keys(&self) -> storage::Result<Vec<G2AffineOf<C>>> {
    decode_pairing_keys::<C>(&decode(&self.pairings)?)
  }

  /// The verifier parameters the verifying key carries.
  pub(crate) fn verifier_params(
    &self,
  ) -> storage::Result<crate::kzg::VerifierParams<C>> {
    Ok(crate::kzg::VerifierParams::<C>::from_bytes(&self.parameters)?)
  }

  /// Setup classification covers both the outer proof and the deferred
  /// inner opening equation. Development stages may use different seeds.
  pub(crate) fn check_setup_class(
    &self,
    expected: SetupClass,
  ) -> PipelineResult<()> {
    let parameters = self.verifier_params()?;
    if SetupClass::of(&parameters) != expected {
      return Err("verifier setup class differs".into());
    }
    if matches!(expected, SetupClass::Ignition | SetupClass::Filecoin)
      && self.keys()? != [parameters.g2, parameters.tau_g2]
    {
      return Err(
        "ceremony verifier has different inner pairing anchors".into(),
      );
    }
    Ok(())
  }

  pub(crate) fn system(
    &self,
  ) -> storage::Result<multi_stark::system::System<KzgConfig<C>>> {
    use crate::kzg::VerifierParams;
    use multi_stark::system::{Circuit, System};
    let supported = self.version == C::OUTER_VK_VERSION;
    if !supported {
      return Err("unsupported recursive verifying key".into());
    }
    if self
      .heights
      .iter()
      .any(|h| *h < 2 || !h.is_power_of_two() || *h > 1 << 28)
      || self.heights[1] > self.heights[0]
    {
      return Err("unsupported recursive verifying key".into());
    }
    let params = VerifierParams::<C>::from_bytes(&self.parameters)?;
    if params.max_trace_len() != self.heights[0] {
      return Err("verifier SRS range mismatch".into());
    }
    if params.max_trace_len().ilog2() as usize >= CurveScalar::<C>::TWO_ADICITY
    {
      return Err(
        "trace and quotient domains exceed scalar two-adicity".into(),
      );
    }
    let mut circuits = vec![];
    let mut fixed = KzgCommitment::<C>(vec![]);
    for (i, bytes) in self.setup.iter().enumerate() {
      let (circuit, mut commit): (Circuit<CurveScalar<C>>, KzgCommitment<C>) =
        decode(bytes)?;
      if circuit.main_width != [3, 1][i]
        || circuit.preprocessed_height != self.heights[i]
      {
        return Err("setup shape mismatch".into());
      }
      circuits.push(circuit);
      fixed.0.append(&mut commit.0);
    }
    let mut system = System {
      config: KzgConfig::<C>::verifier_only(params, 2)
        .with_transcript(TranscriptKind::Blake3),
      circuits,
      preprocessed_commit: Some(fixed),
      preprocessed_indices: vec![Some(0), Some(1)],
      vk_digest: [0u8; 32],
    };
    crate::kzg::config::bind_system_key(&mut system);
    Ok(system)
  }

  pub(crate) fn prepare(&self) -> PipelineResult<PreparedVerifyingKey<C>> {
    Ok(PreparedVerifyingKey {
      id: self.id(),
      verifier: RecursiveVerifier::<C>::from_parts(
        self.system()?,
        ClaimTemplate::<CurveScalar<C>>::recursive(RECURSIVE_PUBLIC_VALUES),
        &self.keys()?,
        18,
      )?,
    })
  }

  pub(crate) fn verify(
    &self,
    packet: &[u8],
    expected: &Statement,
  ) -> PipelineResult<()> {
    self.prepare()?.verify(packet, expected)
  }
}

pub(crate) struct PreparedVerifyingKey<C: KzgCurve = Bn254> {
  id: [u8; 32],
  verifier: RecursiveVerifier<C>,
}

impl<C: KzgCurve> PreparedVerifyingKey<C> {
  pub(crate) fn verify(
    &self,
    packet: &[u8],
    expected: &Statement,
  ) -> PipelineResult<()> {
    let body = packet_body::<C>(packet, &self.id, expected)?;
    self.verifier.verify_scalar_bytes(
      body,
      &expected
        .iter()
        .copied()
        .map(CurveScalar::<C>::from_u64)
        .collect::<Vec<_>>(),
    )
  }
}

/// Verify a packet against the stage's portable verifier. Without an
/// independently derived statement, the one the stage's own claim rows
/// carry is used, so the check covers the proof but not the claim binding.
#[cfg(test)]
pub(crate) fn verify_saved<C: KzgCurve>(
  dir: &Path,
  packet: &[u8],
  expected: Option<&Statement>,
) -> PipelineResult<()> {
  let staged;
  let expected = match expected {
    Some(expected) => expected,
    None => {
      let manifest: storage::Manifest<C> =
        storage::load(&dir.join("manifest.bin"))?;
      staged = statement::from_rows(&manifest.claims)?;
      &staged
    },
  };
  VerifyingKey::<C>::from_bytes(&fs::read(dir.join("vk.bin"))?)?
    .verify(packet, expected)
}

#[cfg(test)]
mod tests {
  use super::super::super::init_fri::INIT_PUBLIC_WORDS;
  use super::*;
  use crate::{
    foreign::KzgCircuitExt,
    kzg::{Scalar, Srs, curve::Bls12381},
    test_support::TempDir,
  };
  use ark_ec::CurveGroup;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::{
    plonkish::CircuitBuilder,
    system::{System, SystemWitness},
    traits::Algebra,
  };
  use std::sync::Arc;

  fn recursive_vk_fixture_for<C: KzgCurve>()
  -> storage::Result<(VerifyingKey<C>, Vec<u8>)> {
    use crate::kzg::VerifierParams;
    let srs = Srs::<C>::unsafe_dev_setup(256, b"recursive-verifier-fixture");
    let pairing_keys = [srs.g2, srs.tau_g2];
    let claims = init_packet_claims_for::<C>(&srs);
    let publics = staged_publics::<C>(&claims, 2)?;
    let mut builder = CircuitBuilder::new();
    let table = builder.fixed_table(
      "small",
      vec![vec![CurveScalar::<C>::ONE], vec![CurveScalar::<C>::TWO]],
    );
    let one = builder.constant(CurveScalar::<C>::ONE);
    builder.lookup(table, &[one]);
    for claim in &claims[1..] {
      let value = builder.constant(claim[3]);
      builder.expose_public(value);
    }
    let compiled = builder
      .finish()
      .lower_to_multi_stark_sharded(CurveScalar::<C>::from_u8(94), 128)?
      .merge_table_traces(128)?;
    let assignment = compiled.witness().generate()?;
    let height = compiled.main_height();
    let parameters = VerifierParams::<C>::with_max_trace_len(&srs, height);
    let config = KzgConfig::<C>::with_max_trace_len(Arc::new(srs), height, 2)
      .with_transcript(TranscriptKind::Blake3)
      .with_streaming_lookups()
      .with_streaming_quotient();
    let proved = Lowered { compiled, assignment }
      .commit(config, None, 0)?
      .prove(&claims)?;
    assert_eq!(proved.system.circuits.len(), 2);
    let fixed = proved.system.preprocessed_commit.as_ref().unwrap();
    let encode_setup = |index: usize| -> storage::Result<Vec<u8>> {
      Ok(bincode::serde::encode_to_vec(
        (
          &proved.system.circuits[index],
          KzgCommitment::<C>(vec![fixed.0[index].clone()]),
        ),
        bincode::config::standard(),
      )?)
    };
    let mut keys = Vec::new();
    pairing_keys.to_vec().serialize_compressed(&mut keys)?;
    let vk = VerifyingKey::<C> {
      version: C::OUTER_VK_VERSION,
      heights: [
        proved.system.circuits[0].preprocessed_height,
        proved.system.circuits[1].preprocessed_height,
      ],
      setup: [encode_setup(0)?, encode_setup(1)?],
      pairings: bincode::serde::encode_to_vec(
        Pairings { keys },
        bincode::config::standard(),
      )?,
      parameters: parameters.to_bytes()?,
      _curve: PhantomData,
    };
    let mut packet = vk.id().to_vec();
    for word in INIT_PUBLIC_WORDS {
      packet.extend(word.to_le_bytes());
    }
    packet.extend(pairing_bytes::<C>(&publics[18..])?);
    packet.extend(&proved.bytes);
    Ok((vk, packet))
  }

  fn recursive_vk_fixture() -> storage::Result<(VerifyingKey, Vec<u8>)> {
    recursive_vk_fixture_for::<Bn254>()
  }

  #[test]
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  fn plonk_recursive_export_includes_anchor_and_deferred_publics()
  -> storage::Result<()> {
    let (vk, packet) = recursive_vk_fixture()?;
    let expected = INIT_PUBLIC_WORDS;
    let directory = TempDir::new("plonk-recursive-claims");
    final_export::write_export(
      &vk, &packet, &expected, &directory, "witness", true,
    )?;
    let exported: serde_json::Value =
      serde_json::from_slice(&fs::read(directory.join("vk.json"))?)?;
    assert_eq!(exported["format"], Bn254::PLONK_VK_FORMAT);
    let claims = exported["claims"].as_array().unwrap();
    assert_eq!(claims.len(), 23);
    assert_eq!(exported["publics"].as_array().unwrap().len(), 23);
    for (index, claim) in claims.iter().enumerate() {
      assert_eq!(claim[3]["public"], index);
    }
    assert_eq!(exported["publics"][22]["deferredHalf"], 3);
    let witness: serde_json::Value =
      serde_json::from_slice(&fs::read(directory.join("witness.json"))?)?;
    assert_eq!(witness["deferred"].as_array().unwrap().len(), 2);
    let mut wrong = expected;
    wrong[10] ^= 1;
    assert!(
      final_export::write_export(
        &vk, &packet, &wrong, &directory, "wrong", true,
      )
      .is_err()
    );
    Ok(())
  }

  #[test]
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  fn bls12_381_plonk_recursive_export_and_vk_round_trip() -> storage::Result<()>
  {
    let (vk, packet) = recursive_vk_fixture_for::<Bls12381>()?;
    let expected = INIT_PUBLIC_WORDS;
    let encoded = vk.to_bytes()?;
    let decoded = VerifyingKey::<Bls12381>::from_bytes(&encoded)?;
    decoded.verify(&packet, &expected)?;
    let directory = TempDir::new("bls12-381-plonk-recursive-claims");
    final_export::write_export(
      &vk, &packet, &expected, &directory, "witness", true,
    )?;
    let exported: serde_json::Value =
      serde_json::from_slice(&fs::read(directory.join("vk.json"))?)?;
    assert_eq!(exported["format"], Bls12381::PLONK_VK_FORMAT);
    assert_eq!(exported["outerKeys"][0].as_str().unwrap().len(), 2 + 96 * 2);
    assert_eq!(exported["deferredKeys"][0].as_str().unwrap().len(), 2 + 96 * 2);
    let witness: serde_json::Value =
      serde_json::from_slice(&fs::read(directory.join("witness.json"))?)?;
    assert_eq!(witness["deferred"].as_array().unwrap().len(), 2);
    Ok(())
  }

  #[test]
  fn ignition_staging_rejects_other_inner_keys_before_creating_files()
  -> storage::Result<()> {
    use crate::pipeline::{StageConfig, setup::SetupConfig};
    let inner = Srs::unsafe_dev_setup(2, b"ignition-stage-development-inner");
    let claims = init_packet_claims(&inner);
    let mut builder = CircuitBuilder::new();
    let table =
      builder.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
    let one = builder.constant(Scalar::ONE);
    builder.lookup(table, &[one]);
    for claim in &claims[1..] {
      let value = builder.constant(claim[3]);
      builder.expose_public(value);
    }
    let circuit = builder.finish();
    let assignment = circuit.witness().generate()?;
    let frontend = Frontend::<Bn254>::new(
      circuit,
      &[inner.g2, inner.tau_g2],
      b"ignition-stage-anchors",
      128,
    )?;
    let scratch = TempDir::new("ignition-stage-anchors");
    let root = scratch.join("stage");
    assert!(!root.exists());
    let config = StageConfig {
      setup: SetupConfig::Ignition { srs: root.join("absent-srs.bin") },
      fixed_cache_root: None,
      prefetch_bytes: 0,
    };
    let error = frontend
      .stage(assignment, &root, &INIT_PUBLIC_WORDS, &config)
      .unwrap_err();
    assert!(error.to_string().contains("inner pairing anchors differ"));
    assert!(!root.exists());
    Ok(())
  }

  #[test]
  fn pinned_recursive_key_binds_claim_and_rejects_tampering()
  -> storage::Result<()> {
    use super::super::super::verifying_keys::verify_with_vk;
    let (vk, packet) = recursive_vk_fixture()?;
    let claim = include_bytes!("../../../tests/fixtures/init-fri/claim.bin");
    let expected = INIT_PUBLIC_WORDS;
    let portable = vk.to_bytes()?;
    let trusted = *blake3::hash(&portable).as_bytes();
    let verify =
      |packet: &[u8], claim: &[u8], expected: &_, pin: &_, development| {
        verify_with_vk(packet, claim, expected, &portable, pin, development)
      };
    assert_eq!(
      verify(&packet, claim, &expected, &trusted, true)?,
      SetupClass::Development
    );
    assert!(verify(&packet, claim, &expected, &trusted, false).is_err());
    assert!(verify(&packet, claim, &expected, &[0; 32], true).is_err());
    assert!(verify(&packet, b"wrong", &expected, &trusted, true).is_err());
    let mut wrong_statement = expected;
    wrong_statement[0] ^= 1;
    assert!(verify(&packet, claim, &wrong_statement, &trusted, true).is_err());
    let mut bad_packet = packet;
    *bad_packet.last_mut().unwrap() ^= 1;
    assert!(verify(&bad_packet, claim, &expected, &trusted, true).is_err());
    Ok(())
  }

  #[test]
  fn ignition_verifier_rejects_substituted_inner_pairing_keys()
  -> storage::Result<()> {
    let mut vk = VerifyingKey::<Bn254>::from_bytes(include_bytes!(
      "../../../verifying-keys/0.5/recursive-vk.bin"
    ))?;
    vk.check_setup_class(SetupClass::Ignition)?;
    let development =
      Srs::<Bn254>::unsafe_dev_setup(2, b"substituted-inner-keys");
    let mut keys = Vec::new();
    vec![development.g2, development.tau_g2].serialize_compressed(&mut keys)?;
    vk.pairings = bincode::serde::encode_to_vec(
      Pairings { keys },
      bincode::config::standard(),
    )?;
    assert!(vk.check_setup_class(SetupClass::Ignition).is_err());
    Ok(())
  }

  #[test]
  fn packet_requires_outer_proof_claim_and_external_pairings() {
    let inner = Srs::<Bn254>::unsafe_dev_setup(8, b"packet-inner");
    let keys = vec![inner.g2, inner.tau_g2];
    let vk = [17u8; 32];
    let packet_prefix = |wrong: bool| {
      let mut packet = vk.to_vec();
      for v in INIT_PUBLIC_WORDS {
        packet.extend(v.to_le_bytes());
      }
      let lhs = if wrong {
        (inner.g1[1] * crate::kzg::curve::Fr::from(2u8)).into_affine()
      } else {
        inner.g1[1]
      };
      lhs.serialize_compressed(&mut packet).unwrap();
      (-inner.g1[0]).serialize_compressed(&mut packet).unwrap();
      packet
    };
    let (claims, _) =
      packet_claims::<Bn254>(&packet_prefix(false), &vk, 2, &INIT_PUBLIC_WORDS)
        .unwrap();
    let mut b = CircuitBuilder::new();
    let inputs: Vec<_> = (1..claims.len())
      .map(|i| {
        let v = b.input(format!("public{i}"));
        b.expose_public(v);
        v
      })
      .collect();
    let circuit = b.finish();
    let lowered = circuit.lower_to_multi_stark(Scalar::from_u8(94)).unwrap();
    let config =
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(64, b"packet-outer")), 2)
        .with_transcript(TranscriptKind::Blake3);
    let (system, key) =
      System::new(config, lowered.kzg_circuit_inputs(64, 2).unwrap());
    let codec = FixedProofCodec::new(
      &system,
      &[u8::try_from(system.circuits[0].preprocessed_height.ilog2()).unwrap()],
    )
    .unwrap();
    for wrong in [false, true] {
      let mut packet = packet_prefix(wrong);
      let (claims, _) =
        packet_claims::<Bn254>(&packet, &vk, 2, &INIT_PUBLIC_WORDS).unwrap();
      let mut w = lowered.witness();
      for (&input, claim) in inputs.iter().zip(&claims[1..]) {
        w.set(input, claim[3]).unwrap();
      }
      let a = w.generate().unwrap();
      let proof = system.prove_multiple_claims(
        &key,
        &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        SystemWitness::from_stage_1(lowered.traces(&a).unwrap(), &system),
      );
      packet.extend(codec.encode(&proof).unwrap());
      assert_eq!(
        verify_packet(&system, &codec, &packet, &vk, &keys, &INIT_PUBLIC_WORDS)
          .is_ok(),
        !wrong
      );
      if !wrong {
        let mut changed = packet.clone();
        changed[32 + 8] ^= 1;
        assert!(
          verify_packet(
            &system,
            &codec,
            &changed,
            &vk,
            &keys,
            &INIT_PUBLIC_WORDS
          )
          .is_err()
        );
        let mut changed_claims = claims.clone();
        changed_claims[2][3] += Scalar::ONE;
        assert!(
          system
            .verify_multiple_claims(
              &changed_claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
              &proof
            )
            .is_err()
        );
        assert!(
          verify_packet(
            &system,
            &codec,
            &packet[..packet.len() - 1],
            &vk,
            &keys,
            &INIT_PUBLIC_WORDS
          )
          .is_err()
        );
        packet.push(0);
        assert!(
          verify_packet(
            &system,
            &codec,
            &packet,
            &vk,
            &keys,
            &INIT_PUBLIC_WORDS
          )
          .is_err()
        );
      }
    }
  }

  fn init_packet_claims_for<C: KzgCurve>(
    inner: &Srs<C>,
  ) -> Vec<Vec<CurveScalar<C>>> {
    let mut prefix = [0u8; 32].to_vec();
    for word in INIT_PUBLIC_WORDS {
      prefix.extend(word.to_le_bytes());
    }
    inner.g1[1].serialize_compressed(&mut prefix).unwrap();
    (-inner.g1[0]).serialize_compressed(&mut prefix).unwrap();
    packet_claims::<C>(&prefix, &[0u8; 32], 2, &INIT_PUBLIC_WORDS).unwrap().0
  }

  fn init_packet_claims(inner: &Srs) -> Vec<Vec<Scalar>> {
    init_packet_claims_for::<Bn254>(inner)
  }

  /// Stage a compiled fixture's metadata the way `Frontend::stage` does.
  fn stage_fixture<C: KzgCurve>(
    dir: &Path,
    cache_root: &Path,
    compiled: &MultiStarkCircuit<CurveScalar<C>>,
    assignment: &Assignment<CurveScalar<C>>,
    keys: &[G2AffineOf<C>],
  ) -> storage::Result<fixed_cache::FixedCache> {
    fs::create_dir_all(dir)?;
    let height = compiled.main_height();
    SetupSource::<C>::development(C::OUTER_SEED, height - 1)?
      .with_transcript(TranscriptKind::Blake3)
      .bind_stage(dir, height, 2)?;
    let mut encoded = vec![];
    keys.serialize_compressed(&mut encoded)?;
    storage::save(&dir.join("pairings.bin"), &Pairings { keys: encoded })?;
    let cache =
      fixed_cache::FixedCache::from_identity_for::<C>(cache_root, b"outer");
    let cached = cache.restore(dir)?;
    let manifest = storage::Manifest::<C>::for_compiled(
      compiled,
      compiled.claims(assignment.public_values())?,
      cached.as_ref(),
    )?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    Ok(cache)
  }

  #[test]
  fn fused_vks_prove_and_portable_verifiers_round_trip() -> storage::Result<()>
  {
    let dir = TempDir::new("outer-staged");
    let inner = Srs::unsafe_dev_setup(8, b"staged-inner");
    let keys = vec![inner.g2, inner.tau_g2];
    let claims = init_packet_claims(&inner);
    let make = || -> storage::Result<Lowered> {
      let mut b = CircuitBuilder::new();
      let table =
        b.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
      let one = b.constant(Scalar::ONE);
      b.lookup(table, &[one]);
      for claim in &claims[1..] {
        let value = b.constant(claim[3]);
        b.expose_public(value);
      }
      let compiled = b
        .finish()
        .lower_to_multi_stark_sharded(Scalar::from_u8(94), 128)?
        .merge_table_traces(128)?;
      let assignment = compiled.witness().generate()?;
      Ok(Lowered { compiled, assignment })
    };
    let Lowered { compiled, assignment } = make()?;
    let height = compiled.main_height();
    let first = dir.join("first");
    let cache_root = dir.join("cache");
    let cache =
      stage_fixture(&first, &cache_root, &compiled, &assignment, &keys)?;
    let manifest: storage::Manifest =
      storage::load(&first.join("manifest.bin"))?;
    assert_eq!(manifest.claims, claims);
    let setup = SetupSource::<Bn254>::development(OUTER_SEED, height - 1)?
      .with_transcript(TranscriptKind::Blake3);
    prove(&first, Lowered { compiled, assignment }, &cache, &setup)?;
    assert!(first.join("kzg/setup-0.bin").exists());
    assert!(!first.join("kzg/fixed-0.bin").exists());
    assert!(!first.join("kzg/main-0.bin").exists());
    let packet = fs::read(first.join("kzg/packet.bin"))?;
    verify_saved::<Bn254>(&first, &packet, None)?;
    for offset in [0, 32, packet.len() - 1] {
      let mut bad = packet.clone();
      bad[offset] ^= 1;
      assert!(verify_saved::<Bn254>(&first, &bad, None).is_err());
    }
    assert!(
      verify_saved::<Bn254>(&first, &packet[..packet.len() - 1], None).is_err()
    );
    let mut extra = packet.clone();
    extra.push(0);
    assert!(verify_saved::<Bn254>(&first, &extra, None).is_err());
    // A second run of the verifying key restores the fixed preprocessing from
    // the cache and produces the same packet.
    let second = dir.join("second");
    let Lowered { compiled, assignment } = make()?;
    let cache =
      stage_fixture(&second, &cache_root, &compiled, &assignment, &keys)?;
    assert!(second.join("kzg/setup-0.bin").exists());
    assert!(!second.join("kzg/fixed-0.bin").exists());
    prove(&second, Lowered { compiled, assignment }, &cache, &setup)?;
    assert_eq!(packet, fs::read(second.join("kzg/packet.bin"))?);
    for (row, col) in [(0, 3), (1, 0), (1, 1), (1, 2)] {
      let mut bad = claims.clone();
      bad[row][col] += Scalar::ONE;
      assert!(staged_publics(&bad, keys.len()).is_err());
    }
    let mut bad = claims.clone();
    bad[1].pop();
    assert!(staged_publics(&bad, keys.len()).is_err());
    assert!(staged_publics(&claims[..claims.len() - 1], keys.len()).is_err());
    let portable = fs::read(first.join("vk.bin"))?;
    let claim = include_bytes!("../../../tests/fixtures/init-fri/claim.bin");
    let trusted = *blake3::hash(&portable).as_bytes();
    let verify_local = |claim: &[u8], expected, trusted: &[u8; 32], allow| {
      super::super::super::verifying_keys::verify_with_vk(
        &packet, claim, expected, &portable, trusted, allow,
      )
    };
    assert_eq!(
      verify_local(claim, &INIT_PUBLIC_WORDS, &trusted, true)?,
      SetupClass::Development
    );
    assert!(verify_local(claim, &INIT_PUBLIC_WORDS, &trusted, false).is_err());
    let mut wrong_digest = trusted;
    wrong_digest[0] ^= 1;
    assert!(
      verify_local(claim, &INIT_PUBLIC_WORDS, &wrong_digest, true).is_err()
    );
    assert!(
      verify_local(b"wrong", &INIT_PUBLIC_WORDS, &trusted, true).is_err()
    );
    let mut wrong_program = INIT_PUBLIC_WORDS;
    wrong_program[0] ^= 1;
    assert!(verify_local(claim, &wrong_program, &trusted, true).is_err());
    let vk = VerifyingKey::<Bn254>::from_bytes(&portable)?;
    assert_eq!(vk.version, Bn254::OUTER_VK_VERSION);
    assert_eq!(vk.system()?.config.transcript_kind(), TranscriptKind::Blake3);

    let unsupported_versions = [0, 5, 6];
    for version in unsupported_versions {
      let mut unsupported: VerifyingKey = decode(&portable)?;
      unsupported.version = version;
      let unsupported = bincode::serde::encode_to_vec(
        &unsupported,
        bincode::config::standard(),
      )?;
      assert!(VerifyingKey::<Bn254>::from_bytes(&unsupported).is_err());
    }

    // Verify using only the portable object after deleting the SRS and all checkpoints.
    fs::remove_dir_all(&dir)?;
    vk.verify(&packet, &INIT_PUBLIC_WORDS)?;
    let mut wrong_range: VerifyingKey = decode(&portable)?;
    wrong_range.heights[0] *= 2;
    assert!(wrong_range.system().is_err());
    {
      let max_domain = 1usize << Scalar::TWO_ADICITY;
      let anchors = Srs::<Bn254>::unsafe_dev_setup_prefix(
        2,
        max_domain - 1,
        b"outer-domain-cap",
      );
      let params =
        crate::kzg::VerifierParams::with_max_trace_len(&anchors, max_domain);
      let mut oversized: VerifyingKey = decode(&portable)?;
      oversized.heights = [max_domain; 2];
      oversized.parameters = params.to_bytes()?;
      for setup in &mut oversized.setup {
        let (mut circuit, fixed): (
          multi_stark::system::Circuit<Scalar>,
          KzgCommitment,
        ) = decode(setup)?;
        circuit.preprocessed_height = max_domain;
        *setup = bincode::serde::encode_to_vec(
          (circuit, fixed),
          bincode::config::standard(),
        )?;
      }
      let bytes =
        bincode::serde::encode_to_vec(oversized, bincode::config::standard())?;
      let error = VerifyingKey::<Bn254>::from_bytes(&bytes).err().unwrap();
      assert!(error.to_string().contains("quotient domains exceed"));
    }
    Ok(())
  }

  #[test]
  fn fused_recursive_traces_prove_and_report() -> storage::Result<()> {
    let inner = Srs::unsafe_dev_setup(8, b"fused-recursive-inner");
    let claims = init_packet_claims(&inner);
    let make = |private| -> storage::Result<(Built, Assignment<Scalar>)> {
      let mut builder = CircuitBuilder::new();
      let input = builder.input("private");
      let table = builder.fixed_table(
        "small",
        (0..16).map(|v| vec![Scalar::from_u8(v)]).collect(),
      );
      builder.lookup(table, &[input]);
      for _ in 0..8 {
        builder.mul(input, input);
      }
      for claim in &claims[1..] {
        let wire = builder.constant(claim[3]);
        builder.expose_public(wire);
      }
      let circuit = builder.finish();
      let mut witness = circuit.witness();
      witness.set(input, Scalar::from_u8(private))?;
      let assignment = witness.generate()?;
      Ok((
        Built {
          circuit,
          inputs: vec![],
          points: vec![],
          pairing_outputs: vec![],
          pairing_keys: vec![inner.g2, inner.tau_g2],
          msm_terms: vec![],
          terms: vec![],
        },
        assignment,
      ))
    };
    let root = TempDir::new("kzg-recursive-fused");
    let mut outputs = vec![];
    for (name, private) in [("first", 7), ("same", 7), ("other", 9)] {
      let dir = root.join(name);
      fs::create_dir(&dir)?;
      let (built, assignment) = make(private)?;
      stage(
        built,
        assignment,
        &dir,
        b"recursive-fixture",
        &INIT_PUBLIC_WORDS,
        &crate::pipeline::StageConfig::development(),
      )?;
      let report: serde_json::Value =
        serde_json::from_slice(&fs::read(dir.join("kzg/prove-report.json"))?)?;
      assert_eq!(report["setup"], "development");
      assert_eq!(report["development_srs"], true);
      assert_eq!(report["native_verification_passed"], true);
      assert!(report["public_max_degree"].is_u64());
      assert_eq!(report["trace_heights"].as_array().unwrap().len(), 2);
      let manifest: storage::Manifest =
        storage::load(&dir.join("manifest.bin"))?;
      for i in 0..manifest.heights.len() {
        assert!(!dir.join(format!("kzg/main-{i}.bin")).exists());
        assert!(dir.join(format!("kzg/setup-{i}.bin")).exists());
        assert!(!dir.join(format!("kzg/fixed-{i}.bin")).exists());
      }
      let packet = fs::read(dir.join("kzg/packet.bin"))?;
      verify_saved::<Bn254>(&dir, &packet, None)?;
      outputs.push(
        ["proof.compact.bin", "packet.bin", "vk-id.bin"]
          .map(|name| fs::read(dir.join("kzg").join(name)).unwrap()),
      );
    }
    assert_eq!(outputs[0], outputs[1]);
    assert_ne!(outputs[1][0], outputs[2][0]);
    assert_eq!(outputs[1][2], outputs[2][2]);
    Ok(())
  }

  #[test]
  fn bls12_381_fused_recursive_traces_prove_and_verify() -> storage::Result<()>
  {
    let inner = Srs::<Bls12381>::unsafe_dev_setup(8, b"bls-fused-inner");
    let claims = init_packet_claims_for::<Bls12381>(&inner);
    let mut builder = CircuitBuilder::new();
    let input = builder.input("private");
    let table = builder.fixed_table(
      "small",
      (0..16).map(|v| vec![CurveScalar::<Bls12381>::from_u8(v)]).collect(),
    );
    builder.lookup(table, &[input]);
    for _ in 0..8 {
      builder.mul(input, input);
    }
    for claim in &claims[1..] {
      let wire = builder.constant(claim[3]);
      builder.expose_public(wire);
    }
    let circuit = builder.finish();
    let mut witness = circuit.witness();
    witness.set(input, CurveScalar::<Bls12381>::from_u8(7))?;
    let assignment = witness.generate()?;
    let built = Built::<Bls12381> {
      circuit,
      inputs: vec![],
      points: vec![],
      pairing_outputs: vec![],
      pairing_keys: vec![inner.g2, inner.tau_g2],
      msm_terms: vec![],
      terms: vec![],
    };
    let root = TempDir::new("bls12-381-kzg-recursive-fused");
    let dir = root.join("stage");
    fs::create_dir(&dir)?;
    stage::<Bls12381>(
      built,
      assignment,
      &dir,
      b"bls-recursive-fixture",
      &INIT_PUBLIC_WORDS,
      &crate::pipeline::StageConfig::development(),
    )?;
    let report: serde_json::Value =
      serde_json::from_slice(&fs::read(dir.join("kzg/prove-report.json"))?)?;
    assert_eq!(report["curve"], "bls12-381");
    assert_eq!(report["pairing_bytes"], 96);
    assert_eq!(report["vk_version"], Bls12381::OUTER_VK_VERSION);
    let packet = fs::read(dir.join("kzg/packet.bin"))?;
    verify_saved::<Bls12381>(&dir, &packet, None)?;
    let portable = fs::read(dir.join("vk.bin"))?;
    let trusted = *blake3::hash(&portable).as_bytes();
    let claim = include_bytes!("../../../tests/fixtures/init-fri/claim.bin");
    let expected_claims = statement::to_claims_bytes(&INIT_PUBLIC_WORDS);
    let mut envelope = super::super::super::BLS12_381_PROOF_TAG.to_vec();
    envelope.extend_from_slice(&packet);
    assert_eq!(
      super::super::super::verify_with_vk(
        &envelope,
        claim,
        &expected_claims,
        &portable,
        &trusted,
        true,
      )?,
      SetupClass::Development
    );
    assert!(
      super::super::super::verify_with_vk(
        &envelope,
        claim,
        &expected_claims,
        &portable,
        &trusted,
        false,
      )
      .is_err()
    );
    let mut wrong_curve_envelope = super::super::super::PROOF_TAG.to_vec();
    wrong_curve_envelope.extend_from_slice(&packet);
    assert!(
      super::super::super::verify_with_vk(
        &wrong_curve_envelope,
        claim,
        &expected_claims,
        &portable,
        &trusted,
        true,
      )
      .is_err()
    );
    let mut bad = packet.clone();
    *bad.last_mut().unwrap() ^= 1;
    assert!(verify_saved::<Bls12381>(&dir, &bad, None).is_err());
    Ok(())
  }

  #[test]
  #[ignore = "eight-minute CPU outer proof over an identity-commitment wrapper"]
  fn constant_column_first_stage_proof_wraps_proves_and_verifies()
  -> storage::Result<()> {
    use crate::recursive::native_verifier::Plan;
    use multi_stark::{expr::Expr, lookup::Lookup, system::CircuitInputs};
    use p3_matrix::dense::RowMajorMatrix;
    let words = INIT_PUBLIC_WORDS;
    let srs = Arc::new(Srs::unsafe_dev_setup(8, b"constant-column-inner"));
    let (system, key) = System::new(
      KzgConfig::new(srs.clone(), 2),
      [CircuitInputs {
        main_width: 18,
        preprocessed: Some(RowMajorMatrix::new_col(vec![
          Scalar::ONE,
          Scalar::ZERO,
          Scalar::ZERO,
          Scalar::ZERO,
        ])),
        constraints: (0..18)
          .map(|i| Expr::main_next(i) - Expr::main(i))
          .collect(),
        lookups: (0..19)
          .map(|index| {
            Lookup::pull(
              Expr::preprocessed(0),
              vec![
                Expr::constant(Scalar::from_u8(93)),
                Expr::constant(Scalar::ONE),
                Expr::constant(Scalar::from_usize(index)),
                if index == 0 {
                  Expr::constant(Scalar::ZERO)
                } else {
                  Expr::main(u32::try_from(index - 1).unwrap())
                },
              ],
            )
          })
          .collect(),
        ..Default::default()
      }],
    );
    let claims: Vec<_> = std::iter::once(0)
      .chain(words)
      .enumerate()
      .map(|(index, value)| {
        vec![
          Scalar::from_u8(93),
          Scalar::ONE,
          Scalar::from_usize(index),
          Scalar::from_u64(value),
        ]
      })
      .collect();
    // Every main column is constant and the first is zero, so the proof
    // carries an identity commitment and generator multiples the affine
    // wrapper arithmetic must handle without exceptional additions.
    let main = RowMajorMatrix::new(
      words.into_iter().map(Scalar::from_u64).collect::<Vec<_>>().repeat(4),
      18,
    );
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(vec![main], &system),
    );
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("inner proof: {e:?}"))?;
    assert!(
      proof.commitments.stage_1_trace.0.iter().flatten().any(|p| p.infinity)
    );
    let plan = Plan::new(
      &system,
      &[2],
      super::super::saved::claim_schema(&claims)?,
      super::super::saved::layout(),
    )?;
    let built = plan.build(&proof, &claims)?;
    let assignment = built.check()?;
    let dir = TempDir::new("kzg-recursive-constant");
    stage(
      built,
      assignment,
      &dir,
      &plan.identity(),
      &INIT_PUBLIC_WORDS,
      &crate::pipeline::StageConfig::development(),
    )?;
    let packet = fs::read(dir.join("kzg/packet.bin"))?;
    verify_saved::<Bn254>(&dir, &packet, None)?;
    let mut bad = packet.clone();
    bad[32 + 18 * 8 + 1] ^= 1;
    assert!(verify_saved::<Bn254>(&dir, &bad, None).is_err());
    Ok(())
  }
}
