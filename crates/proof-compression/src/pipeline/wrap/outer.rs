//! Recursive KZG wrapper: staging and proving in one process, and the
//! portable verifier its packets are checked with.
use super::super::stages::{
  construct::{self, Lowered},
  statement::Statement as StageStatement,
  verification,
};
use super::{
  super::Result as PipelineResult,
  super::{
    fixed_cache, prover,
    setup::{SetupClass, SetupSource},
    statement::{self, Statement},
    storage,
  },
};
use crate::{
  kzg::{
    KzgCommitment, KzgConfig, Scalar, TranscriptKind, compact::FixedProofCodec,
  },
  recursive::native_verifier::Built,
};
use multi_stark::{
  plonkish::{Assignment, MultiStarkCircuit},
  traits::Field,
};
use std::{fs, path::Path};

pub(super) const OUTER_SEED: &[u8] = b"init-kzg-recursive-v1";
const OUTER_PROFILE_VERSION: u32 = 5;
/// Largest admitted recursive computation trace. The development public
/// degree of a staged profile covers exactly its own height.
pub(super) const MAX_TRACE_LEN: usize = construct::RECURSIVE_HEIGHT;

#[derive(serde::Serialize, serde::Deserialize)]
struct Pairings {
  keys: Vec<u8>,
}

pub(crate) fn stage(
  built: Built,
  assignment: Assignment<Scalar>,
  dir: &Path,
  profile: &[u8],
  statement: &Statement,
  config: &super::super::WorkerConfig,
) -> storage::Result<()> {
  let frontend = Frontend::from_built(built, profile)?;
  frontend.stage(assignment, dir, statement, config)
}

/// A recursive circuit lowered into one computation trace and one merged
/// table, ready to stage any number of requests of its profile.
pub(crate) struct Frontend {
  compiled: MultiStarkCircuit<Scalar>,
  pairings: Pairings,
  profile: Vec<u8>,
}

impl Frontend {
  fn from_built(built: Built, profile: &[u8]) -> storage::Result<Self> {
    Self::new(built.circuit, &built.pairing_keys, profile, MAX_TRACE_LEN)
  }

  pub(crate) fn new(
    circuit: multi_stark::plonkish::Circuit<Scalar>,
    keys: &[ark_bls12_381::G2Affine],
    profile: &[u8],
    max_height: usize,
  ) -> storage::Result<Self> {
    use ark_serialize::CanonicalSerialize;
    if keys.len() != 2 {
      return Err("invalid recursive pairing profile".into());
    }
    let mut encoded = vec![];
    keys.serialize_compressed(&mut encoded)?;
    let compiled = construct::lower_recursive(circuit, max_height)?;
    Ok(Self {
      compiled,
      pairings: Pairings { keys: encoded },
      profile: profile.to_vec(),
    })
  }

  /// Stage and prove one request, keeping the witness traces in memory.
  /// Fixed preprocessing comes from the cache when it already holds this
  /// profile and is published to it after the proof verifies.
  pub(crate) fn stage(
    self,
    assignment: Assignment<Scalar>,
    dir: &Path,
    statement: &Statement,
    config: &super::super::WorkerConfig,
  ) -> storage::Result<()> {
    if assignment.public_values().len() != 18 + 2 * 2
      || assignment.public_values()[..18]
        .iter()
        .zip(statement)
        .any(|(&value, &word)| value != Scalar::from_u64(word))
    {
      return Err(
        "recursive assignment differs from the first stage's statement".into(),
      );
    }
    let start = std::time::Instant::now();
    let height = self.compiled.main_height();
    let setup = config
      .setup
      .for_stage(OUTER_SEED, height)?
      .with_transcript(TranscriptKind::Keccak256);
    let setup_id = setup.identity(height, 2)?;
    fs::create_dir_all(dir)?;
    setup.bind_stage(dir, height, 2)?;
    storage::save(&dir.join("pairings.bin"), &self.pairings)?;
    let cache_profile = [self.profile.as_slice(), &setup_id].concat();
    let cache = config.fixed_cache(dir, &cache_profile)?;
    let cached = cache.restore(dir)?;
    let manifest = storage::Manifest::for_compiled(
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

fn pairing_keys(dir: &Path) -> storage::Result<Vec<ark_bls12_381::G2Affine>> {
  let profile: Pairings = storage::load(&dir.join("pairings.bin"))?;
  decode_pairing_keys(&profile)
}

fn decode_pairing_keys(
  profile: &Pairings,
) -> storage::Result<Vec<ark_bls12_381::G2Affine>> {
  use ark_ec::AffineRepr;
  use ark_serialize::CanonicalDeserialize;
  if profile.keys.len() != 8 + 2 * 96
    || profile.keys.get(..8) != Some(&2u64.to_le_bytes())
  {
    return Err("invalid pairing profile".into());
  }
  let mut input = profile.keys.as_slice();
  let keys =
    Vec::<ark_bls12_381::G2Affine>::deserialize_compressed(&mut input)?;
  if !input.is_empty()
    || keys.len() != 2
    || keys.iter().any(AffineRepr::is_zero)
  {
    return Err("invalid pairing profile".into());
  }
  Ok(keys)
}

fn pairing_bytes(publics: &[Scalar]) -> storage::Result<Vec<u8>> {
  verification::pack_pairings(publics)
}
fn check_pairings(
  bytes: &[u8],
  keys: &[ark_bls12_381::G2Affine],
) -> storage::Result<()> {
  verification::Pairings {
    keys: keys.try_into().map_err(|_keys| "pairing point count")?,
  }
  .verify_bytes(bytes)
}
fn packet_body<'a>(
  packet: &'a [u8],
  profile: &[u8; 32],
  expected: &Statement,
) -> storage::Result<&'a [u8]> {
  let offset = 32 + statement::WORDS * 8;
  if packet.len() < offset + 96 || packet[..32] != *profile {
    return Err("packet profile mismatch".into());
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

#[cfg(test)]
fn packet_claims(
  packet: &[u8],
  profile: &[u8; 32],
  pairing_count: usize,
  expected: &Statement,
) -> storage::Result<(Vec<Vec<Scalar>>, usize)> {
  if pairing_count != 2 {
    return Err("pairing point count".into());
  }
  let body = packet_body(packet, profile, expected)?;
  let mut public: Vec<_> =
    expected.iter().copied().map(Scalar::from_u64).collect();
  public.extend(verification::unpack_pairings(&body[..96])?);
  let claims = StageStatement::recursive(public.len()).claims(&public)?;
  Ok((claims, 32 + statement::WORDS * 8 + 96))
}
fn verify_packet(
  system: &multi_stark::system::System<KzgConfig>,
  codec: &FixedProofCodec,
  packet: &[u8],
  profile: &[u8; 32],
  keys: &[ark_bls12_381::G2Affine],
  expected: &Statement,
) -> storage::Result<()> {
  let body = packet_body(packet, profile, expected)?;
  let pairings = verification::Pairings {
    keys: keys.try_into().map_err(|_keys| "pairing point count")?,
  };
  verification::verify_recursive_bytes(
    system,
    codec,
    &StageStatement::recursive(22),
    &pairings,
    body,
    &expected.iter().copied().map(Scalar::from_u64).collect::<Vec<_>>(),
  )
}

fn staged_publics(
  claims: &[Vec<Scalar>],
  pairing_count: usize,
) -> storage::Result<Vec<Scalar>> {
  let count = pairing_count
    .checked_mul(2)
    .and_then(|n| n.checked_add(18))
    .ok_or("public count overflow")?;
  StageStatement::recursive(count).public_values(claims)
}

/// Commit the fixed and witness traces from memory, prove, verify the
/// packet and write it with the portable verifier. Fixed columns are
/// checkpointed because every proof of the profile shares them through the
/// cache; witness columns never touch disk.
fn prove(
  dir: &Path,
  lowered: Lowered,
  cache: &fixed_cache::FixedCache,
  setup: &SetupSource,
) -> storage::Result<()> {
  use multi_stark::config::ProofConfig;
  use std::time::Instant;
  let start = Instant::now();
  let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
  if manifest.heights.len() != 2
    || manifest.widths.len() != 2
    || manifest.widths[0] != 3
    || manifest.widths[1] != 1
    || manifest
      .heights
      .iter()
      .any(|h| *h < 2 || !h.is_power_of_two() || *h > 1 << 28)
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
  let keys = pairing_keys(dir)?;
  let publics = staged_publics(&manifest.claims, keys.len())?;
  let point_bytes = pairing_bytes(&publics[18..])?;
  check_pairings(&point_bytes, &keys)?;
  let statement = statement::from_scalars(&publics[..18])?;
  let out = dir.join("kzg");
  fs::create_dir_all(&out)?;
  eprintln!("Preparing KZG parameters for 2^{} rows", height.ilog2());
  setup.check_binding(dir, height, 2)?;
  fs::write(out.join("SECURITY.txt"), setup.security_description())?;
  let setup_id = setup.identity(height, 2)?;
  let verifier_params = setup.verifier_params(height)?;
  let config_started = Instant::now();
  let config = setup
    .config(height, 2, false)?
    .with_streaming_lookups()
    .with_streaming_quotient();
  let srs_config_load_seconds = config_started.elapsed().as_secs_f64();
  eprintln!("Outer KZG parameters ready: {:?}", start.elapsed());
  let prover::Proved { system, codec, bytes, .. } =
    lowered.commit(config, Some(&out), 0)?.prove(&manifest.claims)?;
  let output_span = tracing::info_span!("compression/write_output").entered();
  let verifier = VerifierProfile {
    version: OUTER_PROFILE_VERSION,
    heights: [manifest.heights[0], manifest.heights[1]],
    setup: [
      fs::read(out.join("setup-0.bin"))?,
      fs::read(out.join("setup-1.bin"))?,
    ],
    pairings: fs::read(dir.join("pairings.bin"))?,
    parameters: verifier_params.to_bytes()?,
  };
  let profile = verifier.id();
  let mut packet = profile.to_vec();
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
    verify_packet(&system, &codec, &packet, &profile, &keys, &statement)
  })?;
  let verify_seconds = verify_start.elapsed().as_secs_f64();
  let encoded =
    bincode::serde::encode_to_vec(&verifier, bincode::config::standard())?;
  storage::write_atomic(&out.join("proof.compact.bin"), &bytes)?;
  storage::write_atomic(&dir.join("verifier.bin"), &encoded)?;
  storage::write_atomic(&out.join("profile-id.bin"), &profile)?;
  storage::write_atomic(&out.join("packet.bin"), &packet)?;
  let public_setup = system.config.pcs().verifier_params().public_setup();
  let development = setup.class() == SetupClass::Development;
  let report = serde_json::json!({
    "proof_bytes": bytes.len(),
    "packet_bytes": packet.len(),
    "claim_bytes": 144,
    "pairing_bytes": keys.len() * 48,
    "profile_bytes": 32,
    "profile_version": OUTER_PROFILE_VERSION,
    "transcript": "keccak256",
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
    "profile_id": blake3::Hash::from_bytes(profile).to_hex().to_string(),
    "trace_heights": manifest.heights,
  });
  fs::write(
    out.join("prove-report.json"),
    serde_json::to_vec_pretty(&report)?,
  )?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  drop(output_span);
  cache.publish(dir)?;
  Ok(())
}

/// Recursive verifier metadata. Application verification accepts only bundled profiles.
#[derive(serde::Serialize, serde::Deserialize)]
pub(crate) struct VerifierProfile {
  version: u32,
  heights: [usize; 2],
  setup: [Vec<u8>; 2],
  pairings: Vec<u8>,
  parameters: Vec<u8>,
}

fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> storage::Result<T> {
  if bytes.len() > 1 << 20 {
    return Err("verifier profile too large".into());
  }
  let (value, consumed) = bincode::serde::decode_from_slice(
    bytes,
    bincode::config::standard().with_limit::<{ 1 << 20 }>(),
  )?;
  if consumed != bytes.len() {
    return Err("trailing verifier profile bytes".into());
  }
  Ok(value)
}

impl VerifierProfile {
  pub(crate) fn from_bytes(bytes: &[u8]) -> PipelineResult<Self> {
    let profile: Self = decode(bytes)?;
    profile.prepare()?;
    Ok(profile)
  }

  pub(crate) fn id(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(
      format!("init-kzg-recursive-profile/v{}", self.version).as_bytes(),
    );
    hash.update(OUTER_SEED);
    hash.update(&self.parameters);
    hash.update(&(self.heights[0] as u64).to_le_bytes());
    for setup in &self.setup {
      hash.update(setup);
    }
    hash.update(&self.pairings);
    *hash.finalize().as_bytes()
  }

  fn keys(&self) -> storage::Result<Vec<ark_bls12_381::G2Affine>> {
    decode_pairing_keys(&decode(&self.pairings)?)
  }

  /// The verifier parameters the profile carries.
  pub(crate) fn verifier_params(
    &self,
  ) -> storage::Result<crate::kzg::VerifierParams> {
    Ok(crate::kzg::VerifierParams::from_bytes(&self.parameters)?)
  }

  /// Filecoin classification covers both the outer proof and the deferred
  /// inner opening equation. Development stages may use different seeds.
  pub(crate) fn check_setup_class(
    &self,
    expected: SetupClass,
  ) -> PipelineResult<()> {
    let parameters = self.verifier_params()?;
    if SetupClass::of(&parameters) != expected {
      return Err("bundled verifier setup class differs".into());
    }
    if expected == SetupClass::Filecoin
      && self.keys()? != [parameters.g2, parameters.tau_g2]
    {
      return Err(
        "Filecoin verifier has different inner pairing anchors".into(),
      );
    }
    Ok(())
  }

  fn system(&self) -> storage::Result<multi_stark::system::System<KzgConfig>> {
    use crate::kzg::VerifierParams;
    use multi_stark::system::{Circuit, System};
    if self.version != OUTER_PROFILE_VERSION {
      return Err("unsupported recursive verifier profile".into());
    }
    if self
      .heights
      .iter()
      .any(|h| *h < 2 || !h.is_power_of_two() || *h > 1 << 28)
      || self.heights[1] > self.heights[0]
    {
      return Err("unsupported recursive verifier profile".into());
    }
    let params = VerifierParams::from_bytes(&self.parameters)?;
    if params.max_trace_len() != self.heights[0] {
      return Err("verifier SRS range mismatch".into());
    }
    let mut circuits = vec![];
    let mut fixed = KzgCommitment(vec![]);
    for (i, bytes) in self.setup.iter().enumerate() {
      let (circuit, mut commit): (Circuit<Scalar>, KzgCommitment) =
        decode(bytes)?;
      if circuit.main_width != [3, 1][i]
        || circuit.preprocessed_height != self.heights[i]
      {
        return Err("setup shape mismatch".into());
      }
      circuits.push(circuit);
      fixed.0.append(&mut commit.0);
    }
    Ok(System {
      config: KzgConfig::verifier_only(params, 2)
        .with_transcript(TranscriptKind::Keccak256),
      circuits,
      preprocessed_commit: Some(fixed),
      preprocessed_indices: vec![Some(0), Some(1)],
    })
  }

  pub(crate) fn prepare(&self) -> PipelineResult<PreparedVerifierProfile> {
    Ok(PreparedVerifierProfile {
      id: self.id(),
      verifier: super::super::stages::RecursiveVerifier::from_parts(
        self.system()?,
        StageStatement::recursive(22),
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

pub(crate) struct PreparedVerifierProfile {
  id: [u8; 32],
  verifier: super::super::stages::RecursiveVerifier,
}

impl PreparedVerifierProfile {
  pub(crate) fn verify(
    &self,
    packet: &[u8],
    expected: &Statement,
  ) -> PipelineResult<()> {
    let body = packet_body(packet, &self.id, expected)?;
    self.verifier.verify_scalar_bytes(
      body,
      &expected.iter().copied().map(Scalar::from_u64).collect::<Vec<_>>(),
    )
  }
}

/// Verify a packet against the stage's portable verifier. Without an
/// independently derived statement, the one the stage's own claim rows
/// carry is used, so the check covers the proof but not the claim binding.
pub(crate) fn verify_saved(
  dir: &Path,
  packet: &[u8],
  expected: Option<&Statement>,
) -> PipelineResult<()> {
  let staged;
  let expected = match expected {
    Some(expected) => expected,
    None => {
      let manifest: storage::Manifest =
        storage::load(&dir.join("manifest.bin"))?;
      staged = statement::from_rows(&manifest.claims)?;
      &staged
    },
  };
  VerifierProfile::from_bytes(&fs::read(dir.join("verifier.bin"))?)?
    .verify(packet, expected)
}

#[cfg(test)]
mod tests {
  use super::super::super::init_claim;
  use super::*;
  use crate::{foreign::KzgCircuitExt, kzg::Srs};
  use ark_ec::CurveGroup;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::{
    plonkish::CircuitBuilder,
    system::{System, SystemWitness},
    traits::Algebra,
  };
  use std::sync::Arc;

  #[test]
  fn bundled_and_public_recursive_verifiers_share_transport_validation()
  -> storage::Result<()> {
    let wire = VerifierProfile::from_bytes(include_bytes!(
      "../../../profiles/aggregate-filecoin-v5.bin"
    ))?;
    let prepared = wire.prepare()?;
    let public = super::super::super::stages::RecursiveVerifier::from_bytes(
      &prepared.verifier.to_bytes()?,
    )?;
    let packet = include_bytes!(
      "../../../tests/fixtures/aggregate-kzg/filecoin-v5-packet.bin"
    );
    let words = init_claim::INIT_PUBLIC_WORDS;
    let expected = words.map(Scalar::from_u64);
    prepared.verify(packet, &words)?;
    public.verify_scalar_bytes(&packet[32 + 18 * 8..], &expected)?;
    let mut wrong = expected;
    wrong[0] += Scalar::ONE;
    assert!(
      public.verify_scalar_bytes(&packet[32 + 18 * 8..], &wrong).is_err()
    );
    let mut corrupt = packet.to_vec();
    let last = corrupt.len() - 1;
    corrupt[last] ^= 1;
    assert!(prepared.verify(&corrupt, &words).is_err());
    assert!(
      public.verify_scalar_bytes(&corrupt[32 + 18 * 8..], &expected).is_err()
    );
    assert!(
      public
        .verify_scalar_bytes(&packet[32 + 18 * 8..packet.len() - 1], &expected)
        .is_err()
    );
    Ok(())
  }

  #[test]
  fn filecoin_bundle_requires_filecoin_inner_pairing_anchors() {
    use ark_serialize::CanonicalSerialize;
    let mut profile = VerifierProfile::from_bytes(include_bytes!(
      "../../../profiles/aggregate-filecoin-v5.bin"
    ))
    .unwrap();
    profile.check_setup_class(SetupClass::Filecoin).unwrap();
    assert!(profile.check_setup_class(SetupClass::Development).is_err());
    let development = Srs::unsafe_dev_setup(2, b"mixed-pairing-setup");
    let mut keys = Vec::new();
    vec![development.g2, development.tau_g2]
      .serialize_compressed(&mut keys)
      .unwrap();
    profile.pairings = bincode::serde::encode_to_vec(
      Pairings { keys },
      bincode::config::standard(),
    )
    .unwrap();
    assert!(profile.check_setup_class(SetupClass::Filecoin).is_err());
  }

  #[test]
  fn packet_requires_outer_proof_claim_and_external_pairings() {
    let inner = Srs::unsafe_dev_setup(8, b"packet-inner");
    let keys = vec![inner.g2, inner.tau_g2];
    let profile = [17u8; 32];
    let packet_prefix = |wrong: bool| {
      let mut packet = profile.to_vec();
      for v in init_claim::INIT_PUBLIC_WORDS {
        packet.extend(v.to_le_bytes());
      }
      let lhs = if wrong {
        (inner.g1[1] * ark_bls12_381::Fr::from(2u8)).into_affine()
      } else {
        inner.g1[1]
      };
      lhs.serialize_compressed(&mut packet).unwrap();
      (-inner.g1[0]).serialize_compressed(&mut packet).unwrap();
      packet
    };
    let (claims, _) = packet_claims(
      &packet_prefix(false),
      &profile,
      2,
      &init_claim::INIT_PUBLIC_WORDS,
    )
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
        .with_transcript(TranscriptKind::Keccak256);
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
        packet_claims(&packet, &profile, 2, &init_claim::INIT_PUBLIC_WORDS)
          .unwrap();
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
        verify_packet(
          &system,
          &codec,
          &packet,
          &profile,
          &keys,
          &init_claim::INIT_PUBLIC_WORDS
        )
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
            &profile,
            &keys,
            &init_claim::INIT_PUBLIC_WORDS
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
            &profile,
            &keys,
            &init_claim::INIT_PUBLIC_WORDS
          )
          .is_err()
        );
        packet.push(0);
        assert!(
          verify_packet(
            &system,
            &codec,
            &packet,
            &profile,
            &keys,
            &init_claim::INIT_PUBLIC_WORDS
          )
          .is_err()
        );
      }
    }
  }

  fn init_packet_claims(inner: &Srs) -> Vec<Vec<Scalar>> {
    let mut prefix = [0u8; 32].to_vec();
    for word in init_claim::INIT_PUBLIC_WORDS {
      prefix.extend(word.to_le_bytes());
    }
    inner.g1[1].serialize_compressed(&mut prefix).unwrap();
    (-inner.g1[0]).serialize_compressed(&mut prefix).unwrap();
    packet_claims(&prefix, &[0u8; 32], 2, &init_claim::INIT_PUBLIC_WORDS)
      .unwrap()
      .0
  }

  /// Stage a compiled fixture's metadata the way `Frontend::stage` does.
  fn stage_fixture(
    dir: &Path,
    cache_root: &Path,
    compiled: &MultiStarkCircuit<Scalar>,
    assignment: &Assignment<Scalar>,
    keys: &[ark_bls12_381::G2Affine],
  ) -> storage::Result<fixed_cache::FixedCache> {
    fs::create_dir_all(dir)?;
    let height = compiled.main_height();
    SetupSource::development(OUTER_SEED, height - 1)?
      .with_transcript(TranscriptKind::Keccak256)
      .bind_stage(dir, height, 2)?;
    let mut encoded = vec![];
    keys.serialize_compressed(&mut encoded)?;
    storage::save(&dir.join("pairings.bin"), &Pairings { keys: encoded })?;
    let cache = fixed_cache::FixedCache::from_profile(cache_root, b"outer")?;
    let cached = cache.restore(dir)?;
    let manifest = storage::Manifest::for_compiled(
      compiled,
      compiled.claims(assignment.public_values())?,
      cached.as_ref(),
    )?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    Ok(cache)
  }

  #[test]
  fn fused_profiles_prove_and_portable_verifiers_round_trip()
  -> storage::Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("outer-staged-{}-v5", std::process::id()));
    fs::create_dir(&dir)?;
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
    let setup = SetupSource::development(OUTER_SEED, height - 1)?
      .with_transcript(TranscriptKind::Keccak256);
    prove(&first, Lowered { compiled, assignment }, &cache, &setup)?;
    assert!(first.join("kzg/fixed-0.bin").exists());
    assert!(!first.join("kzg/main-0.bin").exists());
    let packet = fs::read(first.join("kzg/packet.bin"))?;
    verify_saved(&first, &packet, None)?;
    for offset in [0, 32, packet.len() - 1] {
      let mut bad = packet.clone();
      bad[offset] ^= 1;
      assert!(verify_saved(&first, &bad, None).is_err());
    }
    assert!(verify_saved(&first, &packet[..packet.len() - 1], None).is_err());
    let mut extra = packet.clone();
    extra.push(0);
    assert!(verify_saved(&first, &extra, None).is_err());
    // A second run of the profile restores the fixed preprocessing from
    // the cache and produces the same packet.
    let second = dir.join("second");
    let Lowered { compiled, assignment } = make()?;
    let cache =
      stage_fixture(&second, &cache_root, &compiled, &assignment, &keys)?;
    assert!(second.join("kzg/fixed-0.bin").exists());
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
    let portable = fs::read(first.join("verifier.bin"))?;
    let profile = VerifierProfile::from_bytes(&portable)?;
    assert_eq!(profile.version, OUTER_PROFILE_VERSION);
    assert_eq!(
      profile.system()?.config.transcript_kind(),
      TranscriptKind::Keccak256
    );

    for version in [0, 4, 6] {
      let mut unsupported: VerifierProfile = decode(&portable)?;
      unsupported.version = version;
      let unsupported = bincode::serde::encode_to_vec(
        &unsupported,
        bincode::config::standard(),
      )?;
      assert!(VerifierProfile::from_bytes(&unsupported).is_err());
    }

    // Verify using only the portable object after deleting the SRS and all checkpoints.
    fs::remove_dir_all(&dir)?;
    profile.verify(&packet, &init_claim::INIT_PUBLIC_WORDS)?;
    let mut wrong_range: VerifierProfile = decode(&portable)?;
    wrong_range.heights[0] *= 2;
    assert!(wrong_range.system().is_err());
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
    let root = std::env::temp_dir()
      .join(format!("kzg-recursive-fused-{}", std::process::id()));
    fs::create_dir(&root)?;
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
        &init_claim::INIT_PUBLIC_WORDS,
        &crate::pipeline::WorkerConfig::development(),
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
        assert!(dir.join(format!("kzg/fixed-{i}.bin")).exists());
      }
      let packet = fs::read(dir.join("kzg/packet.bin"))?;
      verify_saved(&dir, &packet, None)?;
      outputs.push(
        ["proof.compact.bin", "packet.bin", "profile-id.bin"]
          .map(|name| fs::read(dir.join("kzg").join(name)).unwrap()),
      );
    }
    assert_eq!(outputs[0], outputs[1]);
    assert_ne!(outputs[1][0], outputs[2][0]);
    assert_eq!(outputs[1][2], outputs[2][2]);
    fs::remove_dir_all(root)?;
    Ok(())
  }

  #[test]
  #[ignore = "eight-minute CPU outer proof over an identity-commitment wrapper"]
  fn constant_column_first_stage_proof_wraps_proves_and_verifies()
  -> storage::Result<()> {
    use crate::recursive::native_verifier::Plan;
    use multi_stark::{expr::Expr, lookup::Lookup, system::CircuitInputs};
    use p3_matrix::dense::RowMajorMatrix;
    let words = init_claim::INIT_PUBLIC_WORDS;
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
    let dir = std::env::temp_dir()
      .join(format!("kzg-recursive-constant-{}", std::process::id()));
    fs::create_dir(&dir)?;
    stage(
      built,
      assignment,
      &dir,
      &plan.identity(),
      &init_claim::INIT_PUBLIC_WORDS,
      &crate::pipeline::WorkerConfig::development(),
    )?;
    let packet = fs::read(dir.join("kzg/packet.bin"))?;
    verify_saved(&dir, &packet, None)?;
    let mut bad = packet.clone();
    bad[32 + 18 * 8 + 1] ^= 1;
    assert!(verify_saved(&dir, &bad, None).is_err());
    fs::remove_dir_all(dir)?;
    Ok(())
  }
}
