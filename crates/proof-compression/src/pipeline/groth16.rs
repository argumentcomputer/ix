//! Final BN254 Groth16 proofs under the release key.
#[cfg(feature = "groth16")]
use super::final_proof::{hex, sha256};
#[cfg(feature = "groth16")]
use super::gnark;
#[cfg(feature = "groth16")]
use super::storage;
use super::{
  Result,
  final_proof::{Artifact, digest, load_json},
  setup::SetupClass,
  statement, verifying_keys,
};
#[cfg(feature = "groth16")]
use super::{
  final_proof::{claim_digest, read_bounded},
  setup::SetupConfig,
  wrap,
};
#[cfg(feature = "groth16")]
use std::fs;
#[cfg(feature = "groth16")]
use std::path::Path;
use std::path::PathBuf;

pub(super) const PROOF_TAG: &[u8; 8] = b"IXBN\0\0\0\x03";
const ARTIFACTS_VAR: &str = "IX_GROTH16_ARTIFACTS";
const MAX_PROOF_BYTES: usize = 196;

fn check_length(packet: &[u8]) -> Result<()> {
  if packet.len() != 164 + 32 && packet.len() != MAX_PROOF_BYTES + 32 {
    return Err("invalid Groth16 packet length".into());
  }
  Ok(())
}

/// Verify a Groth16 packet of `claim` under the release key.
#[cfg(feature = "groth16")]
pub(super) fn verify(
  packet: &[u8],
  claim: &[u8],
  allow_development: bool,
) -> Result<SetupClass> {
  check_length(packet)?;
  if packet[..32] != verifying_keys::decode(verifying_keys::GROTH16_VK_SHA256)?
  {
    return Err(
      "Groth16 proof uses a verifying key other than the release key".into(),
    );
  }
  if <sha2::Sha256 as sha2::Digest>::digest(verifying_keys::GROTH16_VK)
    .as_slice()
    != &packet[..32]
  {
    return Err("bundled Groth16 verifying key differs from its pin".into());
  }
  let setup = verifying_keys::groth16_setup(allow_development)?;
  verify_under(verifying_keys::GROTH16_VK, packet, claim)?;
  Ok(setup)
}

/// Verify the stage against the key prepared for the independently reconstructed
/// inner verifier. Development stages additionally bind their exported bundle.
#[cfg(feature = "groth16")]
pub(super) fn check_stage(
  dir: &Path,
  expected: &statement::Statement,
  allow_development: bool,
  bundled: bool,
  verifier: &Path,
  setup: &SetupConfig,
  cache_root: &Path,
) -> Result<()> {
  let schema = super::final_proof::description(verifier, expected, setup)?;
  let artifacts = prepared_for_schema(&schema, allow_development, cache_root)?;
  let metadata: Metadata = load_json(&artifacts.join("manifest.json"))?;
  let envelope = fs::read(dir.join("proof.envelope.bin"))?;
  let packet = envelope
    .strip_prefix(PROOF_TAG.as_slice())
    .ok_or("not a Groth16 proof envelope")?;
  check_length(packet)?;
  let key = fs::read(dir.join("verifying-key.bin"))?;
  if <sha2::Sha256 as sha2::Digest>::digest(&key).as_slice() != &packet[..32] {
    return Err("Groth16 proof names another verifying key".into());
  }
  if packet[..32] != digest(&metadata.artifact("verifying-key.bin")?.sha256)? {
    return Err("Groth16 stage uses another prepared circuit key".into());
  }
  if bundled
    && !allow_development
    && packet[..32]
      != verifying_keys::decode(verifying_keys::GROTH16_VK_SHA256)?
  {
    return Err("Groth16 verifying key differs from the bundled key".into());
  }
  if allow_development {
    super::development::Verifier::new(
      super::FinalSystem::Groth16,
      verifier,
      &schema,
      expected,
      setup,
      &key,
      None,
    )?
    .check_saved(dir)?;
  }
  gnark::verify_groth16(
    &key,
    packet[..32].try_into()?,
    &packet[32..],
    &claim_digest(expected)?,
  )
}

#[cfg(not(feature = "groth16"))]
pub(super) fn check_stage(
  _dir: &std::path::Path,
  _expected: &statement::Statement,
  _allow_development: bool,
  _bundled: bool,
  _verifier: &std::path::Path,
  _setup: &super::SetupConfig,
  _cache_root: &std::path::Path,
) -> Result<()> {
  Err("this ix was built without Groth16; rebuild with IX_GROTH16=1".into())
}

#[cfg(feature = "groth16")]
fn verify_under(key: &[u8], packet: &[u8], claim: &[u8]) -> Result<()> {
  gnark::verify_groth16(
    key,
    packet[..32].try_into()?,
    &packet[32..],
    blake3::hash(claim).as_bytes(),
  )
}

#[cfg(not(feature = "groth16"))]
pub(super) fn verify(
  packet: &[u8],
  _claim: &[u8],
  _allow_development: bool,
) -> Result<SetupClass> {
  check_length(packet)?;
  Err("Groth16 proofs are verified by gnark, and this ix was built without Groth16; rebuild with IX_GROTH16=1".into())
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub(super) struct Metadata {
  #[serde(rename = "innerVKSHA256")]
  inner_vk: String,
  constraints: usize,
  domain: u64,
  public_inputs: usize,
  commitments: usize,
  setup: String,
  #[serde(
    default,
    rename = "ceremonySHA256",
    skip_serializing_if = "Option::is_none"
  )]
  ceremony: Option<String>,
  keys_ready: bool,
  files: std::collections::BTreeMap<String, Artifact>,
}

impl Metadata {
  fn validate(&self) -> Result<()> {
    if self.public_inputs != 2
      || self.commitments > 1
      || self.constraints == 0
      || self.constraints > 1 << 27
      || self.domain != u64::try_from(self.constraints)?.next_power_of_two()
    {
      return Err("unsupported Groth16 circuit metadata".into());
    }
    digest(&self.inner_vk)?;
    if self.artifact("vk.json")?.sha256 != self.inner_vk {
      return Err("Groth16 schema identity differs".into());
    }
    self.artifact("circuit.bin")?;
    if self.keys_ready {
      match self.setup.as_str() {
        "mpc" => {
          digest(
            self
              .ceremony
              .as_deref()
              .ok_or("missing Groth16 ceremony identity")?,
          )?;
        },
        "development" if self.ceremony.is_none() => {},
        _ => return Err("invalid Groth16 setup metadata".into()),
      }
      for name in
        ["proving-key.bin", "verifying-key.bin", "Groth16Verifier.sol"]
      {
        self.artifact(name)?;
      }
    } else if !self.setup.is_empty() || self.ceremony.is_some() {
      return Err("unprepared Groth16 circuit carries setup metadata".into());
    }
    Ok(())
  }

  fn artifact(&self, name: &str) -> Result<&Artifact> {
    let value = self
      .files
      .get(name)
      .ok_or_else(|| format!("missing Groth16 artifact {name}"))?;
    digest(&value.sha256)?;
    if value.bytes == 0 || value.bytes > 1 << 42 {
      return Err("invalid Groth16 artifact size".into());
    }
    Ok(value)
  }
}

/// The prepared artifacts `IX_GROTH16_ARTIFACTS` names, which must be the
/// release circuit and key.
fn prepared(allow_development: bool) -> Result<PathBuf> {
  let dir =
    std::env::var_os(ARTIFACTS_VAR).map(PathBuf::from).ok_or_else(|| {
      format!("set {ARTIFACTS_VAR} to prepared Groth16 circuit artifacts")
    })?;
  let m: Metadata = load_json(&dir.join("manifest.json"))?;
  m.validate()?;
  if !m.keys_ready {
    return Err("Groth16 keys are not prepared".into());
  }
  if m.artifact("verifying-key.bin")?.sha256
    != verifying_keys::GROTH16_VK_SHA256
    || m.inner_vk != verifying_keys::FINAL_SCHEMA_SHA256
    || m.artifact("circuit.bin")?.sha256
      != verifying_keys::GROTH16_CIRCUIT_SHA256
    || m.setup != "development"
    || m.ceremony.is_some()
  {
    return Err(
      "Groth16 artifacts differ from the release circuit and key".into(),
    );
  }
  verifying_keys::groth16_setup(allow_development)?;
  Ok(dir)
}

pub(super) fn preflight(allow_development: bool) -> Result<()> {
  match std::env::var("IX_GROTH16_BACKEND").as_deref() {
    Err(std::env::VarError::NotPresent) | Ok("" | "cpu" | "cuda") => {},
    _ => return Err("IX_GROTH16_BACKEND must be cpu or cuda".into()),
  }
  if !allow_development {
    prepared(false)?;
  }
  Ok(())
}

/// The release Groth16 key proves `expected`'s aggregation program. The
/// artifacts themselves are checked by `preflight`.
pub(super) fn check_statement(expected: &statement::Statement) -> Result<()> {
  if expected[..10] != verifying_keys::STATEMENT_PREFIX {
    return Err(
      "the release Groth16 key proves another aggregation program".into(),
    );
  }
  Ok(())
}

/// Prove the recursive KZG packet with release artifacts or a cached local
/// development key, and publish its envelope, key and Solidity verifier.
#[cfg(feature = "groth16")]
pub(super) fn wrap_packet(
  verifier: &Path,
  packet: &Path,
  trusted: &str,
  expected: &statement::Statement,
  out: &Path,
  allow_development: bool,
  setup: &SetupConfig,
  cache_root: &Path,
) -> Result<()> {
  statement::from_claims_bytes(&statement::to_claims_bytes(expected))?;
  if !allow_development {
    check_statement(expected)?;
  }
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("Groth16 output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::final_export(verifier, packet, trusted, expected, &input, setup)?;
  let schema = super::final_proof::description(verifier, expected, setup)?;
  if fs::read(input.join("vk.json"))? != schema {
    return Err(
      "Groth16 witness export differs from the expected verifier".into(),
    );
  }
  let artifacts = prepared_for_schema(&schema, allow_development, cache_root)?;
  let claim = claim_digest(expected)?;
  prove(&artifacts, &input.join("witness.json"), &claim, out)?;
  let metadata: Metadata = load_json(&artifacts.join("manifest.json"))?;
  let key_id = digest(&metadata.artifact("verifying-key.bin")?.sha256)?;
  let key = read_bounded(&artifacts.join("verifying-key.bin"), 1 << 20)?;
  let proof = read_bounded(&out.join("proof.bin"), MAX_PROOF_BYTES)?;
  if !matches!(proof.len(), 164 | MAX_PROOF_BYTES) {
    return Err("invalid native Groth16 proof length".into());
  }
  gnark::verify_groth16(&key, &key_id, &proof, &claim)?;
  let mut envelope = PROOF_TAG.to_vec();
  envelope.extend(key_id);
  envelope.extend(proof);
  for name in ["verifying-key.bin", "Groth16Verifier.sol"] {
    storage::write_atomic(&out.join(name), &fs::read(artifacts.join(name))?)?;
  }
  if allow_development {
    super::development::Verifier::new(
      super::FinalSystem::Groth16,
      verifier,
      &schema,
      expected,
      setup,
      &key,
      None,
    )?
    .write(out)?;
  }
  storage::write_atomic(&out.join("proof.envelope.bin"), &envelope)?;
  Ok(())
}

#[cfg(feature = "groth16")]
fn artifact(path: &Path) -> Result<Artifact> {
  Ok(Artifact { sha256: hex(&sha256(path)?), bytes: fs::metadata(path)?.len() })
}

/// Compile the gnark Groth16 verifier circuit for the exported verifier
/// description `schema` into the empty directory `out`, without keys.
#[cfg(feature = "groth16")]
pub fn compile(schema: &Path, out: &Path) -> Result<()> {
  let schema = read_bounded(schema, 16 << 20)?;
  compile_bytes(&schema, out)
}

#[cfg(feature = "groth16")]
fn compile_bytes(schema: &[u8], out: &Path) -> Result<()> {
  super::prepare_output(out)?;
  let info = gnark::compile_groth16(schema, &out.join("circuit.bin"))?;
  storage::write_atomic(&out.join("vk.json"), schema)?;
  let mut files = std::collections::BTreeMap::new();
  for name in ["vk.json", "circuit.bin"] {
    files.insert(name.into(), artifact(&out.join(name))?);
  }
  let metadata = Metadata {
    inner_vk: files["vk.json"].sha256.clone(),
    constraints: info.constraints,
    domain: info.domain,
    public_inputs: info.public_inputs,
    commitments: info.commitments,
    setup: String::new(),
    ceremony: None,
    keys_ready: false,
    files,
  };
  metadata.validate()?;
  storage::write_atomic(
    &out.join("manifest.json"),
    &serde_json::to_vec_pretty(&metadata)?,
  )?;
  Ok(())
}

#[cfg(feature = "groth16")]
fn prepared_for_schema(
  schema: &[u8],
  allow_development: bool,
  cache_root: &Path,
) -> Result<PathBuf> {
  use sha2::{Digest, Sha256};
  let schema_hash = hex(&Sha256::digest(schema));
  let dir = if !allow_development
    || (schema_hash == verifying_keys::FINAL_SCHEMA_SHA256
      && std::env::var_os(ARTIFACTS_VAR).is_some())
  {
    prepared(allow_development)?
  } else {
    let mut identity = blake3::Hasher::new();
    identity.update(b"ix/groth16-development-circuit/v1");
    identity.update(env!("IX_GNARK_SOURCE_BLAKE3").as_bytes());
    identity.update(schema_hash.as_bytes());
    let dir = cache_root
      .join("development")
      .join(identity.finalize().to_hex().as_str());
    storage::prepare_cached_directory(&dir, |temporary| {
      compile_bytes(schema, temporary)?;
      setup_development(temporary)
    })?;
    dir
  };
  let metadata: Metadata = load_json(&dir.join("manifest.json"))?;
  metadata.validate()?;
  if !metadata.keys_ready
    || metadata.inner_vk != schema_hash
    || fs::read(dir.join("vk.json"))? != schema
    || (allow_development
      && (metadata.setup != "development" || metadata.ceremony.is_some()))
  {
    return Err(
      "Groth16 cache differs from the selected circuit and setup".into(),
    );
  }
  Ok(dir)
}

/// Prepare local development keys for the circuit compiled in
/// `dir`. Proofs under them are accepted only with explicit development
/// verification.
#[cfg(feature = "groth16")]
pub fn setup_development(dir: &Path) -> Result<()> {
  setup(dir, gnark::Groth16Setup::Development)
}

/// Run the circuit-specific MPC phase for the circuit compiled in `dir` from
/// the ceremony descriptor `descriptor`, whose SHA-256 must be `pin`.
#[cfg(feature = "groth16")]
pub fn setup_mpc(dir: &Path, descriptor: &Path, pin: &str) -> Result<()> {
  digest(pin)?;
  setup(dir, gnark::Groth16Setup::Ceremony { path: descriptor, digest: pin })
}

/// Import released keys for the circuit compiled in `dir` from the release
/// descriptor `descriptor`, whose SHA-256 must be `pin`.
#[cfg(feature = "groth16")]
pub fn import(dir: &Path, descriptor: &Path, pin: &str) -> Result<()> {
  digest(pin)?;
  setup(dir, gnark::Groth16Setup::Import { path: descriptor, digest: pin })
}

#[cfg(feature = "groth16")]
fn setup(dir: &Path, request: gnark::Groth16Setup<'_>) -> Result<()> {
  let metadata: Metadata = load_json(&dir.join("manifest.json"))?;
  metadata.validate()?;
  if metadata.keys_ready {
    return Err("Groth16 keys are already prepared".into());
  }
  let prepared = gnark::setup_groth16(dir, &metadata, request)?;
  prepared.validate()?;
  if !prepared.keys_ready {
    return Err("Groth16 setup did not return prepared keys".into());
  }
  storage::write_atomic(
    &dir.join("manifest.json"),
    &serde_json::to_vec_pretty(&prepared)?,
  )?;
  Ok(())
}

#[cfg(feature = "groth16")]
fn proving_backend() -> Result<gnark::Groth16Backend> {
  match std::env::var("IX_GROTH16_BACKEND").as_deref() {
    Err(std::env::VarError::NotPresent) | Ok("" | "cpu") => {
      Ok(gnark::Groth16Backend::Cpu)
    },
    Ok("cuda") => {
      if !cfg!(feature = "cuda") {
        return Err("Groth16 CUDA requires groth16 and cuda features".into());
      }
      let device = std::env::var("IX_GROTH16_DEVICE")
        .unwrap_or_else(|_| "0".into())
        .parse()?;
      if device < 0 {
        return Err("invalid Groth16 device".into());
      }
      let library = std::env::var("ICICLE_BACKEND_INSTALL_DIR")
        .ok()
        .filter(|s| !s.is_empty())
        .or_else(|| {
          let installed = std::env::current_exe()
            .ok()?
            .parent()?
            .parent()?
            .join("lib/backend");
          installed.is_dir().then(|| installed.to_string_lossy().into_owned())
        })
        .or_else(|| option_env!("IX_GROTH16_ICICLE_BACKEND").map(str::to_owned))
        .unwrap_or_default();
      Ok(gnark::Groth16Backend::Cuda { device, library })
    },
    _ => Err("IX_GROTH16_BACKEND must be cpu or cuda".into()),
  }
}

#[cfg(feature = "groth16")]
fn prove(
  dir: &Path,
  witness: &Path,
  claim: &[u8; 32],
  out: &Path,
) -> Result<()> {
  let metadata: Metadata = load_json(&dir.join("manifest.json"))?;
  metadata.validate()?;
  let backend = proving_backend()?;
  let start = std::time::Instant::now();
  let mut prover = gnark::Prover::open_groth16(dir, &metadata, &backend)?;
  let load_seconds = start.elapsed().as_secs_f64();
  let witness = read_bounded(witness, 16 << 20)?;
  let start = std::time::Instant::now();
  let proof = prover.prove(&witness, claim)?;
  let prove_seconds = start.elapsed().as_secs_f64();
  prover.close()?;
  fs::create_dir_all(out)?;
  storage::write_atomic(&out.join("proof.bin"), &proof.native)?;
  storage::write_atomic(&out.join("proof.solidity.bin"), &proof.solidity)?;
  storage::write_atomic(
    &out.join("report.json"),
    &serde_json::to_vec_pretty(&serde_json::json!({
      "system":"groth16", "curve":"bn254", "backend":match backend { gnark::Groth16Backend::Cpu=>"cpu",gnark::Groth16Backend::Cuda{..}=>"cuda" },
      "setup":metadata.setup, "loadSeconds":load_seconds, "proveVerifySeconds":prove_seconds,
      "nativeBytes":proof.native.len(), "solidityBytes":proof.solidity.len(), "claimDigest":hex(claim),
      "verifyingKeySHA256":metadata.artifact("verifying-key.bin")?.sha256,
    }))?,
  )?;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  #[cfg(feature = "groth16")]
  fn saved_init_groth16_proof_verifies_without_gpu() -> Result<()> {
    let dir =
      Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/groth16");
    let provenance: serde_json::Value =
      load_json(&dir.join("provenance.json"))?;
    let bytes = fs::read(dir.join("proof.bin"))?;
    let vk = dir.join("verifying-key.bin");
    let id = sha256(&vk)?;
    assert_eq!(
      hex(&id),
      provenance["files"]["verifying-key.bin"].as_str().unwrap()
    );
    let claim = include_bytes!("../../tests/fixtures/init-fri/claim.bin");
    assert_eq!(
      blake3::hash(claim).to_hex().as_str(),
      provenance["claim_digest"].as_str().unwrap()
    );
    let mut packet = id.to_vec();
    packet.extend(bytes);
    let key = fs::read(&vk)?;
    verify_under(&key, &packet, claim)?;
    assert!(verify_under(&key, &packet, b"another claim").is_err());
    assert!(verify(&packet, claim, true).is_err());
    let mut wrong_key = key.clone();
    wrong_key[0] ^= 1;
    assert!(verify_under(&wrong_key, &packet, claim).is_err());
    packet[32] = 0;
    assert!(verify_under(&key, &packet, claim).is_err());
    Ok(())
  }

  #[test]
  fn malformed_envelopes_fail_before_key_access() {
    assert_eq!(PROOF_TAG, b"IXBN\0\0\0\x03");
    for length in [0, 32, 195, 197, 227, 229, 1 << 20] {
      assert!(
        verify(&vec![0; length], b"claim", false)
          .unwrap_err()
          .to_string()
          .contains("packet length")
      );
    }
  }
}

#[cfg(all(test, feature = "groth16"))]
mod native_tests {
  use super::*;

  #[test]
  #[ignore = "compiles the full Init verifier circuit"]
  fn compiles_init_without_changing_constraints() -> Result<()> {
    let directory = crate::test_support::TempDir::new("groth16-compile");
    let schema =
      include_bytes!("../../../../tools/gnark/testdata/bn254/vk.json");
    let path = directory.join("circuit.bin");
    let info = gnark::compile_groth16(schema, &path)?;
    let expected: serde_json::Value = serde_json::from_str(include_str!(
      "../../tests/fixtures/groth16/provenance.json"
    ))?;
    assert_eq!(
      u64::try_from(info.constraints)?,
      expected["constraints"].as_u64().unwrap()
    );
    assert_eq!(info.domain, expected["domain"].as_u64().unwrap());
    assert_eq!(info.commitments, 1);
    assert_eq!(info.public_inputs, 2);
    assert_eq!(
      hex(&sha256(&path)?),
      expected["circuit_sha256"].as_str().unwrap()
    );
    Ok(())
  }

  #[test]
  #[ignore = "requires prepared Init proving artifacts and several GiB of memory"]
  fn retained_init_prover_reuses_keys() -> Result<()> {
    let dir = PathBuf::from(std::env::var("IX_GROTH16_ARTIFACTS")?);
    let metadata: Metadata = load_json(&dir.join("manifest.json"))?;
    metadata.validate()?;
    let provenance: serde_json::Value = serde_json::from_str(include_str!(
      "../../tests/fixtures/groth16/provenance.json"
    ))?;
    assert_eq!(
      metadata.artifact("verifying-key.bin")?.sha256,
      provenance["files"]["verifying-key.bin"].as_str().unwrap()
    );
    let key = include_bytes!("../../tests/fixtures/groth16/verifying-key.bin");
    let expected_key = digest(&metadata.artifact("verifying-key.bin")?.sha256)?;
    let claim = digest(provenance["claim_digest"].as_str().unwrap())?;
    let witness =
      include_bytes!("../../../../tools/gnark/testdata/bn254/witness.json");
    let mut prover =
      gnark::Prover::open_groth16(&dir, &metadata, &proving_backend()?)?;
    let first = prover.prove(witness, &claim)?;
    let second = prover.prove(witness, &claim)?;
    for proof in [&first, &second] {
      gnark::verify_groth16(key, &expected_key, &proof.native, &claim)?;
      assert_eq!(proof.native.len(), 196);
      assert_eq!(proof.solidity.len(), 384);
    }
    assert_ne!(first.native, second.native);
    let mut wrong = claim;
    wrong[0] ^= 1;
    assert!(prover.prove(witness, &wrong).is_err());
    assert!(prover.prove(witness, &claim).is_err());
    prover.close()?;
    Ok(())
  }
}
