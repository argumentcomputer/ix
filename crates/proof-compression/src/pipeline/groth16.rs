//! Terminal BN254 Groth16 proofs under the release key.
#[cfg(feature = "groth16")]
use super::gnark;
#[cfg(feature = "groth16")]
use super::storage;
#[cfg(all(test, feature = "groth16"))]
use super::terminal::Scratch;
#[cfg(feature = "groth16")]
use super::terminal::{hex, sha256};
use super::{
  Result,
  setup::SetupClass,
  statement,
  terminal::{Artifact, digest, load_json},
  verifying_keys,
};
#[cfg(feature = "groth16")]
use super::{
  setup::SetupConfig,
  terminal::{claim_digest, read_bounded},
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
  if packet[..32] != verifying_keys::decode(verifying_keys::GROTH16_VK_SHA256) {
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
  verify_under(verifying_keys::GROTH16_VK, packet, claim)?;
  verifying_keys::groth16_setup(allow_development)
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
    || m.inner_vk != verifying_keys::TERMINAL_SCHEMA_SHA256
    || m.artifact("circuit.bin")?.sha256
      != verifying_keys::GROTH16_CIRCUIT_SHA256
    || m.setup != "development"
    || m.ceremony.is_some()
  {
    return Err(
      "Groth16 artifacts differ from the release circuit and key".into(),
    );
  }
  for name in ["proving-key.bin", "Groth16Verifier.sol"] {
    m.artifact(name)?;
  }
  verifying_keys::groth16_setup(allow_development)?;
  Ok(dir)
}

pub(super) fn preflight(allow_development: bool) -> Result<()> {
  match std::env::var("IX_GROTH16_BACKEND").as_deref() {
    Err(std::env::VarError::NotPresent) | Ok("" | "cpu" | "cuda") => {},
    _ => return Err("IX_GROTH16_BACKEND must be cpu or cuda".into()),
  }
  prepared(allow_development)?;
  Ok(())
}

pub(super) fn check_statement(
  expected: &statement::Statement,
  allow_development: bool,
) -> Result<()> {
  prepared(allow_development)?;
  if expected[..10] != verifying_keys::STATEMENT_PREFIX {
    return Err(
      "the release Groth16 key proves another aggregation program".into(),
    );
  }
  Ok(())
}

/// Prove the recursive KZG packet in `packet` in Groth16 under the prepared
/// artifacts `IX_GROTH16_ARTIFACTS` names, and write its envelope, verifying
/// key and Solidity verifier to the empty directory `out`.
#[cfg(feature = "groth16")]
pub(super) fn wrap_packet(
  verifier: &Path,
  packet: &Path,
  trusted: &str,
  expected: &statement::Statement,
  out: &Path,
  allow_development: bool,
  setup: &SetupConfig,
) -> Result<()> {
  statement::from_claims_bytes(&statement::to_claims_bytes(expected))?;
  let artifacts = prepared(allow_development)?;
  if expected[..10] != verifying_keys::STATEMENT_PREFIX {
    return Err(
      "the release Groth16 key proves another aggregation program".into(),
    );
  }
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("Groth16 output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::plonk_export(verifier, packet, trusted, expected, &input, setup)?;
  let exported: serde_json::Value = load_json(&input.join("vk.json"))?;
  let inner_id =
    exported["vkId"].as_str().ok_or("missing exported inner key identity")?;
  if digest(inner_id)?
    != verifying_keys::decode(verifying_keys::RECURSIVE_VK_ID)
    || sha256(&input.join("vk.json"))?
      != verifying_keys::decode(verifying_keys::TERMINAL_SCHEMA_SHA256)
  {
    return Err(
      "Groth16 circuit was compiled for a different verifier description"
        .into(),
    );
  }
  let claim = claim_digest(expected)?;
  prove(&artifacts, &input.join("witness.json"), &claim, out)?;
  let key_id = verifying_keys::decode(verifying_keys::GROTH16_VK_SHA256);
  gnark::verify_groth16(
    verifying_keys::GROTH16_VK,
    &key_id,
    &read_bounded(&out.join("proof.bin"), MAX_PROOF_BYTES)?,
    &claim,
  )?;
  let proof = fs::read(out.join("proof.bin"))?;
  if !matches!(proof.len(), 164 | MAX_PROOF_BYTES) {
    return Err("invalid native Groth16 proof length".into());
  }
  let mut envelope = PROOF_TAG.to_vec();
  envelope.extend(key_id);
  envelope.extend(proof);
  for name in ["verifying-key.bin", "Groth16Verifier.sol"] {
    storage::write_atomic(&out.join(name), &fs::read(artifacts.join(name))?)?;
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
  super::prepare_output(out)?;
  let schema = read_bounded(schema, 16 << 20)?;
  let info = gnark::compile_groth16(&schema, &out.join("circuit.bin"))?;
  storage::write_atomic(&out.join("vk.json"), &schema)?;
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

/// Prepare known-trapdoor development keys for the circuit compiled in
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
      let pin_keys = match std::env::var("IX_GROTH16_PIN_KEY").as_deref() {
        Err(std::env::VarError::NotPresent) | Ok("" | "0") => false,
        Ok("1") => true,
        _ => return Err("IX_GROTH16_PIN_KEY must be 0 or 1".into()),
      };
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
      Ok(gnark::Groth16Backend::Cuda { device, pin_keys, library })
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
    let directory = Scratch::new()?;
    let schema =
      include_bytes!("../../../../tools/plonk-wrapper/testdata/bn254/vk.json");
    let path = directory.0.join("circuit.bin");
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
    let witness = include_bytes!(
      "../../../../tools/plonk-wrapper/testdata/bn254/witness.json"
    );
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
