//! Terminal BN254 Groth16 proofs under independently admitted circuit keys.
#[cfg(feature = "groth16")]
use super::gnark;
use super::storage;
#[cfg(any(not(feature = "groth16"), test))]
use super::terminal::Scratch;
#[cfg(not(feature = "groth16"))]
use super::terminal::checked;
#[cfg(any(feature = "groth16", test))]
use super::terminal::sha256;
use super::{
  Result,
  setup::SetupClass,
  statement,
  terminal::{Artifact, digest, hex, load_json},
};
#[cfg(feature = "groth16")]
use super::{
  terminal::{claim_digest, read_bounded},
  wrap,
};
#[cfg(any(feature = "groth16", test))]
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(not(feature = "groth16"))]
use std::process::Command;

pub(super) const PROOF_TAG: &[u8; 8] = b"IXBN\0\0\0\x03";
const CATALOG_FORMAT: &str = "ix-bn254-groth16-verifiers-v1";
const CATALOG_VAR: &str = "IX_GROTH16_VERIFIER_CATALOG";
const ARTIFACTS_VAR: &str = "IX_GROTH16_ARTIFACTS";
const MAX_PROOF_BYTES: usize = 196;

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustedCatalog {
  format: String,
  keys: Vec<TrustedKey>,
}

#[derive(Clone, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustedKey {
  sha256: String,
  path: PathBuf,
  inner_vk_id: String,
  inner_schema_sha256: String,
  statement_prefix: [u64; 10],
  circuit_sha256: String,
  setup: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  ceremony_sha256: Option<String>,
}

impl TrustedKey {
  fn setup_class(&self, allow_development: bool) -> Result<SetupClass> {
    match self.setup.as_str() {
      "mpc" => {
        digest(self.ceremony_sha256.as_deref().ok_or("missing Groth16 ceremony identity")?)?;
        Ok(SetupClass::Groth16)
      },
      "development" if allow_development && self.ceremony_sha256.is_none() => Ok(SetupClass::Development),
      "development" => Err("development Groth16 keys require explicit --allow-development or --dev-srs verification".into()),
      _ => Err("unsupported Groth16 setup class".into()),
    }
  }
}

fn catalog_path() -> Result<PathBuf> {
  std::env::var_os(CATALOG_VAR).map(PathBuf::from).ok_or_else(|| {
    format!(
      "set {CATALOG_VAR} to an independently trusted Groth16 verifier catalog"
    )
    .into()
  })
}

fn select_key(
  path: &Path,
  id: &[u8; 32],
  allow_development: bool,
) -> Result<TrustedKey> {
  let catalog: TrustedCatalog = load_json(path)?;
  if catalog.format != CATALOG_FORMAT {
    return Err("unsupported Groth16 verifier catalog".into());
  }
  let mut selected = None;
  let mut seen = std::collections::BTreeSet::new();
  for mut key in catalog.keys {
    let key_id = digest(&key.sha256)?;
    key.sha256 = hex(&key_id);
    key.inner_vk_id = hex(&digest(&key.inner_vk_id)?);
    key.inner_schema_sha256 = hex(&digest(&key.inner_schema_sha256)?);
    key.circuit_sha256 = hex(&digest(&key.circuit_sha256)?);
    if let Some(value) = &mut key.ceremony_sha256 {
      *value = hex(&digest(value)?);
    }
    if !seen.insert(key_id) {
      return Err("duplicate Groth16 verifying key in catalog".into());
    }
    let words = statement::with_claim(&key.statement_prefix, b"");
    statement::from_claims_bytes(&statement::to_claims_bytes(&words))?;
    key.setup_class(true)?;
    if key_id == *id {
      key.setup_class(allow_development)?;
      if key.path.is_relative() {
        key.path =
          path.parent().unwrap_or_else(|| Path::new(".")).join(&key.path);
      }
      selected = Some(key);
    }
  }
  selected.ok_or(
    "Groth16 proof uses a verifying key not authorized by the catalog".into(),
  )
}

pub(super) fn verify(
  packet: &[u8],
  claim: &[u8],
  allow_development: bool,
) -> Result<SetupClass> {
  if packet.len() != 164 + 32 && packet.len() != MAX_PROOF_BYTES + 32 {
    return Err("invalid Groth16 packet length".into());
  }
  verify_with_catalog(packet, claim, &catalog_path()?, allow_development)
}

fn verify_with_catalog(
  packet: &[u8],
  claim: &[u8],
  catalog: &Path,
  allow_development: bool,
) -> Result<SetupClass> {
  if packet.len() != 164 + 32 && packet.len() != MAX_PROOF_BYTES + 32 {
    return Err("invalid Groth16 packet length".into());
  }
  let id = packet[..32].try_into()?;
  let key = select_key(catalog, id, allow_development)?;
  let expected = *blake3::hash(claim).as_bytes();
  #[cfg(feature = "groth16")]
  gnark::verify_groth16(
    &read_bounded(&key.path, 1 << 20)?,
    id,
    &packet[32..],
    &expected,
  )?;
  #[cfg(not(feature = "groth16"))]
  {
    let scratch = Scratch::new()?;
    let proof = scratch.0.join("proof.bin");
    storage::write_atomic(&proof, &packet[32..])?;
    checked(
      Command::new(super::worker_executable()?)
        .args(["groth16", "verify-key"])
        .arg(&key.path)
        .arg(hex(id))
        .arg(proof)
        .arg(hex(&expected)),
    )?;
  }
  key.setup_class(allow_development)
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

fn prepared(allow_development: bool) -> Result<(PathBuf, TrustedKey)> {
  let dir =
    std::env::var_os(ARTIFACTS_VAR).map(PathBuf::from).ok_or_else(|| {
      format!("set {ARTIFACTS_VAR} to prepared Groth16 circuit artifacts")
    })?;
  let m: Metadata = load_json(&dir.join("manifest.json"))?;
  m.validate()?;
  if !m.keys_ready {
    return Err("Groth16 keys are not prepared".into());
  }
  let key = select_key(
    &catalog_path()?,
    &digest(&m.artifact("verifying-key.bin")?.sha256)?,
    allow_development,
  )?;
  if m.inner_vk != key.inner_schema_sha256
    || m.artifact("vk.json")?.sha256 != key.inner_schema_sha256
    || m.artifact("circuit.bin")?.sha256 != key.circuit_sha256
    || m.setup != key.setup
    || m.ceremony != key.ceremony_sha256
  {
    return Err(
      "Groth16 artifacts differ from the admitted circuit and setup".into(),
    );
  }
  for name in ["proving-key.bin", "Groth16Verifier.sol"] {
    m.artifact(name)?;
  }
  Ok((dir, key))
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
  let (_, key) = prepared(allow_development)?;
  if expected[..10] != key.statement_prefix {
    return Err(
      "Groth16 catalog authorizes another aggregation program".into(),
    );
  }
  Ok(())
}

#[cfg(feature = "groth16")]
fn wrap_packet(
  verifier: &Path,
  packet: &Path,
  trusted: &str,
  expected: &statement::Statement,
  out: &Path,
  allow_development: bool,
) -> Result<()> {
  statement::from_claims_bytes(&statement::to_claims_bytes(expected))?;
  let (artifacts, key) = prepared(allow_development)?;
  if expected[..10] != key.statement_prefix {
    return Err("Groth16 key does not authorize this inner verifier and aggregation program".into());
  }
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("Groth16 output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::plonk_export(verifier, packet, trusted, expected, &input)?;
  let exported: serde_json::Value = load_json(&input.join("vk.json"))?;
  let inner_id =
    exported["vkId"].as_str().ok_or("missing exported inner key identity")?;
  if digest(inner_id)? != digest(&key.inner_vk_id)?
    || sha256(&input.join("vk.json"))? != digest(&key.inner_schema_sha256)?
  {
    return Err(
      "Groth16 circuit was compiled for a different verifier description"
        .into(),
    );
  }
  let claim = claim_digest(expected)?;
  prove(&artifacts, &input.join("witness.json"), &claim, out)?;
  gnark::verify_groth16(
    &read_bounded(&key.path, 1 << 20)?,
    &digest(&key.sha256)?,
    &read_bounded(&out.join("proof.bin"), MAX_PROOF_BYTES)?,
    &claim,
  )?;
  let proof = fs::read(out.join("proof.bin"))?;
  if !matches!(proof.len(), 164 | MAX_PROOF_BYTES) {
    return Err("invalid native Groth16 proof length".into());
  }
  let mut envelope = PROOF_TAG.to_vec();
  envelope.extend(digest(&key.sha256)?);
  envelope.extend(proof);
  for name in ["verifying-key.bin", "Groth16Verifier.sol"] {
    storage::write_atomic(&out.join(name), &fs::read(artifacts.join(name))?)?;
  }
  storage::write_atomic(&out.join("proof.envelope.bin"), &envelope)?;
  Ok(())
}

#[cfg(feature = "groth16")]
pub(crate) fn run(args: &[String]) -> Result<()> {
  let development_flags =
    args.iter().filter(|s| s.as_str() == "--allow-development").count();
  let production_flags =
    args.iter().filter(|s| s.as_str() == "--production").count();
  if development_flags > 1
    || production_flags > 1
    || development_flags + production_flags > 1
  {
    return Err("conflicting Groth16 setup policy flags".into());
  }
  let allow_development = development_flags == 1;
  let positional: Vec<_> = args
    .iter()
    .filter(|s| !matches!(s.as_str(), "--allow-development" | "--production"))
    .map(String::as_str)
    .collect();
  match positional.as_slice() {
    ["compile", schema, out] => compile(Path::new(schema), Path::new(out)),
    ["setup-development", dir] => setup(Path::new(dir), gnark::Groth16Setup::Development),
    ["setup-mpc", dir, descriptor, pin] => { digest(pin)?; setup(Path::new(dir), gnark::Groth16Setup::Ceremony { path:Path::new(descriptor),digest:pin }) },
    ["import", dir, descriptor, pin] => { digest(pin)?; setup(Path::new(dir), gnark::Groth16Setup::Import { path:Path::new(descriptor),digest:pin }) },
    ["prove", dir, witness, claim, out] => prove(Path::new(dir),Path::new(witness),&digest(claim)?,Path::new(out)),
    ["verify-key", key, pin, proof, claim] => gnark::verify_groth16(&read_bounded(Path::new(key), 1<<20)?, &digest(pin)?, &read_bounded(Path::new(proof), MAX_PROOF_BYTES)?, &digest(claim)?),
    ["export", verifier, packet, trusted, expected, out] => {
      let expected = load_json(Path::new(expected))?;
      wrap::plonk_export(Path::new(verifier), Path::new(packet), trusted, &expected, Path::new(out))
    },
    ["verify", proof, claim] => {
      let bytes = read_bounded(Path::new(proof), MAX_PROOF_BYTES + 32 + PROOF_TAG.len())?;
      let packet = bytes.strip_prefix(PROOF_TAG).ok_or("unsupported Groth16 proof curve or version")?;
      let setup = verify(packet, &fs::read(claim)?, allow_development)?;
      println!("{}", serde_json::json!({"verified": true, "curve": "bn254", "setup": setup.label()}));
      Ok(())
    },
    ["wrap", verifier, packet, trusted, expected, out] => {
      let expected = load_json(Path::new(expected))?;
      wrap_packet(Path::new(verifier), Path::new(packet), trusted, &expected, Path::new(out), allow_development)
    },
    _ => Err("usage: ix-compression-worker groth16 compile <vk.json> <empty-dir> | setup-development <dir> | setup-mpc <dir> <ceremony.json> <trusted-sha256> | import <dir> <release.json> <trusted-sha256> | prove <dir> <witness.json> <expected-claim-digest> <out> | export <verifier.bin> <packet.bin> <trusted-inner-blake3> <expected-statement.json> <out> | wrap <verifier.bin> <packet.bin> <trusted-inner-blake3> <expected-statement.json> <out> [--allow-development] | verify <proof.envelope.bin> <claim.bin> [--allow-development]".into()),
  }
}

#[cfg(feature = "groth16")]
fn artifact(path: &Path) -> Result<Artifact> {
  Ok(Artifact { sha256: hex(&sha256(path)?), bytes: fs::metadata(path)?.len() })
}

#[cfg(feature = "groth16")]
fn compile(schema: &Path, out: &Path) -> Result<()> {
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
    let key = TrustedKey {
      sha256: hex(&id),
      path: vk.clone(),
      inner_vk_id: provenance["inner_vk_id"].as_str().unwrap().into(),
      inner_schema_sha256: provenance["inner_schema_sha256"]
        .as_str()
        .unwrap()
        .into(),
      statement_prefix: serde_json::from_value(
        provenance["statement_prefix"].clone(),
      )?,
      circuit_sha256: provenance["circuit_sha256"].as_str().unwrap().into(),
      setup: "development".into(),
      ceremony_sha256: None,
    };
    let scratch = Scratch::new()?;
    let catalog = scratch.0.join("catalog.json");
    storage::write_atomic(
      &catalog,
      &serde_json::to_vec(&TrustedCatalog {
        format: CATALOG_FORMAT.into(),
        keys: vec![key],
      })?,
    )?;
    assert!(verify_with_catalog(&packet, claim, &catalog, false).is_err());
    assert_eq!(
      verify_with_catalog(&packet, claim, &catalog, true)?,
      SetupClass::Development
    );
    assert!(
      verify_with_catalog(&packet, b"another claim", &catalog, true).is_err()
    );
    let mut wrong_key = fs::read(&vk)?;
    wrong_key[0] ^= 1;
    assert!(
      gnark::verify_groth16(
        &wrong_key,
        &id,
        &packet[32..],
        &digest(provenance["claim_digest"].as_str().unwrap())?
      )
      .is_err()
    );
    packet[32] = 0;
    assert!(verify_with_catalog(&packet, claim, &catalog, true).is_err());
    Ok(())
  }

  #[test]
  fn catalog_requires_exact_key_identity_and_explicit_development() -> Result<()>
  {
    let scratch = Scratch::new()?;
    let path = scratch.0.join("catalog.json");
    let mut catalog = TrustedCatalog {
      format: CATALOG_FORMAT.into(),
      keys: vec![TrustedKey {
        sha256: hex(&[1; 32]),
        path: "key.bin".into(),
        inner_vk_id: hex(&[2; 32]),
        inner_schema_sha256: hex(&[3; 32]),
        statement_prefix: [0; 10],
        circuit_sha256: hex(&[4; 32]),
        setup: "development".into(),
        ceremony_sha256: None,
      }],
    };
    let save = |value: &TrustedCatalog| {
      storage::write_atomic(&path, &serde_json::to_vec(value).unwrap())
    };
    save(&catalog)?;
    assert!(select_key(&path, &[1; 32], false).is_err());
    assert_eq!(
      select_key(&path, &[1; 32], true)?.path,
      scratch.0.join("key.bin")
    );
    assert!(select_key(&path, &[9; 32], true).is_err());
    catalog.keys[0].setup = "mpc".into();
    save(&catalog)?;
    assert!(select_key(&path, &[1; 32], false).is_err());
    catalog.keys[0].ceremony_sha256 = Some(hex(&[5; 32]));
    save(&catalog)?;
    assert_eq!(
      select_key(&path, &[1; 32], false)?.setup_class(false)?,
      SetupClass::Groth16
    );
    catalog.keys.push(catalog.keys[0].clone());
    save(&catalog)?;
    assert!(select_key(&path, &[1; 32], false).is_err());
    assert_eq!(PROOF_TAG, b"IXBN\0\0\0\x03");
    Ok(())
  }

  #[test]
  fn malformed_envelopes_fail_before_key_access() {
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
