//! Terminal BN254 Groth16 proofs under independently admitted circuit keys.
use super::{
  Result,
  setup::SetupClass,
  statement, storage,
  terminal::{Scratch, checked, claim_digest, digest, hex, load_json, sha256},
  wrap,
};
use std::{
  fs,
  path::{Path, PathBuf},
  process::Command,
};

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
  if !matches!(packet.len(), 196 | 228) {
    return Err("invalid Groth16 packet length".into());
  }
  verify_with_catalog(
    packet,
    claim,
    &catalog_path()?,
    &super::terminal::helper_executable("IX_GROTH16_HELPER")?,
    allow_development,
  )
}

fn verify_with_catalog(
  packet: &[u8],
  claim: &[u8],
  catalog: &Path,
  helper: &Path,
  allow_development: bool,
) -> Result<SetupClass> {
  if !matches!(packet.len(), 196 | 228) {
    return Err("invalid Groth16 packet length".into());
  }
  let id = packet[..32].try_into()?;
  let key = select_key(catalog, id, allow_development)?;
  if fs::metadata(&key.path)?.len() > 1 << 20 || sha256(&key.path)? != *id {
    return Err(
      "Groth16 verifying key differs from the trusted catalog".into(),
    );
  }
  let scratch = Scratch::new()?;
  let proof = scratch.0.join("proof.bin");
  storage::write_atomic(&proof, &packet[32..])?;
  checked(
    Command::new(helper)
      .arg("groth16")
      .arg("verify")
      .env("CUDA_VISIBLE_DEVICES", "")
      .arg(&key.path)
      .arg(hex(id))
      .arg(proof)
      .arg(blake3::hash(claim).to_hex().as_str()),
  )?;
  key.setup_class(allow_development)
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct Metadata {
  format: String,
  curve: String,
  #[serde(rename = "innerVKSHA256")]
  inner_vk: String,
  commitment_hash: String,
  constraints: usize,
  domain: u64,
  public_inputs: usize,
  commitments: usize,
  setup: String,
  #[serde(default, rename = "ceremonySHA256")]
  ceremony: Option<String>,
  keys_ready: bool,
  files: std::collections::BTreeMap<String, Artifact>,
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
  #[serde(rename = "SHA256")]
  sha256: String,
  #[serde(rename = "Bytes")]
  bytes: u64,
}

impl Metadata {
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
  if m.format != "ix-bn254-groth16-artifacts-v1"
    || m.curve != "bn254"
    || m.commitment_hash != "sha256"
    || !m.keys_ready
    || m.public_inputs != 2
    || m.commitments > 1
    || m.constraints == 0
    || m.constraints > 1 << 27
    || m.domain != u64::try_from(m.constraints)?.next_power_of_two()
  {
    return Err("unsupported or unprepared Groth16 artifact metadata".into());
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
  let helper = super::terminal::helper_executable("IX_GROTH16_HELPER")?;
  let output =
    Command::new(helper).args(["groth16", "capabilities"]).output()?;
  if !output.status.success() {
    return Err("terminal helper does not support Groth16".into());
  }
  let capabilities: serde_json::Value = serde_json::from_slice(&output.stdout)?;
  if capabilities["system"] != "groth16" || capabilities["curve"] != "bn254" {
    return Err(
      "terminal helper reports another Groth16 system or curve".into(),
    );
  }
  match std::env::var("IX_GROTH16_BACKEND").as_deref() {
    Err(_) | Ok("" | "cpu") => {},
    Ok("cuda") if capabilities["cuda"] == true => {},
    Ok("cuda") => {
      return Err(
        "terminal helper was built without CUDA Groth16 support".into(),
      );
    },
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
  let helper = super::terminal::helper_executable("IX_GROTH16_HELPER")?;
  checked(
    Command::new(&helper)
      .arg("groth16")
      .arg("prove")
      .arg(&artifacts)
      .arg(input.join("witness.json"))
      .arg(hex(&claim))
      .arg(out),
  )?;
  checked(
    Command::new(&helper)
      .arg("groth16")
      .arg("verify")
      .arg(&key.path)
      .arg(&key.sha256)
      .arg(out.join("proof.bin"))
      .arg(hex(&claim)),
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
    ["export", verifier, packet, trusted, expected, out] => {
      let expected = load_json(Path::new(expected))?;
      wrap::plonk_export(Path::new(verifier), Path::new(packet), trusted, &expected, Path::new(out))
    },
    ["verify", proof, claim] => {
      let bytes = fs::read(proof)?;
      let packet = bytes.strip_prefix(PROOF_TAG).ok_or("unsupported Groth16 proof curve or version")?;
      let setup = verify(packet, &fs::read(claim)?, allow_development)?;
      println!("{}", serde_json::json!({"verified": true, "curve": "bn254", "setup": setup.label()}));
      Ok(())
    },
    ["wrap", verifier, packet, trusted, expected, out] => {
      let expected = load_json(Path::new(expected))?;
      wrap_packet(Path::new(verifier), Path::new(packet), trusted, &expected, Path::new(out), allow_development)
    },
    _ => Err("usage: ix-compression-worker groth16 export <verifier.bin> <packet.bin> <trusted-inner-blake3> <expected-statement.json> <out> | wrap <verifier.bin> <packet.bin> <trusted-inner-blake3> <expected-statement.json> <out> [--allow-development] | verify <proof.envelope.bin> <claim.bin> [--allow-development]".into()),
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  #[ignore = "requires a compiled terminal helper in IX_GROTH16_HELPER"]
  fn saved_init_groth16_proof_verifies_without_gpu() -> Result<()> {
    let helper =
      super::super::terminal::helper_executable("IX_GROTH16_HELPER")?;
    let dir =
      Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/groth16");
    let provenance: serde_json::Value =
      load_json(&dir.join("provenance.json"))?;
    let bytes = fs::read(dir.join("proof.bin"))?;
    let vk = dir.join("verifying-key.bin");
    let id = sha256(&vk)?;
    let claim = include_bytes!("../../tests/fixtures/init-fri/claim.bin");
    assert_eq!(
      blake3::hash(claim).to_hex().as_str(),
      provenance["claim_digest"].as_str().unwrap()
    );
    let mut packet = id.to_vec();
    packet.extend(bytes);
    let key = TrustedKey {
      sha256: hex(&id),
      path: vk,
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
    assert!(
      verify_with_catalog(&packet, claim, &catalog, &helper, false).is_err()
    );
    assert_eq!(
      verify_with_catalog(&packet, claim, &catalog, &helper, true)?,
      SetupClass::Development
    );
    assert!(
      verify_with_catalog(&packet, b"another claim", &catalog, &helper, true)
        .is_err()
    );
    packet[32] = 0;
    assert!(
      verify_with_catalog(&packet, claim, &catalog, &helper, true).is_err()
    );
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
  fn malformed_envelopes_fail_before_key_or_helper_access() {
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
