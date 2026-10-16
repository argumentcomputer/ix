//! Terminal PLONK worker operations and authenticated parameter interchange.
use super::{
  Result, fixed_cache,
  setup::{SetupClass, SetupConfig},
  statement, storage, wrap,
};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use std::{
  fs,
  io::{Read, Write},
  path::{Path, PathBuf},
  process::{Command, Stdio},
};

pub(super) const PROOF_TAG: &[u8; 8] = b"IXCMP\0\0\x05";
const HELPER: &str = "ix-bls-plonk-wrapper";
const CATALOG_VAR: &str = "IX_PLONK_VERIFIER_CATALOG";
const MAX_PROOF_BYTES: usize = 1 << 20;

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustedCatalog {
  format: String,
  keys: Vec<TrustedKey>,
}

#[derive(serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustedKey {
  sha256: String,
  path: PathBuf,
  inner_profile_id: String,
  statement_prefix: [u64; 10],
  circuit_sha256: String,
  helper_sha256: String,
  setup: String,
}

struct Scratch(PathBuf);
impl Scratch {
  fn new() -> Result<Self> {
    let path = storage::temporary_path(&std::env::temp_dir().join("ix-plonk"));
    fs::create_dir(&path)?;
    Ok(Self(path))
  }
}
impl Drop for Scratch {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.0);
  }
}

fn hex(bytes: &[u8]) -> String {
  use std::fmt::Write as _;
  let mut text = String::with_capacity(bytes.len() * 2);
  for byte in bytes {
    write!(text, "{byte:02x}").unwrap();
  }
  text
}

fn digest(text: &str) -> Result<[u8; 32]> {
  let text = text.strip_prefix("0x").unwrap_or(text);
  if text.len() != 64 || !text.is_ascii() {
    return Err("expected a 32-byte hexadecimal digest".into());
  }
  let mut bytes = [0; 32];
  for (i, byte) in bytes.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&text[2 * i..2 * i + 2], 16)?;
  }
  Ok(bytes)
}

fn sha256(path: &Path) -> Result<[u8; 32]> {
  let mut file = fs::File::open(path)?;
  let mut hash = Sha256::new();
  let mut buffer = vec![0; 65536];
  loop {
    let count = file.read(&mut buffer)?;
    if count == 0 {
      break;
    }
    hash.update(&buffer[..count]);
  }
  Ok(hash.finalize().into())
}

fn load_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
  let mut bytes = Vec::new();
  fs::File::open(path)?.take((1 << 20) + 1).read_to_end(&mut bytes)?;
  if bytes.len() > 1 << 20 {
    return Err("PLONK metadata exceeds its size limit".into());
  }
  Ok(serde_json::from_slice(&bytes)?)
}

pub(super) fn helper_executable() -> Result<PathBuf> {
  let path = if let Some(path) = std::env::var_os("IX_PLONK_HELPER") {
    PathBuf::from(path)
  } else {
    std::env::current_exe()?.with_file_name(HELPER)
  };
  if !path.is_file() {
    return Err(
      format!(
        "{HELPER} is missing; install it beside ix or set IX_PLONK_HELPER"
      )
      .into(),
    );
  }
  Ok(path)
}

fn checked(command: &mut Command) -> Result<()> {
  let status = command
    .stdout(Stdio::from(std::io::stderr()))
    .stderr(Stdio::inherit())
    .status()?;
  if !status.success() {
    return Err(format!("PLONK helper failed ({status})").into());
  }
  Ok(())
}

fn filecoin_anchor_encoding() -> Result<String> {
  let anchors = crate::kzg::srs::filecoin::filecoin_anchors();
  let mut bytes = Vec::new();
  anchors.g1[0].serialize_compressed(&mut bytes)?;
  anchors.g2.serialize_compressed(&mut bytes)?;
  anchors.tau_g2.serialize_compressed(&mut bytes)?;
  Ok(hex(&bytes))
}

fn select_key(path: &Path, id: &[u8; 32]) -> Result<TrustedKey> {
  let catalog: TrustedCatalog = load_json(path)?;
  if catalog.format != "ix-bls-plonk-verifiers-v1" {
    return Err("unsupported PLONK verifier catalog".into());
  }
  let mut selected = None;
  let mut seen = std::collections::BTreeSet::new();
  for key in catalog.keys {
    let key_id = digest(&key.sha256)?;
    digest(&key.inner_profile_id)?;
    digest(&key.circuit_sha256)?;
    digest(&key.helper_sha256)?;
    if !seen.insert(key_id) {
      return Err("duplicate PLONK verifier key in catalog".into());
    }
    if key.setup != "filecoin" {
      return Err("PLONK catalog requires Filecoin keys".into());
    }
    let words = statement::with_claim(&key.statement_prefix, b"");
    statement::from_claims_bytes(&statement::to_claims_bytes(&words))?;
    if key_id == *id {
      selected = Some(key);
    }
  }
  let mut key = selected.ok_or(
    "PLONK proof uses a verification key not authorized by the catalog",
  )?;
  if key.path.is_relative() {
    key.path = path.parent().unwrap_or_else(|| Path::new(".")).join(&key.path);
  }
  Ok(key)
}

pub(super) fn verify(packet: &[u8], claim: &[u8]) -> Result<SetupClass> {
  if packet.len() <= 32 || packet.len() > MAX_PROOF_BYTES + 32 {
    return Err("invalid PLONK packet length".into());
  }
  let id = packet[..32].try_into()?;
  let catalog =
    std::env::var_os(CATALOG_VAR).map(PathBuf::from).ok_or_else(|| {
      format!(
        "set {CATALOG_VAR} to an independently trusted PLONK verifier catalog"
      )
    })?;
  let key = select_key(&catalog, id)?;
  if fs::metadata(&key.path)?.len() > 1 << 20 {
    return Err("PLONK verification key is too large".into());
  }
  let helper = helper_executable()?;
  let scratch = Scratch::new()?;
  let proof = scratch.0.join("proof.bin");
  storage::write_atomic(&proof, &packet[32..])?;
  checked(
    Command::new(helper)
      .arg("verify")
      .arg(&key.path)
      .arg(hex(id))
      .arg(&proof)
      .arg(blake3::hash(claim).to_hex().as_str())
      .arg(filecoin_anchor_encoding()?),
  )?;
  Ok(SetupClass::Filecoin)
}

pub(crate) fn run(args: &[String]) -> Result<()> {
  match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
    ["fixture", out] => wrap::plonk_fixture(Path::new(out)),
    ["export", verifier, packet, digest, statement, out] => {
      let expected = serde_json::from_slice(&fs::read(statement)?)?;
      wrap::plonk_export(Path::new(verifier), Path::new(packet), digest, &expected, Path::new(out))
    },
    ["srs", domain, out] => export_srs(domain.parse()?, Path::new(out)),
    ["profile-blake3", source, trusted, out] => {
      let source = fs::read(source)?;
      if *blake3::hash(&source).as_bytes() != digest(trusted)? { return Err("trusted source profile digest differs".into()); }
      let (bytes, id) = wrap::VerifierProfile::reencode_blake3(&source)?;
      storage::write_atomic(Path::new(out), &bytes)?;
      eprintln!("profile_id={} verifier_blake3={}", hex(&id), blake3::hash(&bytes).to_hex());
      Ok(())
    },
    ["wrap", verifier, packet, trusted, expected, cache, out] => {
      let expected = load_json(Path::new(expected))?;
      wrap_packet(Path::new(verifier), Path::new(packet), trusted, &expected, Path::new(cache), Path::new(out))
    },
    _ => Err("usage: ix-compression-worker plonk fixture <dir> | export <verifier.bin> <packet.bin> <trusted-blake3> <expected-statement.json> <dir> | srs <plonk-domain> <output> | wrap <verifier.bin> <packet.bin> <trusted-verifier-blake3> <expected-statement.json> <cache> <out>".into()),
  }
}

fn export_srs(domain: usize, path: &Path) -> Result<()> {
  export_parameters(domain, path, &SetupConfig::from_env(false)?)
}

fn export_parameters(
  domain: usize,
  path: &Path,
  config: &SetupConfig,
) -> Result<()> {
  if domain < 2 || !domain.is_power_of_two() {
    return Err("PLONK domain must be a power of two >= 2".into());
  }
  let count = domain.checked_add(3).ok_or("PLONK SRS length overflow")?;
  let prefix =
    count.checked_next_power_of_two().ok_or("PLONK SRS length overflow")?;
  let SetupConfig::Filecoin { manifest, .. } = config else {
    return Err("PLONK requires authenticated Filecoin parameters".into());
  };
  let source = config.for_stage(b"ix/bls-plonk/srs/v1", prefix)?;
  let srs = source.srs(prefix, false)?;
  let temporary = storage::temporary_path(path);
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent)?;
  }
  let mut out = std::io::BufWriter::new(fs::File::create(&temporary)?);
  out.write_all(b"IXPSRS01")?;
  out.write_all(&srs.public_setup.id)?;
  out.write_all(&(srs.public_setup.max_degree as u64).to_le_bytes())?;
  out.write_all(manifest)?;
  out.write_all(&(count as u64).to_le_bytes())?;
  srs.g2.serialize_compressed(&mut out)?;
  srs.tau_g2.serialize_compressed(&mut out)?;
  for point in &srs.g1[..count] {
    out.write_all(&point.x.into_bigint().to_bytes_be())?;
    out.write_all(&point.y.into_bigint().to_bytes_be())?;
  }
  out.flush()?;
  drop(out);
  storage::persist(&temporary, path)?;
  let mut hash = blake3::Hasher::new();
  hash.update_mmap_rayon(path)?;
  let receipt = serde_json::json!({
    "format": "ix-plonk-srs-export-v1", "blake3": hash.finalize().to_hex().as_str(),
    "setupId": blake3::Hash::from_bytes(srs.public_setup.id).to_hex().as_str(),
    "publicMaxDegree": srs.public_setup.max_degree, "powers": count,
    "filecoinManifest": blake3::Hash::from_bytes(*manifest).to_hex().as_str(),
  });
  storage::write_atomic(
    &path.with_extension("json"),
    &serde_json::to_vec_pretty(&receipt)?,
  )?;
  Ok(())
}

#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ParameterReceipt {
  format: String,
  blake3: String,
  setup_id: String,
  public_max_degree: usize,
  powers: usize,
  filecoin_manifest: String,
}

fn cached_parameters(
  domain: usize,
  root: &Path,
  config: &SetupConfig,
) -> Result<(PathBuf, String)> {
  let SetupConfig::Filecoin { manifest, .. } = config else {
    return Err("PLONK requires Filecoin parameters".into());
  };
  let anchors = crate::kzg::srs::filecoin::filecoin_anchors();
  let mut identity = blake3::Hasher::new();
  identity.update(b"ix/plonk-parameter-export/v1");
  identity.update(&anchors.public_setup.id);
  identity.update(manifest);
  identity.update(&u64::try_from(domain)?.to_le_bytes());
  let path = root.join(identity.finalize().to_hex().as_str()).join("srs.bin");
  let receipt_path = path.with_extension("json");
  if !receipt_path.try_exists()? {
    export_parameters(domain, &path, config)?;
  }
  let receipt: ParameterReceipt = load_json(&receipt_path)?;
  if receipt.format != "ix-plonk-srs-export-v1"
    || digest(&receipt.setup_id)? != anchors.public_setup.id
    || digest(&receipt.filecoin_manifest)? != *manifest
    || receipt.public_max_degree != anchors.public_setup.max_degree
    || receipt.powers
      != domain.checked_add(3).ok_or("PLONK SRS length overflow")?
  {
    return Err("cached PLONK parameter identity differs".into());
  }
  let mut hash = blake3::Hasher::new();
  hash.update_mmap_rayon(&path)?;
  if *hash.finalize().as_bytes() != digest(&receipt.blake3)? {
    return Err("cached PLONK parameter export is damaged".into());
  }
  Ok((path, receipt.blake3))
}

fn metadata_string<'a>(
  value: &'a serde_json::Value,
  field: &str,
) -> Result<&'a str> {
  value
    .get(field)
    .and_then(serde_json::Value::as_str)
    .ok_or_else(|| format!("missing PLONK metadata field {field}").into())
}

fn claim_digest(expected: &statement::Statement) -> Result<[u8; 32]> {
  let mut digest = [0; 32];
  for (chunk, value) in
    digest.as_chunks_mut::<4>().0.iter_mut().zip(&expected[10..])
  {
    *chunk = u32::try_from(*value)?.to_le_bytes();
  }
  Ok(digest)
}

fn wrap_packet(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &statement::Statement,
  cache_root: &Path,
  out: &Path,
) -> Result<()> {
  statement::from_claims_bytes(&statement::to_claims_bytes(expected))?;
  let expected_digest = claim_digest(expected)?;
  let setup = SetupConfig::from_env(false)?;
  let SetupConfig::Filecoin { manifest, .. } = &setup else {
    return Err("PLONK requires Filecoin parameters".into());
  };
  let helper = helper_executable()?;
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("PLONK output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::plonk_export(verifier, packet, trusted_digest, expected, &input)?;
  let profile_path = input.join("profile.json");
  let exported: serde_json::Value = load_json(&profile_path)?;
  let mut identity = blake3::Hasher::new();
  identity.update(b"ix/bls-plonk-cache/v1");
  identity.update(&fixed_cache::executable_digest()?);
  identity.update(&sha256(&helper)?);
  identity.update(&sha256(&profile_path)?);
  identity.update(manifest);
  let cache =
    cache_root.join("circuits").join(identity.finalize().to_hex().as_str());
  checked(Command::new(&helper).arg("compile").arg(&profile_path).arg(&cache))?;
  let mut metadata: serde_json::Value =
    load_json(&cache.join("manifest.json"))?;
  let domain = usize::try_from(
    metadata
      .get("Domain")
      .and_then(serde_json::Value::as_u64)
      .ok_or("missing PLONK domain")?,
  )?;
  if domain < 2 || !domain.is_power_of_two() || domain > 1 << 26 {
    return Err(
      "PLONK domain exceeds the authenticated adapter capacity".into(),
    );
  }
  if metadata.get("KeysReady").and_then(serde_json::Value::as_bool)
    != Some(true)
  {
    let (srs, receipt) =
      cached_parameters(domain, &cache_root.join("parameters"), &setup)?;
    checked(
      Command::new(&helper)
        .arg("prepare")
        .arg(&cache)
        .arg(srs)
        .arg(receipt)
        .env("IX_PLONK_LAGRANGE_CACHE", cache_root.join("lagrange")),
    )?;
    metadata = load_json(&cache.join("manifest.json"))?;
  }
  checked(
    Command::new(&helper)
      .arg("prove")
      .arg(&cache)
      .arg(input.join("witness.json"))
      .arg(out),
  )?;
  let key_hash =
    metadata_string(&metadata["Files"]["verifying-key.bin"], "SHA256")?;
  let key_id = digest(key_hash)?;
  let key = cache.join("verifying-key.bin");
  checked(
    Command::new(&helper)
      .arg("verify")
      .arg(&key)
      .arg(key_hash)
      .arg(out.join("proof.bin"))
      .arg(hex(&expected_digest))
      .arg(filecoin_anchor_encoding()?),
  )?;
  let proof = fs::read(out.join("proof.bin"))?;
  if proof.is_empty() || proof.len() > MAX_PROOF_BYTES {
    return Err("invalid native PLONK proof length".into());
  }
  let mut envelope = PROOF_TAG.to_vec();
  envelope.extend(key_id);
  envelope.extend(proof);
  storage::write_atomic(&out.join("proof.envelope.bin"), &envelope)?;
  storage::write_atomic(&out.join("verifying-key.bin"), &fs::read(&key)?)?;
  storage::write_atomic(
    &out.join("PlonkVerifier.sol"),
    &fs::read(cache.join("PlonkVerifier.sol"))?,
  )?;
  let candidate = TrustedCatalog {
    format: "ix-bls-plonk-verifiers-v1".into(),
    keys: vec![TrustedKey {
      sha256: key_hash.into(),
      path: "verifying-key.bin".into(),
      inner_profile_id: metadata_string(&exported, "profileId")?.into(),
      statement_prefix: expected[..10].try_into()?,
      circuit_sha256: metadata_string(
        &metadata["Files"]["circuit.bin"],
        "SHA256",
      )?
      .into(),
      helper_sha256: metadata_string(&metadata, "ExecutableSHA256")?.into(),
      setup: "filecoin".into(),
    }],
  };
  storage::write_atomic(
    &out.join("verifier-catalog.candidate.json"),
    &serde_json::to_vec_pretty(&candidate)?,
  )?;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn key() -> TrustedKey {
    TrustedKey {
      sha256: hex(&[1; 32]),
      path: "verifier.bin".into(),
      inner_profile_id: hex(&[2; 32]),
      statement_prefix: [0; 10],
      circuit_sha256: hex(&[3; 32]),
      helper_sha256: hex(&[4; 32]),
      setup: "filecoin".into(),
    }
  }

  #[test]
  fn catalog_requires_an_independently_authorized_key() -> Result<()> {
    let scratch = Scratch::new()?;
    let path = scratch.0.join("catalog.json");
    let mut catalog = TrustedCatalog {
      format: "ix-bls-plonk-verifiers-v1".into(),
      keys: vec![key()],
    };
    let write = |catalog: &TrustedCatalog| {
      storage::write_atomic(&path, &serde_json::to_vec(catalog).unwrap())
    };
    write(&catalog)?;
    assert_eq!(
      select_key(&path, &[1; 32])?.path,
      scratch.0.join("verifier.bin")
    );
    assert!(select_key(&path, &[5; 32]).is_err());
    catalog.keys.push(key());
    write(&catalog)?;
    assert!(select_key(&path, &[1; 32]).is_err());
    catalog.keys.pop();
    catalog.keys[0].setup = "development".into();
    write(&catalog)?;
    assert!(select_key(&path, &[1; 32]).is_err());
    catalog.keys[0].setup = "filecoin".into();
    catalog.keys[0].statement_prefix[0] = u64::MAX;
    write(&catalog)?;
    assert!(select_key(&path, &[1; 32]).is_err());
    assert!(digest("é").is_err());
    assert!(verify(&[], b"claim").is_err());
    Ok(())
  }

  #[test]
  fn parameter_cache_preserves_filecoin_receipt_and_rejects_corruption()
  -> Result<()> {
    use crate::kzg::srs::filecoin::{
      FILECOIN_PREFIX_2P8_FIXTURE, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
    };
    let scratch = Scratch::new()?;
    let setup = SetupConfig::Filecoin {
      cache: FILECOIN_PREFIX_2P8_FIXTURE.into(),
      manifest: FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
    };
    let (path, receipt) = cached_parameters(8, &scratch.0, &setup)?;
    assert_eq!(fs::metadata(&path)?.len(), 280 + 96 * 11);
    let (again, same_receipt) = cached_parameters(8, &scratch.0, &setup)?;
    assert_eq!(again, path);
    assert_eq!(same_receipt, receipt);
    let mut bytes = fs::read(&path)?;
    *bytes.last_mut().unwrap() ^= 1;
    fs::write(&path, bytes)?;
    assert!(cached_parameters(8, &scratch.0, &setup).is_err());
    Ok(())
  }
}
