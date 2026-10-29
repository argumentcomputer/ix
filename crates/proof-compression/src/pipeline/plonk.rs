//! Terminal PLONK worker operations and authenticated parameter interchange.
use super::terminal::{
  Scratch, checked, claim_digest, digest, hex, load_json, sha256,
};
use super::{
  Result, fixed_cache,
  setup::{SetupClass, SetupConfig},
  statement, storage, wrap,
};
use ark_ff::{BigInteger, PrimeField};
use std::{
  fs,
  io::Write,
  path::{Path, PathBuf},
  process::Command,
};

pub(super) const PROOF_TAG: &[u8; 8] = b"IXBN\0\0\0\x02";
const CATALOG_FORMAT: &str = "ix-bn254-plonk-verifiers-v1";
const SETUP_NAME: &str = "ignition";
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
  inner_vk_id: String,
  statement_prefix: [u64; 10],
  circuit_sha256: String,
  helper_sha256: String,
  setup: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  admission: Option<PathBuf>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  admission_blake3: Option<String>,
}

pub(super) fn helper_executable() -> Result<PathBuf> {
  super::terminal::helper_executable("IX_PLONK_HELPER")
}

fn setup_manifest(config: &SetupConfig) -> Result<[u8; 32]> {
  match config {
    SetupConfig::Ignition { manifest, .. } => Ok(*manifest),
    _ => Err("PLONK requires authenticated ceremony parameters".into()),
  }
}

fn anchors(config: &SetupConfig) -> Result<crate::kzg::Srs> {
  setup_manifest(config)?;
  Ok(config.ignition_admission().ok_or("missing Ignition admission")?.anchors())
}

fn encode_g2(point: crate::kzg::curve::G2Affine) -> Vec<u8> {
  let mut bytes = Vec::new();
  for value in [point.x.c0, point.x.c1, point.y.c0, point.y.c1] {
    bytes.extend(value.into_bigint().to_bytes_be());
  }
  bytes
}

fn anchor_encoding(srs: &crate::kzg::Srs) -> String {
  let mut bytes = Vec::new();
  for value in [srs.g1[0].x, srs.g1[0].y] {
    bytes.extend(value.into_bigint().to_bytes_be());
  }
  bytes.extend(encode_g2(srs.g2));
  bytes.extend(encode_g2(srs.tau_g2));
  hex(&bytes)
}

fn key_anchors(key: &TrustedKey) -> Result<crate::kzg::Srs> {
  {
    Ok(
      crate::kzg::srs::ignition::IgnitionAdmission::read(
        key.admission.as_ref().ok_or("missing trusted admission path")?,
        digest(
          key
            .admission_blake3
            .as_ref()
            .ok_or("missing trusted admission pin")?,
        )?,
      )?
      .anchors(),
    )
  }
}

fn select_key(path: &Path, id: &[u8; 32]) -> Result<TrustedKey> {
  let catalog: TrustedCatalog = load_json(path)?;
  if catalog.format != CATALOG_FORMAT {
    return Err("unsupported PLONK verifier catalog".into());
  }
  let mut selected = None;
  let mut seen = std::collections::BTreeSet::new();
  for key in catalog.keys {
    let key_id = digest(&key.sha256)?;
    digest(&key.inner_vk_id)?;
    digest(&key.circuit_sha256)?;
    digest(&key.helper_sha256)?;
    if !seen.insert(key_id) {
      return Err("duplicate PLONK verifier key in catalog".into());
    }
    if key.setup != SETUP_NAME {
      return Err("PLONK catalog setup class differs".into());
    }
    {
      digest(
        key.admission_blake3.as_ref().ok_or("missing trusted admission pin")?,
      )?;
      if key.admission.is_none() {
        return Err("missing trusted admission path".into());
      }
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
  if let Some(admission) = &mut key.admission
    && admission.is_relative()
  {
    *admission =
      path.parent().unwrap_or_else(|| Path::new(".")).join(&*admission);
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
      .arg(anchor_encoding(&key_anchors(&key)?)),
  )?;
  Ok(SetupClass::Ignition)
}

pub(crate) fn run(args: &[String]) -> Result<()> {
  let development = args.iter().any(|arg| arg == "--dev-srs");
  let args: Vec<_> = args.iter().filter(|arg| *arg != "--dev-srs").collect();
  match args.iter().map(|s| s.as_str()).collect::<Vec<_>>().as_slice() {
    ["verify", proof, claim] => {
      let bytes = fs::read(proof)?;
      let packet = bytes.strip_prefix(PROOF_TAG).ok_or("unsupported PLONK proof curve or version")?;
      let setup = verify(packet, &fs::read(claim)?)?;
      println!("{}", serde_json::json!({"verified": true, "curve": crate::kzg::curve::NAME, "setup": setup.label()}));
      Ok(())
    },
    ["export", verifier, packet, digest, statement, out] => {
      let expected = serde_json::from_slice(&fs::read(statement)?)?;
      wrap::plonk_export(Path::new(verifier), Path::new(packet), digest, &expected, Path::new(out))
    },
    ["export-first", stage, statement, out] => {
      let expected = serde_json::from_slice(&fs::read(statement)?)?;
      wrap::plonk_export_first(Path::new(stage), &expected, Path::new(out), development)
    },
    ["srs", domain, out] => export_srs(domain.parse()?, Path::new(out)),
    ["wrap", verifier, packet, trusted, expected, cache, out] => {
      let expected = load_json(Path::new(expected))?;
      wrap_packet(Path::new(verifier), Path::new(packet), trusted, &expected, Path::new(cache), Path::new(out))
    },
    _ => Err("usage: ix-compression-worker plonk export <verifier.bin> <packet.bin> <trusted-blake3> <expected-statement.json> <dir> | export-first <first-kzg-dir> <expected-statement.json> <dir> [--dev-srs] | srs <plonk-domain> <output> | wrap <verifier.bin> <packet.bin> <trusted-verifier-blake3> <expected-statement.json> <cache> <out> | verify <proof.envelope.bin> <claim.bin>".into()),
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
  let manifest = setup_manifest(config)?;
  let source = config.for_stage(b"ix/bn254-plonk/srs/v1", prefix)?;
  let srs = source.srs(prefix, false)?;
  let temporary = storage::temporary_path(path);
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent)?;
  }
  let mut out = std::io::BufWriter::new(fs::File::create(&temporary)?);
  out.write_all(b"IXBPSR01")?;
  out.write_all(&srs.public_setup.id)?;
  out.write_all(&(srs.public_setup.max_degree as u64).to_le_bytes())?;
  out.write_all(&manifest)?;
  out.write_all(&(count as u64).to_le_bytes())?;
  out.write_all(&encode_g2(srs.g2))?;
  out.write_all(&encode_g2(srs.tau_g2))?;
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
    "format": "ix-bn254-plonk-srs-export-v1", "blake3": hash.finalize().to_hex().as_str(),
    "setupId": blake3::Hash::from_bytes(srs.public_setup.id).to_hex().as_str(),
    "publicMaxDegree": srs.public_setup.max_degree, "powers": count,
    ("ignitionManifest"): blake3::Hash::from_bytes(manifest).to_hex().as_str(),
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
  #[serde(rename = "ignitionManifest")]
  setup_manifest: String,
}

fn cached_parameters(
  domain: usize,
  root: &Path,
  config: &SetupConfig,
) -> Result<(PathBuf, String)> {
  let manifest = setup_manifest(config)?;
  let anchors = anchors(config)?;
  let mut identity = blake3::Hasher::new();
  identity.update(b"ix/plonk-parameter-export/v1");
  identity.update(&anchors.public_setup.id);
  identity.update(&manifest);
  identity.update(&u64::try_from(domain)?.to_le_bytes());
  let path = root.join(identity.finalize().to_hex().as_str()).join("srs.bin");
  let receipt_path = path.with_extension("json");
  if !receipt_path.try_exists()? {
    export_parameters(domain, &path, config)?;
  }
  let receipt: ParameterReceipt = load_json(&receipt_path)?;
  if receipt.format != "ix-bn254-plonk-srs-export-v1"
    || digest(&receipt.setup_id)? != anchors.public_setup.id
    || digest(&receipt.setup_manifest)? != manifest
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
  let manifest = setup_manifest(&setup)?;
  let helper = helper_executable()?;
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("PLONK output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::plonk_export(verifier, packet, trusted_digest, expected, &input)?;
  let vk_path = input.join("vk.json");
  let exported: serde_json::Value = load_json(&vk_path)?;
  let mut identity = blake3::Hasher::new();
  identity.update(b"ix/bn254-plonk-cache/v1");
  identity.update(&fixed_cache::executable_digest()?);
  identity.update(&sha256(&helper)?);
  identity.update(&sha256(&vk_path)?);
  identity.update(&manifest);
  let cache =
    cache_root.join("circuits").join(identity.finalize().to_hex().as_str());
  checked(Command::new(&helper).arg("compile").arg(&vk_path).arg(&cache))?;
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
      .arg(anchor_encoding(&anchors(&setup)?)),
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
  let admission_bytes = setup
    .ignition_admission()
    .ok_or("missing Ignition admission")?
    .to_bytes()?;
  storage::write_atomic(&out.join("admission.json"), &admission_bytes)?;
  let candidate = TrustedCatalog {
    format: CATALOG_FORMAT.into(),
    keys: vec![TrustedKey {
      sha256: key_hash.into(),
      path: "verifying-key.bin".into(),
      inner_vk_id: metadata_string(&exported, "vkId")?.into(),
      statement_prefix: expected[..10].try_into()?,
      circuit_sha256: metadata_string(
        &metadata["Files"]["circuit.bin"],
        "SHA256",
      )?
      .into(),
      helper_sha256: metadata_string(&metadata, "ExecutableSHA256")?.into(),
      setup: SETUP_NAME.into(),
      admission: Some("admission.json".into()),
      admission_blake3: Some(
        blake3::hash(&admission_bytes).to_hex().to_string(),
      ),
    }],
  };
  storage::write_atomic(
    &out.join("verifier-catalog.candidate.json"),
    &serde_json::to_vec_pretty(&candidate)?,
  )?;
  Ok(())
}

#[cfg(test)]
mod bn254_tests {
  use super::*;

  #[test]
  fn catalog_requires_pinned_ignition_anchors_without_a_proving_cache()
  -> Result<()> {
    let scratch = Scratch::new()?;
    let (admission, _) = crate::kzg::srs::ignition::test_admission(7, 8, 41);
    let bytes = admission.to_bytes()?;
    let pin = blake3::hash(&bytes).to_hex().to_string();
    storage::write_atomic(&scratch.0.join("admission.json"), &bytes)?;
    let mut catalog = TrustedCatalog {
      format: CATALOG_FORMAT.into(),
      keys: vec![TrustedKey {
        sha256: hex(&[1; 32]),
        path: "key.bin".into(),
        inner_vk_id: hex(&[2; 32]),
        statement_prefix: [0; 10],
        circuit_sha256: hex(&[3; 32]),
        helper_sha256: hex(&[4; 32]),
        setup: "ignition".into(),
        admission: Some("admission.json".into()),
        admission_blake3: Some(pin),
      }],
    };
    let path = scratch.0.join("catalog.json");
    let write = |catalog: &TrustedCatalog| {
      storage::write_atomic(&path, &serde_json::to_vec(catalog).unwrap())
    };
    write(&catalog)?;
    let key = select_key(&path, &[1; 32])?;
    assert_eq!(
      anchor_encoding(&key_anchors(&key)?),
      anchor_encoding(&admission.anchors())
    );
    assert!(select_key(&path, &[9; 32]).is_err());
    catalog.keys[0].admission_blake3 = Some(hex(&[0; 32]));
    write(&catalog)?;
    assert!(key_anchors(&select_key(&path, &[1; 32])?).is_err());
    catalog.keys[0].admission = None;
    write(&catalog)?;
    assert!(select_key(&path, &[1; 32]).is_err());
    catalog.keys[0].setup = "filecoin".into();
    write(&catalog)?;
    assert!(select_key(&path, &[1; 32]).is_err());
    catalog.format = "ix-bls-plonk-verifiers-v1".into();
    write(&catalog)?;
    assert!(select_key(&path, &[1; 32]).is_err());
    assert_eq!(PROOF_TAG, b"IXBN\0\0\0\x02");
    Ok(())
  }
}
