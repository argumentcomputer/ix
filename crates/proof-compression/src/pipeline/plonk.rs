//! Terminal PLONK worker operations and authenticated parameter interchange.
#[cfg(feature = "plonk")]
use super::fixed_cache;
#[cfg(feature = "plonk")]
use super::gnark;
#[cfg(any(not(feature = "plonk"), test))]
use super::terminal::Scratch;
#[cfg(not(feature = "plonk"))]
use super::terminal::checked;
#[cfg(feature = "plonk")]
use super::terminal::{claim_digest, decode_hex, read_bounded, sha256};
use super::terminal::{digest, hex, load_json};
use super::{Result, setup::SetupClass, statement, storage};
#[cfg(feature = "plonk")]
use super::{setup::SetupConfig, wrap};
use ark_ff::{BigInteger, PrimeField};
#[cfg(feature = "plonk")]
use sha2::{Digest, Sha256};
#[cfg(feature = "plonk")]
use std::io::Write;
#[cfg(not(feature = "plonk"))]
use std::process::Command;
use std::{
  fs,
  path::{Path, PathBuf},
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
  setup: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  admission: Option<PathBuf>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  admission_blake3: Option<String>,
}

#[cfg(feature = "plonk")]
fn setup_manifest(config: &SetupConfig) -> Result<[u8; 32]> {
  match config {
    SetupConfig::Ignition { manifest, .. } => Ok(*manifest),
    _ => Err("PLONK requires authenticated ceremony parameters".into()),
  }
}

#[cfg(feature = "plonk")]
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

fn anchor_encoding(srs: &crate::kzg::Srs) -> Vec<u8> {
  let mut bytes = Vec::new();
  for value in [srs.g1[0].x, srs.g1[0].y] {
    bytes.extend(value.into_bigint().to_bytes_be());
  }
  bytes.extend(encode_g2(srs.g2));
  bytes.extend(encode_g2(srs.tau_g2));
  bytes
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
  let expected = *blake3::hash(claim).as_bytes();
  let anchor_bytes = anchor_encoding(&key_anchors(&key)?);
  #[cfg(feature = "plonk")]
  gnark::verify(
    &read_bounded(&key.path, 1 << 20)?,
    id,
    &packet[32..],
    &expected,
    &anchor_bytes,
  )?;
  #[cfg(not(feature = "plonk"))]
  {
    let scratch = Scratch::new()?;
    let proof = scratch.0.join("proof.bin");
    storage::write_atomic(&proof, &packet[32..])?;
    checked(
      Command::new(super::worker_executable()?)
        .args(["plonk", "verify-key"])
        .arg(&key.path)
        .arg(hex(id))
        .arg(&proof)
        .arg(hex(&expected))
        .arg(hex(&anchor_bytes)),
    )?;
  }
  Ok(SetupClass::Ignition)
}

#[cfg(feature = "plonk")]
pub(crate) fn run(args: &[String]) -> Result<()> {
  let development = args.iter().any(|arg| arg == "--dev-srs");
  let args: Vec<_> = args.iter().filter(|arg| *arg != "--dev-srs").collect();
  match args.iter().map(|s| s.as_str()).collect::<Vec<_>>().as_slice() {
    ["verify-key", key, trusted, proof, claim, anchors] => {
      gnark::verify(&read_bounded(Path::new(key), 1 << 20)?, &digest(trusted)?, &read_bounded(Path::new(proof), MAX_PROOF_BYTES)?, &digest(claim)?, &decode_hex(anchors)?)
    },
    ["verify", proof, claim] => {
      let bytes = read_bounded(Path::new(proof), MAX_PROOF_BYTES + 32 + PROOF_TAG.len())?;
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

#[cfg(feature = "plonk")]
fn export_srs(domain: usize, path: &Path) -> Result<()> {
  export_parameters(domain, path, &SetupConfig::from_env(false)?)
}

#[cfg(feature = "plonk")]
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

#[cfg(feature = "plonk")]
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

#[cfg(feature = "plonk")]
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

#[cfg(feature = "plonk")]
fn metadata_string<'a>(
  value: &'a serde_json::Value,
  field: &str,
) -> Result<&'a str> {
  value
    .get(field)
    .and_then(serde_json::Value::as_str)
    .ok_or_else(|| format!("missing PLONK metadata field {field}").into())
}

#[cfg(feature = "plonk")]
fn artifact(path: &Path) -> Result<gnark::Artifact> {
  Ok(gnark::Artifact {
    sha256: hex(&sha256(path)?),
    bytes: fs::metadata(path)?.len(),
  })
}

#[cfg(feature = "plonk")]
pub(super) fn proving_backend() -> Result<gnark::Backend> {
  match std::env::var("IX_PLONK_BACKEND").as_deref().unwrap_or("cpu") {
    "" | "cpu" => Ok(gnark::Backend::Cpu),
    "cuda" => {
      let device: i32 = std::env::var("IX_PLONK_CUDA_DEVICE")
        .unwrap_or_else(|_| "0".into())
        .parse()?;
      if device < 0 {
        return Err("IX_PLONK_CUDA_DEVICE must be nonnegative".into());
      }
      let gib: u64 = std::env::var("IX_PLONK_CUDA_MEMORY_GIB")
        .unwrap_or_else(|_| "64".into())
        .parse()?;
      let memory_bytes = gib
        .checked_mul(1 << 30)
        .filter(|n| *n > 0)
        .ok_or("invalid PLONK CUDA memory budget")?;
      let mask_msm = match std::env::var("IX_PLONK_CUDA_MSM_STRATEGY")
        .as_deref()
        .unwrap_or("split")
      {
        "" | "split" => false,
        "mask" => true,
        _ => {
          return Err(
            "IX_PLONK_CUDA_MSM_STRATEGY must be split or mask".into(),
          );
        },
      };
      Ok(gnark::Backend::Cuda { device, memory_bytes, mask_msm })
    },
    _ => Err("IX_PLONK_BACKEND must be cpu or cuda".into()),
  }
}

#[cfg(feature = "plonk")]
fn prepare_artifacts(
  vk: &Path,
  setup: &SetupConfig,
  cache_root: &Path,
) -> Result<(PathBuf, gnark::Manifest)> {
  let schema = fs::read(vk)?;
  let schema_hash = hex(&Sha256::digest(&schema));
  let mut identity = blake3::Hasher::new();
  identity.update(&fixed_cache::executable_digest()?);
  identity.update(schema_hash.as_bytes());
  identity.update(&setup_manifest(setup)?);
  let dir =
    cache_root.join("circuits").join(identity.finalize().to_hex().as_str());
  fs::create_dir_all(&dir)?;
  let metadata_path = dir.join("manifest.json");
  let mut metadata: gnark::Manifest = if metadata_path.is_file() {
    let metadata: gnark::Manifest = load_json(&metadata_path)?;
    // Go authenticates the large native artifacts while decoding them.
    if metadata.inner_vk_sha256 != schema_hash
      || metadata.files.get("vk.json") != Some(&artifact(&dir.join("vk.json"))?)
    {
      return Err("PLONK circuit cache identity differs".into());
    }
    metadata
  } else {
    storage::write_atomic(&dir.join("vk.json"), &schema)?;
    let info = gnark::compile(&schema, &dir.join("circuit.bin"))?;
    let metadata = gnark::Manifest {
      inner_vk_sha256: schema_hash,
      srs_blake3: String::new(),
      keys_ready: false,
      domain: info.domain,
      constraints: info.constraints,
      public_inputs: info.public_inputs,
      commitments: info.commitments,
      files: std::collections::BTreeMap::from([
        ("vk.json".into(), artifact(&dir.join("vk.json"))?),
        ("circuit.bin".into(), artifact(&dir.join("circuit.bin"))?),
      ]),
    };
    storage::write_atomic(
      &metadata_path,
      &serde_json::to_vec_pretty(&metadata)?,
    )?;
    metadata
  };
  let domain = usize::try_from(metadata.domain)?;
  if !(2..=1 << 26).contains(&domain)
    || !domain.is_power_of_two()
    || metadata.public_inputs != 2
  {
    return Err("invalid PLONK circuit dimensions".into());
  }
  if !metadata.keys_ready {
    let (srs, receipt) =
      cached_parameters(domain, &cache_root.join("parameters"), setup)?;
    let mut identity = Sha256::new();
    identity.update(setup_manifest(setup)?);
    identity.update(domain.to_le_bytes());
    identity.update(receipt.as_bytes());
    let lagrange_root =
      cache_root.join("lagrange").join(hex(&identity.finalize()));
    fs::create_dir_all(&lagrange_root)?;
    let lagrange = lagrange_root.join("points.bin");
    let lagrange_metadata = lagrange_root.join("manifest.json");
    let cached_lagrange = lagrange_metadata.is_file();
    let lagrange_hash = if cached_lagrange {
      let saved: gnark::Artifact = load_json(&lagrange_metadata)?;
      if saved.bytes != 64 * metadata.domain {
        return Err("Lagrange cache identity differs".into());
      }
      digest(&saved.sha256)?;
      saved.sha256
    } else {
      String::new()
    };
    gnark::prepare(&gnark::Preparation {
      schema: &schema,
      circuit: &dir.join("circuit.bin"),
      circuit_hash: metadata
        .files
        .get("circuit.bin")
        .ok_or("missing circuit hash")?,
      domain: metadata.domain,
      srs: &srs,
      srs_digest: &receipt,
      lagrange: &lagrange,
      lagrange_digest: &lagrange_hash,
      output: &dir,
    })?;
    if !cached_lagrange {
      storage::write_atomic(
        &lagrange_metadata,
        &serde_json::to_vec(&artifact(&lagrange)?)?,
      )?;
    }
    for name in ["proving-key.bin", "verifying-key.bin", "PlonkVerifier.sol"] {
      metadata.files.insert(name.into(), artifact(&dir.join(name))?);
    }
    metadata.srs_blake3 = receipt;
    metadata.keys_ready = true;
    storage::write_atomic(
      &metadata_path,
      &serde_json::to_vec_pretty(&metadata)?,
    )?;
  }
  if metadata.files.get("PlonkVerifier.sol")
    != Some(&artifact(&dir.join("PlonkVerifier.sol"))?)
  {
    return Err("Solidity verifier cache identity differs".into());
  }
  Ok((dir, metadata))
}

#[cfg(feature = "plonk")]
fn wrap_packet(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &statement::Statement,
  cache_root: &Path,
  out: &Path,
) -> Result<()> {
  use std::time::Instant;
  statement::from_claims_bytes(&statement::to_claims_bytes(expected))?;
  let expected_digest = claim_digest(expected)?;
  let setup = SetupConfig::from_env(false)?;
  setup_manifest(&setup)?;
  let backend = proving_backend()?;
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("PLONK output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::plonk_export(verifier, packet, trusted_digest, expected, &input)?;
  let vk_path = input.join("vk.json");
  let exported: serde_json::Value = load_json(&vk_path)?;
  let (cache, metadata) = prepare_artifacts(&vk_path, &setup, cache_root)?;
  let started = Instant::now();
  let mut prover = gnark::Prover::open(&cache, &metadata, backend)?;
  let load_seconds = started.elapsed().as_secs_f64();
  let witness = fs::read(input.join("witness.json"))?;
  let started = Instant::now();
  let proof = prover.prove(&witness, &expected_digest)?;
  let prove_seconds = started.elapsed().as_secs_f64();
  prover.close()?;
  let key = cache.join("verifying-key.bin");
  let key_hash = &metadata
    .files
    .get("verifying-key.bin")
    .ok_or("missing verifying key hash")?
    .sha256;
  let key_id = digest(key_hash)?;
  gnark::verify(
    &fs::read(&key)?,
    &key_id,
    &proof.native,
    &expected_digest,
    &anchor_encoding(&anchors(&setup)?),
  )?;
  if proof.native.is_empty() || proof.native.len() > MAX_PROOF_BYTES {
    return Err("invalid native PLONK proof length".into());
  }
  let mut envelope = PROOF_TAG.to_vec();
  envelope.extend(key_id);
  envelope.extend(&proof.native);
  storage::write_atomic(&out.join("proof.bin"), &proof.native)?;
  storage::write_atomic(&out.join("proof.solidity.bin"), &proof.solidity)?;
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
      sha256: key_hash.clone(),
      path: "verifying-key.bin".into(),
      inner_vk_id: metadata_string(&exported, "vkId")?.into(),
      statement_prefix: expected[..10].try_into()?,
      circuit_sha256: metadata
        .files
        .get("circuit.bin")
        .ok_or("missing circuit hash")?
        .sha256
        .clone(),
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
  storage::write_atomic(
    &out.join("report.json"),
    &serde_json::to_vec_pretty(
      &serde_json::json!({"backend":match backend { gnark::Backend::Cpu => "cpu", gnark::Backend::Cuda { .. } => "cuda" },"loadSeconds":load_seconds,"proveSeconds":prove_seconds,"verifyingKeySHA256":key_hash,"solidityBytes":proof.solidity.len()}),
    )?,
  )?;
  storage::write_atomic(&out.join("proof.envelope.bin"), &envelope)?;
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
