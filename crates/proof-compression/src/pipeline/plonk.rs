//! Terminal PLONK proofs under the release key, and authenticated parameter
//! interchange.
#[cfg(any(feature = "plonk", feature = "groth16"))]
use super::statement;
#[cfg(feature = "plonk")]
use super::storage;
#[cfg(feature = "plonk")]
use super::terminal::{claim_digest, sha256};
#[cfg(feature = "plonk")]
use super::terminal::{digest, hex, load_json};
use super::{Result, setup::SetupClass};
#[cfg(feature = "plonk")]
use super::{gnark, verifying_keys};
#[cfg(any(feature = "plonk", feature = "groth16"))]
use super::{setup::SetupConfig, wrap};
#[cfg(feature = "plonk")]
use ark_ff::{BigInteger, PrimeField};
#[cfg(feature = "plonk")]
use sha2::{Digest, Sha256};
#[cfg(feature = "plonk")]
use std::fs;
#[cfg(feature = "plonk")]
use std::io::Write;
#[cfg(any(feature = "plonk", feature = "groth16"))]
use std::path::Path;
#[cfg(feature = "plonk")]
use std::path::PathBuf;

pub(super) const PROOF_TAG: &[u8; 8] = b"IXBN\0\0\0\x02";
const MAX_PROOF_BYTES: usize = 1 << 20;

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

#[cfg(feature = "plonk")]
fn encode_g2(point: crate::kzg::curve::G2Affine) -> Vec<u8> {
  let mut bytes = Vec::new();
  for value in [point.x.c0, point.x.c1, point.y.c0, point.y.c1] {
    bytes.extend(value.into_bigint().to_bytes_be());
  }
  bytes
}

#[cfg(feature = "plonk")]
fn anchor_encoding(srs: &crate::kzg::Srs) -> Vec<u8> {
  let mut bytes = Vec::new();
  for value in [srs.g1[0].x, srs.g1[0].y] {
    bytes.extend(value.into_bigint().to_bytes_be());
  }
  bytes.extend(encode_g2(srs.g2));
  bytes.extend(encode_g2(srs.tau_g2));
  bytes
}

#[cfg(not(feature = "plonk"))]
pub(super) fn verify(packet: &[u8], _claim: &[u8]) -> Result<SetupClass> {
  if packet.len() <= 32 || packet.len() > MAX_PROOF_BYTES + 32 {
    return Err("invalid PLONK packet length".into());
  }
  Err("PLONK proofs are verified by gnark, and this ix was built without PLONK; rebuild with IX_PLONK=1".into())
}

/// Verify a PLONK packet of `claim` under the release's PLONK key.
#[cfg(feature = "plonk")]
pub(super) fn verify(packet: &[u8], claim: &[u8]) -> Result<SetupClass> {
  if packet.len() <= 32 || packet.len() > MAX_PROOF_BYTES + 32 {
    return Err("invalid PLONK packet length".into());
  }
  let id: [u8; 32] = packet[..32].try_into()?;
  if id != digest(verifying_keys::PLONK_VK_SHA256)? {
    return Err(
      "PLONK proof uses a verifying key other than the release key".into(),
    );
  }
  if Sha256::digest(verifying_keys::PLONK_VK).as_slice() != id {
    return Err("bundled PLONK verifying key differs from its pin".into());
  }
  let anchors = anchor_encoding(&verifying_keys::admission()?.anchors());
  gnark::verify(
    verifying_keys::PLONK_VK,
    &id,
    &packet[32..],
    blake3::hash(claim).as_bytes(),
    &anchors,
  )?;
  Ok(SetupClass::Ignition)
}

/// Write the gnark verifier description (`vk.json`) and witness
/// (`witness.json`) for the recursive KZG packet in `packet` to `out`. The
/// verifying key in `verifier` must have BLAKE3 digest `trusted_digest` and
/// be admitted by `setup`'s Ignition parameters.
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub fn export(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &[u64; statement::WORDS],
  out: &Path,
  setup: &SetupConfig,
) -> Result<()> {
  wrap::plonk_export(verifier, packet, trusted_digest, expected, out, setup)
}

/// Write the first `domain + 3` Ignition powers a PLONK circuit of `domain`
/// rows needs to `path`, with a JSON receipt beside it.
#[cfg(feature = "plonk")]
pub fn export_parameters(
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
  schema: &[u8],
  setup: &SetupConfig,
  cache_root: &Path,
) -> Result<(PathBuf, gnark::Manifest)> {
  let schema_hash = hex(&Sha256::digest(schema));
  // `go.sum` pins the gnark that compiles the circuit and serializes its keys.
  let mut identity = blake3::Hasher::new();
  identity.update(b"ix/plonk-circuit-cache/v2");
  identity.update(include_bytes!("../../../../tools/plonk-wrapper/go.sum"));
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
    storage::write_atomic(&dir.join("vk.json"), schema)?;
    let info = gnark::compile(schema, &dir.join("circuit.bin"))?;
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
      schema,
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

/// Derive the PLONK verifying key for the recursive verifying key
/// `recursive_vk` and statement prefix `prefix` without a proof: compile the
/// verifier description `wrap_packet` proves and set its keys up under
/// `setup`'s Ignition parameters, caching them under `cache_root` as
/// `wrap_packet` does.
#[cfg(feature = "plonk")]
pub fn derive_verifying_key(
  recursive_vk: &[u8],
  prefix: &[u64; 10],
  setup: &SetupConfig,
  cache_root: &Path,
) -> Result<Vec<u8>> {
  let vk = wrap::VerifyingKey::from_bytes(recursive_vk)?;
  vk.check_ignition_admission(
    setup
      .ignition_admission()
      .ok_or("PLONK requires admitted Ignition parameters")?,
  )?;
  let schema = wrap::plonk_description(&vk, prefix)?;
  let (dir, metadata) = prepare_artifacts(&schema, setup, cache_root)?;
  let key = fs::read(dir.join("verifying-key.bin"))?;
  let recorded = &metadata
    .files
    .get("verifying-key.bin")
    .ok_or("missing verifying key hash")?
    .sha256;
  if hex(&Sha256::digest(&key)) != *recorded {
    return Err("cached PLONK verifying key differs from its manifest".into());
  }
  Ok(key)
}

/// Prove the recursive KZG packet in `packet` in PLONK and write its
/// envelope, native and Solidity proofs and verifying key to the empty
/// directory `out`. Compiled circuits, keys and parameter
/// exports are cached under `cache_root`.
#[cfg(feature = "plonk")]
pub(super) fn wrap_packet(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &statement::Statement,
  cache_root: &Path,
  out: &Path,
  setup: &SetupConfig,
) -> Result<()> {
  use std::time::Instant;
  statement::from_claims_bytes(&statement::to_claims_bytes(expected))?;
  let expected_digest = claim_digest(expected)?;
  setup_manifest(setup)?;
  let backend = proving_backend()?;
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err("PLONK output directory must be empty".into());
  }
  let input = out.join("input");
  wrap::plonk_export(
    verifier,
    packet,
    trusted_digest,
    expected,
    &input,
    setup,
  )?;
  let (cache, metadata) =
    prepare_artifacts(&fs::read(input.join("vk.json"))?, setup, cache_root)?;
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
    &anchor_encoding(&anchors(setup)?),
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
  fn plonk_packets_are_tagged_and_bounded() {
    assert_eq!(PROOF_TAG, b"IXBN\0\0\0\x02");
    assert!(verify(&[0; 32], b"claim").is_err());
  }

  #[test]
  #[cfg(feature = "plonk")]
  fn other_keys_are_rejected() {
    let error = verify(&[1; 64], b"claim").unwrap_err();
    assert!(error.to_string().contains("other than the release key"));
  }
}
