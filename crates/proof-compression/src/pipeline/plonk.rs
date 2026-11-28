//! Legacy pipeline PLONK proof tags, packet bounds, and pure-Rust parameter
//! export interchange for BN254 and BLS12-381.
//!
//! Go/gnark proving and verification in this legacy pipeline module have been
//! retired and removed; use the pure-Rust native PLONK backend in
//! `crate::aiur_backend::plonk::native`.

#[cfg(all(test, feature = "plonk"))]
use super::final_proof::{digest, load_json};
use super::setup::SetupConfig;
use super::statement;
#[cfg(feature = "plonk")]
use super::storage;
#[cfg(feature = "plonk")]
use super::verifying_keys;
#[cfg(any(feature = "plonk", feature = "groth16"))]
use super::wrap;
use super::{Result, setup::SetupClass};
#[cfg(feature = "plonk")]
use crate::kzg::curve::Curve;
use crate::kzg::curve::{Bls12381, Bn254, KzgCurve};
#[cfg(feature = "plonk")]
use ark_ff::{BigInteger, PrimeField};
#[cfg(feature = "plonk")]
use std::fs;
#[cfg(feature = "plonk")]
use std::io::{Read, Write};
use std::path::Path;
#[cfg(all(test, feature = "plonk"))]
use std::path::PathBuf;

pub(super) const PROOF_TAG: &[u8; 8] = Bn254::PLONK_PROOF_TAG;
pub(super) const BLS12_381_PROOF_TAG: &[u8; 8] = Bls12381::PLONK_PROOF_TAG;
const MAX_PROOF_BYTES: usize = 1 << 20;

const RETIRED_ERROR: &str = "legacy Go/gnark pipeline PLONK has been retired \
  and removed; use the pure-Rust native PLONK backend in \
  aiur_backend::plonk::native";

pub(super) fn retired_error() -> Box<dyn std::error::Error> {
  RETIRED_ERROR.into()
}

#[cfg(feature = "plonk")]
const fn final_srs_seed(curve: Curve) -> &'static [u8] {
  match curve {
    Curve::Bn254 => b"ix/bn254-plonk/srs/v1",
    Curve::Bls12381 => b"ix/bls-plonk/srs/v1",
  }
}

#[cfg(feature = "plonk")]
fn setup_identity<C: KzgCurve>(config: &SetupConfig) -> [u8; 32] {
  match config {
    SetupConfig::Ignition { .. } => {
      verifying_keys::ignition_parameters()
        .expect("bundled Ignition parameters")
        .public_setup
        .id
    },
    SetupConfig::Filecoin { .. } => {
      crate::kzg::srs::filecoin::filecoin_setup_id()
    },
    SetupConfig::Development { .. } => {
      *blake3::hash(final_srs_seed(C::CURVE)).as_bytes()
    },
  }
}

#[cfg(all(test, feature = "plonk"))]
fn anchors<C: KzgCurve>(
  config: &SetupConfig,
  domain: usize,
) -> Result<crate::kzg::Srs<C>> {
  let size = parameter_size(config, domain)?;
  let height = match config {
    SetupConfig::Ignition { .. } => domain,
    SetupConfig::Filecoin { .. } | SetupConfig::Development { .. } => {
      size.loaded_powers().next_power_of_two()
    },
  };
  config.for_stage::<C>(final_srs_seed(C::CURVE), height)?.srs(2, true)
}

#[cfg(feature = "plonk")]
fn parameter_size(
  config: &SetupConfig,
  domain: usize,
) -> Result<super::plonk_limits::ParameterSize> {
  let size = super::plonk_limits::ParameterSize::for_domain(domain)?;
  if matches!(config, SetupConfig::Ignition { .. }) {
    size.check_public_degree(
      verifying_keys::ignition_parameters()?.public_setup.max_degree,
    )?;
  }
  Ok(size)
}

#[cfg(all(test, feature = "plonk"))]
fn anchor_encoding<C: KzgCurve>(srs: &crate::kzg::Srs<C>) -> Vec<u8> {
  C::encode_plonk_anchors(&srs.g1[0], &srs.g2, &srs.tau_g2)
}

pub(super) fn verify(packet: &[u8], _claim: &[u8]) -> Result<SetupClass> {
  if packet.len() <= 32 || packet.len() > MAX_PROOF_BYTES + 32 {
    return Err("invalid PLONK packet length".into());
  }
  Err(retired_error())
}

pub(super) fn verify_bls12_381(
  packet: &[u8],
  _claim: &[u8],
) -> Result<SetupClass> {
  if packet.len() <= 32 || packet.len() > MAX_PROOF_BYTES + 32 {
    return Err("invalid PLONK packet length".into());
  }
  Err(retired_error())
}

#[allow(clippy::extra_unused_type_parameters)]
pub(super) fn check_stage_for<C: KzgCurve>(
  _dir: &Path,
  _expected: &statement::Statement,
  _setup: &SetupConfig,
  _bundled: bool,
  _verifier: &Path,
  _development: bool,
  _cache_root: &Path,
) -> Result<()> {
  Err(retired_error())
}

/// Write the verifier description (`vk.json`) and witness (`witness.json`)
/// for the recursive KZG packet in `packet` to `out`. The verifying key in
/// `verifier` must have BLAKE3 digest `trusted_digest` and match the released
/// parameters or explicitly selected development setup.
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub fn export(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &[u64; statement::WORDS],
  out: &Path,
  setup: &SetupConfig,
) -> Result<()> {
  export_for::<Bn254>(verifier, packet, trusted_digest, expected, out, setup)
}

#[cfg(any(feature = "plonk", feature = "groth16"))]
pub fn export_for<C: KzgCurve>(
  verifier: &Path,
  packet: &Path,
  trusted_digest: &str,
  expected: &[u64; statement::WORDS],
  out: &Path,
  setup: &SetupConfig,
) -> Result<()> {
  wrap::final_export::<C>(
    verifier,
    packet,
    trusted_digest,
    expected,
    out,
    setup,
  )
}

/// Write the first `domain + 3` powers of the selected final PLONK setup,
/// independently of the inner verifier's parameters, with a pinned receipt.
#[cfg(feature = "plonk")]
pub fn export_parameters(
  domain: usize,
  path: &Path,
  config: &SetupConfig,
) -> Result<()> {
  export_parameters_for::<Bn254>(domain, path, config)
}

#[cfg(feature = "plonk")]
fn export_bn254_ignition_parameters(
  size: super::plonk_limits::ParameterSize,
  path: &Path,
  srs_path: &Path,
  config: &SetupConfig,
) -> Result<()> {
  let mut count_bytes = [0; 4];
  fs::File::open(srs_path)?.read_exact(&mut count_bytes)?;
  let parameters = verifying_keys::ignition_parameters()?;
  size.check_capacity(
    u32::from_be_bytes(count_bytes) as usize,
    parameters.public_setup.max_degree,
  )?;
  let count = size.opening_powers();
  let manifest = setup_identity::<Bn254>(config);
  let powers = crate::kzg::srs::gnark::load_exact(
    srs_path,
    count,
    parameters.public_setup,
  )?;
  if powers.g1[..2] != parameters.g1
    || powers.g2 != parameters.g2
    || powers.tau_g2 != parameters.tau_g2
  {
    return Err(
      "PLONK powers differ from the released Ignition anchors".into(),
    );
  }
  let public_setup = parameters.public_setup;
  let temporary = storage::temporary_path(path);
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent)?;
  }
  let mut out = std::io::BufWriter::new(fs::File::create(&temporary)?);
  out.write_all(Bn254::PLONK_SRS_MAGIC)?;
  out.write_all(&public_setup.id)?;
  out.write_all(&(public_setup.max_degree as u64).to_le_bytes())?;
  out.write_all(&manifest)?;
  out.write_all(&(count as u64).to_le_bytes())?;
  out.write_all(&Bn254::encode_g2_vk(&powers.g2))?;
  out.write_all(&Bn254::encode_g2_vk(&powers.tau_g2))?;
  for point in &powers.g1[..count] {
    out.write_all(&point.x.into_bigint().to_bytes_be())?;
    out.write_all(&point.y.into_bigint().to_bytes_be())?;
  }
  out.flush()?;
  drop(out);
  storage::persist(&temporary, path)?;
  let digest = blake3::Hash::from_bytes(storage::blake3_file(path)?);
  let receipt = serde_json::json!({
    "format": Bn254::PLONK_SRS_FORMAT, "blake3": digest.to_hex().as_str(),
    "setupId": blake3::Hash::from_bytes(public_setup.id).to_hex().as_str(),
    "publicMaxDegree": public_setup.max_degree, "powers": count,
    "setupClass": config.class().label(),
    "setupIdentity": blake3::Hash::from_bytes(manifest).to_hex().as_str(),
  });
  storage::write_atomic(
    &path.with_extension("json"),
    &serde_json::to_vec_pretty(&receipt)?,
  )?;
  Ok(())
}

#[cfg(feature = "plonk")]
pub fn export_parameters_for<C: KzgCurve>(
  domain: usize,
  path: &Path,
  config: &SetupConfig,
) -> Result<()> {
  let size = parameter_size(config, domain)?;
  if let SetupConfig::Ignition { srs } = config {
    if C::CURVE != Curve::Bn254 {
      return Err("Ignition setup is only valid for BN254 PLONK".into());
    }
    return export_bn254_ignition_parameters(size, path, srs, config);
  }
  let count = size.opening_powers();
  let prefix = size.loaded_powers().next_power_of_two();
  let manifest = setup_identity::<C>(config);
  let source = config.for_stage::<C>(final_srs_seed(C::CURVE), prefix)?;
  let srs = source.srs(prefix, false)?;
  let temporary = storage::temporary_path(path);
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent)?;
  }
  let mut out = std::io::BufWriter::new(fs::File::create(&temporary)?);
  out.write_all(C::PLONK_SRS_MAGIC)?;
  out.write_all(&srs.public_setup.id)?;
  out.write_all(&(srs.public_setup.max_degree as u64).to_le_bytes())?;
  out.write_all(&manifest)?;
  out.write_all(&(count as u64).to_le_bytes())?;
  out.write_all(&C::encode_g2_vk(&srs.g2))?;
  out.write_all(&C::encode_g2_vk(&srs.tau_g2))?;
  for point in &srs.g1[..count] {
    out.write_all(&point.x.into_bigint().to_bytes_be())?;
    out.write_all(&point.y.into_bigint().to_bytes_be())?;
  }
  out.flush()?;
  drop(out);
  storage::persist(&temporary, path)?;
  let digest = blake3::Hash::from_bytes(storage::blake3_file(path)?);
  let receipt = serde_json::json!({
    "format": C::PLONK_SRS_FORMAT, "blake3": digest.to_hex().as_str(),
    "setupId": blake3::Hash::from_bytes(srs.public_setup.id).to_hex().as_str(),
    "publicMaxDegree": srs.public_setup.max_degree, "powers": count,
    "setupClass": config.class().label(),
    "setupIdentity": blake3::Hash::from_bytes(manifest).to_hex().as_str(),
  });
  storage::write_atomic(
    &path.with_extension("json"),
    &serde_json::to_vec_pretty(&receipt)?,
  )?;
  Ok(())
}

/// Retired legacy Go/gnark PLONK verifying key derivation; use
/// `aiur_backend::plonk::native`.
#[cfg(feature = "plonk")]
pub fn derive_verifying_key(
  _recursive_vk: &[u8],
  _prefix: &[u64; 10],
  _setup: &SetupConfig,
  _cache_root: &Path,
) -> Result<Vec<u8>> {
  Err(retired_error())
}

/// Retired legacy Go/gnark PLONK verifying key derivation; use
/// `aiur_backend::plonk::native`.
#[cfg(feature = "plonk")]
#[allow(clippy::extra_unused_type_parameters)]
pub fn derive_verifying_key_for<C: KzgCurve>(
  _recursive_vk: &[u8],
  _prefix: &[u64; 10],
  _setup: &SetupConfig,
  _cache_root: &Path,
) -> Result<Vec<u8>> {
  Err(retired_error())
}

#[cfg(all(test, feature = "plonk"))]
#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ParameterReceipt {
  format: String,
  blake3: String,
  setup_id: String,
  public_max_degree: usize,
  powers: usize,
  setup_class: String,
  setup_identity: String,
}

#[cfg(all(test, feature = "plonk"))]
fn cached_parameters_for<C: KzgCurve>(
  domain: usize,
  root: &Path,
  config: &SetupConfig,
) -> Result<(PathBuf, String)> {
  let manifest = setup_identity::<C>(config);
  let anchors = anchors::<C>(config, domain)?;
  let mut identity = blake3::Hasher::new();
  identity.update(b"ix/plonk-parameter-export/v2");
  if C::CURVE != Curve::Bn254 {
    identity.update(C::NAME.as_bytes());
  }
  identity.update(config.class().label().as_bytes());
  identity.update(&anchors.public_setup.id);
  identity.update(&manifest);
  identity.update(&u64::try_from(domain)?.to_le_bytes());
  let path = root.join(identity.finalize().to_hex().as_str()).join("srs.bin");
  let receipt_path = path.with_extension("json");
  if !receipt_path.try_exists()? {
    export_parameters_for::<C>(domain, &path, config)?;
  }
  let receipt: ParameterReceipt = load_json(&receipt_path)?;
  if receipt.format != C::PLONK_SRS_FORMAT
    || receipt.setup_class != config.class().label()
    || digest(&receipt.setup_id)? != anchors.public_setup.id
    || digest(&receipt.setup_identity)? != manifest
    || receipt.public_max_degree != anchors.public_setup.max_degree
    || receipt.powers
      != domain.checked_add(3).ok_or("PLONK SRS length overflow")?
  {
    return Err("cached PLONK parameter identity differs".into());
  }
  let mut header = [0u8; 88];
  fs::File::open(&path)?.read_exact(&mut header)?;
  if &header[..8] != C::PLONK_SRS_MAGIC
    || header[8..40] != anchors.public_setup.id
    || u64::from_le_bytes(header[40..48].try_into()?)
      != u64::try_from(receipt.public_max_degree)?
    || header[48..80] != manifest
    || u64::from_le_bytes(header[80..88].try_into()?)
      != u64::try_from(receipt.powers)?
  {
    return Err("PLONK parameter header differs from its pinned setup".into());
  }
  if storage::blake3_file(&path)? != digest(&receipt.blake3)? {
    return Err("cached PLONK parameter export is damaged".into());
  }
  Ok((path, receipt.blake3))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  #[cfg(feature = "plonk")]
  fn ignition_capacity_is_rejected_before_opening_the_srs() {
    let setup = SetupConfig::Ignition { srs: "/does-not-exist".into() };
    let error = export_parameters(
      crate::pipeline::plonk_limits::MAX_DOMAIN * 2,
      Path::new("/does-not-exist/output.bin"),
      &setup,
    )
    .unwrap_err();
    assert!(
      error.to_string().contains("PLONK domain must be a power of two"),
      "unexpected error: {error}"
    );
    let degree_error =
      crate::pipeline::plonk_limits::ParameterSize::for_domain(1 << 26)
        .unwrap()
        .check_public_degree((1 << 26) - 1)
        .unwrap_err();
    assert!(
      degree_error.contains("67108867-power prefix"),
      "unexpected error: {degree_error}"
    );
    assert!(
      degree_error.contains("admitted maximum degree"),
      "unexpected error: {degree_error}"
    );
  }

  #[test]
  #[cfg(feature = "plonk")]
  fn short_ignition_prefix_is_rejected_before_loading_points() -> Result<()> {
    let temporary = crate::test_support::TempDir::new("plonk-short-prefix");
    let srs = temporary.join("srs.bin");
    fs::write(&srs, 16u32.to_be_bytes())?;
    let setup = SetupConfig::Ignition { srs };
    let out = temporary.join("export.bin");
    let error = export_parameters(16, &out, &setup).unwrap_err();
    assert!(error.to_string().contains("SRS retains 16 powers"));
    assert!(!out.exists());
    Ok(())
  }

  #[test]
  #[cfg(feature = "plonk")]
  fn development_parameters_need_no_ignition_and_bind_the_cache() -> Result<()>
  {
    let temporary = crate::test_support::TempDir::new("plonk-parameters");
    let setup = SetupConfig::Development { cache_directory: None };
    let root = temporary.join("parameters");
    let (path, checksum) = cached_parameters_for::<Bn254>(8, &root, &setup)?;
    let (again, same_checksum) =
      cached_parameters_for::<Bn254>(8, &root, &setup)?;
    assert_eq!((path.clone(), checksum), (again, same_checksum));
    let receipt: ParameterReceipt = load_json(&path.with_extension("json"))?;
    assert_eq!(receipt.setup_class, "development");
    assert_eq!(receipt.powers, 11);
    assert_eq!(
      digest(&receipt.setup_id)?,
      anchors::<Bn254>(&setup, 8)?.public_setup.id
    );
    let mut corrupted = fs::read(&path)?;
    corrupted[8] ^= 1;
    fs::write(&path, corrupted)?;
    assert!(cached_parameters_for::<Bn254>(8, &root, &setup).is_err());
    Ok(())
  }

  #[test]
  #[cfg(feature = "plonk")]
  fn bls12_381_development_parameters_export_and_cache() -> Result<()> {
    let temporary =
      crate::test_support::TempDir::new("bls12-381-plonk-parameters");
    let setup = SetupConfig::Development { cache_directory: None };
    let root = temporary.join("parameters");
    let (path, checksum) = cached_parameters_for::<Bls12381>(8, &root, &setup)?;
    let (again, same_checksum) =
      cached_parameters_for::<Bls12381>(8, &root, &setup)?;
    assert_eq!((path.clone(), checksum), (again, same_checksum));
    let receipt: ParameterReceipt = load_json(&path.with_extension("json"))?;
    assert_eq!(receipt.format, Bls12381::PLONK_SRS_FORMAT);
    assert_eq!(receipt.setup_class, "development");
    assert_eq!(receipt.powers, 11);
    let bytes = fs::read(&path)?;
    assert_eq!(&bytes[..8], Bls12381::PLONK_SRS_MAGIC);
    // 88 header + 2 * 96 G2 + 11 * 96 G1
    assert_eq!(bytes.len(), 88 + 2 * 96 + 11 * 96);
    assert_eq!(anchor_encoding(&anchors::<Bls12381>(&setup, 8)?).len(), 240);
    Ok(())
  }

  #[test]
  fn plonk_packets_are_tagged_and_bounded() {
    assert_eq!(PROOF_TAG, b"IXBN\0\0\0\x02");
    assert_eq!(BLS12_381_PROOF_TAG, b"IXCMP\0\0\x05");
    assert!(
      verify(&[0; 32], b"claim")
        .unwrap_err()
        .to_string()
        .contains("packet length")
    );
    assert!(
      verify_bls12_381(&[0; 32], b"claim")
        .unwrap_err()
        .to_string()
        .contains("packet length")
    );
    let err = verify(&[1; 64], b"claim").unwrap_err().to_string();
    assert!(
      err.contains("retired") && err.contains("aiur_backend::plonk::native"),
      "{err}"
    );
    let err = verify_bls12_381(&[1; 64], b"claim").unwrap_err().to_string();
    assert!(
      err.contains("retired") && err.contains("aiur_backend::plonk::native"),
      "{err}"
    );
  }
}
