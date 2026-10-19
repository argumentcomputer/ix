//! Portable, explicitly pinned authorization for one Ignition setup.

use std::{
  fs::{self, File},
  io::{self, Read},
  path::Path,
};

use serde::{Deserialize, Serialize};

use super::{
  IgnitionCacheIdentity, SHIFTED_TAU_BASIS, cache, invalid,
  load_ignition_cache_with_identity,
  points::{decode_g1, decode_g2, encode_g1, encode_g2},
  source::{parse_source_manifest, read_source_manifest_bytes},
};
use crate::kzg::{
  PublicSetup, Srs, VerifierParams,
  curve::{self, G1Affine, G2Affine},
};

const FORMAT: &str = "ix-bn254-ignition-admission-v1";
const MAX_ADMISSION_BYTES: u64 = 4 << 20;

/// The pin is an explicit trust decision over setup identity and anchors.
/// Its embedded source manifest binds the identity to a specific ceremony
/// descriptor; neither the admission nor its parser authenticates participants.
#[derive(Clone, Debug)]
pub struct IgnitionAdmission {
  source_manifest_json: String,
  source_manifest_digest: [u8; 32],
  public_setup: PublicSetup,
  g1: [G1Affine; 2],
  g2: G2Affine,
  tau_g2: G2Affine,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct AdmissionEncoding {
  format: String,
  curve: String,
  basis: String,
  source_manifest_json: String,
  source_manifest_blake3: String,
  setup_id: String,
  public_max_degree: u64,
  g1: [String; 2],
  g2: String,
  tau_g2: String,
}

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex<const N: usize>(text: &str) -> io::Result<[u8; N]> {
  if text.len() != 2 * N || !text.as_bytes().iter().all(u8::is_ascii_hexdigit) {
    return Err(invalid("invalid Ignition admission hexadecimal field"));
  }
  let mut bytes = [0; N];
  for (index, byte) in bytes.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&text[2 * index..2 * index + 2], 16)
      .map_err(invalid)?;
  }
  Ok(bytes)
}

impl IgnitionAdmission {
  /// Authorize anchors from an authenticated import against an independently
  /// pinned source descriptor. Only the cache's small manifest is loaded.
  pub fn from_cache(
    cache: &Path,
    trusted_cache: [u8; 32],
    source_manifest: &Path,
    trusted_source: [u8; 32],
  ) -> io::Result<Self> {
    let (source_bytes, manifest) =
      read_source_manifest_bytes(source_manifest, trusted_source)?;
    let (srs, identity) =
      load_ignition_cache_with_identity(cache, trusted_cache, 2)?;
    if identity.source_manifest_digest != trusted_source
      || identity.public_setup != manifest.public_setup()?
    {
      return Err(invalid(
        "Ignition admission cache does not match its pinned source manifest",
      ));
    }
    let admission = Self {
      source_manifest_json: String::from_utf8(source_bytes).map_err(invalid)?,
      source_manifest_digest: trusted_source,
      public_setup: srs.public_setup,
      g1: [srs.g1[0], srs.g1[1]],
      g2: srs.g2,
      tau_g2: srs.tau_g2,
    };
    admission.check_cache(&srs, &identity)?;
    Ok(admission)
  }

  /// Canonical JSON for a new admission pin. The original source JSON bytes
  /// remain unchanged inside its string field.
  pub fn to_bytes(&self) -> io::Result<Vec<u8>> {
    let encoding = AdmissionEncoding {
      format: FORMAT.to_owned(),
      curve: curve::NAME.to_owned(),
      basis: SHIFTED_TAU_BASIS.to_owned(),
      source_manifest_json: self.source_manifest_json.clone(),
      source_manifest_blake3: hex(&self.source_manifest_digest),
      setup_id: hex(&self.public_setup.id),
      public_max_degree: self.public_setup.max_degree as u64,
      g1: self.g1.map(|point| hex(&encode_g1(&point))),
      g2: hex(&encode_g2(&self.g2)),
      tau_g2: hex(&encode_g2(&self.tau_g2)),
    };
    let mut bytes = serde_json::to_vec_pretty(&encoding).map_err(invalid)?;
    bytes.push(b'\n');
    Ok(bytes)
  }

  /// Authenticate the exact admission bytes before parsing. The trusted pin
  /// must be configured separately from the proof, verifying key and admission file.
  pub fn from_bytes(
    bytes: &[u8],
    trusted_admission: [u8; 32],
  ) -> io::Result<Self> {
    if bytes.len() as u64 > MAX_ADMISSION_BYTES {
      return Err(invalid("Ignition admission exceeds 4 MiB"));
    }
    if blake3::hash(bytes).as_bytes() != &trusted_admission {
      return Err(invalid("Ignition admission digest mismatch"));
    }
    let encoding: AdmissionEncoding =
      serde_json::from_slice(bytes).map_err(invalid)?;
    if encoding.format != FORMAT
      || encoding.curve != curve::NAME
      || encoding.basis != SHIFTED_TAU_BASIS
    {
      return Err(invalid(
        "Ignition admission format, curve or basis mismatch",
      ));
    }
    let source_manifest_digest = unhex(&encoding.source_manifest_blake3)?;
    let manifest = parse_source_manifest(
      encoding.source_manifest_json.as_bytes(),
      source_manifest_digest,
    )?;
    let public_setup = PublicSetup {
      max_degree: usize::try_from(encoding.public_max_degree)
        .map_err(invalid)?,
      id: unhex(&encoding.setup_id)?,
    };
    if public_setup != manifest.public_setup()? {
      return Err(invalid(
        "Ignition admission setup identity or degree disagrees with its source manifest",
      ));
    }
    let g1 = [
      decode_g1(&unhex::<64>(&encoding.g1[0])?)?,
      decode_g1(&unhex::<64>(&encoding.g1[1])?)?,
    ];
    let g2 = decode_g2(&unhex::<128>(&encoding.g2)?)?;
    let tau_g2 = decode_g2(&unhex::<128>(&encoding.tau_g2)?)?;
    cache::validate_anchors(&g1, g2, tau_g2)?;
    Ok(Self {
      source_manifest_json: encoding.source_manifest_json,
      source_manifest_digest,
      public_setup,
      g1,
      g2,
      tau_g2,
    })
  }

  pub fn read(path: &Path, pin: [u8; 32]) -> io::Result<Self> {
    if !fs::metadata(path)?.is_file() {
      return Err(invalid("Ignition admission must be a regular file"));
    }
    let file = File::open(path)?;
    if !file.metadata()?.is_file() {
      return Err(invalid("Ignition admission must be a regular file"));
    }
    let mut bytes = Vec::new();
    file.take(MAX_ADMISSION_BYTES + 1).read_to_end(&mut bytes)?;
    Self::from_bytes(&bytes, pin)
  }

  pub fn public_setup(&self) -> PublicSetup {
    self.public_setup
  }

  pub fn source_manifest_digest(&self) -> [u8; 32] {
    self.source_manifest_digest
  }

  pub fn anchors(&self) -> Srs {
    Srs {
      g1: self.g1.to_vec(),
      g2: self.g2,
      tau_g2: self.tau_g2,
      public_setup: self.public_setup,
    }
  }

  pub fn pairing_keys(&self) -> [G2Affine; 2] {
    [self.g2, self.tau_g2]
  }

  pub fn check_verifier(&self, params: &VerifierParams) -> io::Result<()> {
    if params.public_setup != self.public_setup
      || params.g1 != self.g1
      || params.g2 != self.g2
      || params.tau_g2 != self.tau_g2
    {
      return Err(invalid(
        "verifier parameters do not match Ignition admission",
      ));
    }
    super::validate_prefix(
      params.max_trace_len(),
      self.public_setup.max_degree + 1,
    )
  }

  /// Compare an authenticated cache load with the admitted source and anchors.
  /// This does not replace loading the cache against its separately trusted pin.
  pub fn check_cache(
    &self,
    srs: &Srs,
    identity: &IgnitionCacheIdentity,
  ) -> io::Result<()> {
    if srs.public_setup != self.public_setup
      || identity.public_setup != self.public_setup
      || identity.source_manifest_digest != self.source_manifest_digest
      || srs.g1.len() < 2
      || srs.g1[..2] != self.g1
      || srs.g2 != self.g2
      || srs.tau_g2 != self.tau_g2
      || srs.max_len() > identity.prefix_len
    {
      return Err(invalid("cache does not match Ignition admission"));
    }
    super::validate_prefix(
      identity.prefix_len,
      self.public_setup.max_degree + 1,
    )?;
    super::validate_prefix(srs.max_len(), self.public_setup.max_degree + 1)
  }
}

#[cfg(test)]
pub(crate) fn test_admission(
  tau: u64,
  count: usize,
  marker: u8,
) -> (IgnitionAdmission, Srs) {
  use super::{
    Contribution, FINAL_ADDRESS, SOURCE_FORMAT, SourceManifest, Transcript,
  };
  use crate::kzg::curve::{Fr, G1Projective};
  use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
  use ark_ff::{Field, PrimeField};

  assert!(tau != 0 && count >= 2 && count.is_power_of_two());
  let tau = Fr::from(tau);
  let g1: Vec<_> = (1..=count)
    .map(|exponent| {
      (G1Projective::generator() * tau.pow([exponent as u64])).into_affine()
    })
    .collect();
  let tau_g2 = (G2Affine::generator() * tau).into_affine();
  let total = u32::try_from(count).unwrap();
  let mut transcript: Vec<_> = [0, 1, total, 1, total, 2, 0]
    .into_iter()
    .flat_map(u32::to_be_bytes)
    .collect();
  for point in &g1 {
    for coordinate in [point.x, point.y] {
      transcript.extend(
        coordinate.into_bigint().0.into_iter().flat_map(u64::to_be_bytes),
      );
    }
  }
  for point in [tau_g2; 2] {
    for coordinate in [point.x.c0, point.x.c1, point.y.c0, point.y.c1] {
      transcript.extend(
        coordinate.into_bigint().0.into_iter().flat_map(u64::to_be_bytes),
      );
    }
  }
  transcript.extend_from_slice(blake2b_simd::blake2b(&transcript).as_bytes());
  let manifest = SourceManifest {
    format: SOURCE_FORMAT.to_owned(),
    ceremony: format!("synthetic ignition {marker}"),
    basis: SHIFTED_TAU_BASIS.to_owned(),
    num_g1_points: total,
    points_per_transcript: total,
    contribution: Contribution {
      position: 197,
      address: FINAL_ADDRESS.to_owned(),
      transcripts: vec![Transcript {
        index: 0,
        blake2b512: blake2b_simd::blake2b(&transcript).to_hex().to_string(),
      }],
    },
    predecessor: None,
  };
  let source_bytes = serde_json::to_vec_pretty(&manifest).unwrap();
  let srs = Srs {
    g1,
    g2: G2Affine::generator(),
    tau_g2,
    public_setup: manifest.public_setup().unwrap(),
  };
  let admission = IgnitionAdmission {
    source_manifest_json: String::from_utf8(source_bytes.clone()).unwrap(),
    source_manifest_digest: *blake3::hash(&source_bytes).as_bytes(),
    public_setup: srs.public_setup,
    g1: [srs.g1[0], srs.g1[1]],
    g2: srs.g2,
    tau_g2: srs.tau_g2,
  };
  let bytes = admission.to_bytes().unwrap();
  (
    IgnitionAdmission::from_bytes(&bytes, *blake3::hash(&bytes).as_bytes())
      .unwrap(),
    srs,
  )
}

#[cfg(test)]
pub(crate) fn test_admission_cache(
  path: &Path,
  admission: &IgnitionAdmission,
  srs: &Srs,
) -> IgnitionCacheIdentity {
  srs.validate().unwrap();
  admission.check_verifier(&VerifierParams::from_srs(srs)).unwrap();
  let mut output = cache::CacheWriter::create(
    path,
    srs.max_len(),
    admission.public_setup,
    admission.source_manifest_digest,
  )
  .unwrap();
  output.push(&srs.g1).unwrap();
  output
    .finish(&super::Anchors {
      g1: admission.g1,
      tau_g2: admission.tau_g2,
      contribution_g2: admission.tau_g2,
    })
    .unwrap()
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::AffineRepr;
  use std::{
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
  };

  static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

  struct Directory(PathBuf);

  impl Directory {
    fn new() -> Self {
      let path = std::env::temp_dir().join(format!(
        "ix-ignition-admission-{}-{}",
        std::process::id(),
        NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed),
      ));
      fs::create_dir(&path).unwrap();
      Self(path)
    }
  }

  impl Drop for Directory {
    fn drop(&mut self) {
      let _ = fs::remove_dir_all(&self.0);
    }
  }

  fn repin(value: &serde_json::Value) -> io::Result<IgnitionAdmission> {
    let bytes = serde_json::to_vec(value).unwrap();
    IgnitionAdmission::from_bytes(&bytes, *blake3::hash(&bytes).as_bytes())
  }

  #[test]
  fn admission_roundtrip_authorizes_verifier_without_cache() {
    let (admission, srs) = test_admission(7, 16, 1);
    let bytes = admission.to_bytes().unwrap();
    let decoded =
      IgnitionAdmission::from_bytes(&bytes, *blake3::hash(&bytes).as_bytes())
        .unwrap();
    assert_eq!(decoded.to_bytes().unwrap(), bytes);
    assert_eq!(decoded.source_manifest_json, admission.source_manifest_json);
    assert_eq!(decoded.anchors().g1, srs.g1[..2]);
    assert_eq!(decoded.pairing_keys(), [srs.g2, srs.tau_g2]);
    let params = VerifierParams::with_max_trace_len(&decoded.anchors(), 16);
    let portable =
      VerifierParams::from_bytes(&params.to_bytes().unwrap()).unwrap();
    decoded.check_verifier(&portable).unwrap();
  }

  #[test]
  fn cache_admission_preserves_source_bytes_and_ignores_cached_prefix_size() {
    let directory = Directory::new();
    let (admission, srs) = test_admission(7, 16, 1);
    let source = directory.0.join("source.json");
    fs::write(&source, &admission.source_manifest_json).unwrap();
    for prefix_len in [4, 16] {
      let cache = directory.0.join(format!("cache-{prefix_len}.bin"));
      let prefix = Srs {
        g1: srs.g1[..prefix_len].to_vec(),
        g2: srs.g2,
        tau_g2: srs.tau_g2,
        public_setup: srs.public_setup,
      };
      let receipt = test_admission_cache(&cache, &admission, &prefix);
      let (anchors, identity) =
        load_ignition_cache_with_identity(&cache, receipt.digest, 2).unwrap();
      assert_eq!(identity, receipt);
      assert_eq!(identity.prefix_len, prefix_len);
      admission.check_cache(&anchors, &identity).unwrap();
      let derived = IgnitionAdmission::from_cache(
        &cache,
        receipt.digest,
        &source,
        admission.source_manifest_digest,
      )
      .unwrap();
      assert_eq!(derived.to_bytes().unwrap(), admission.to_bytes().unwrap());
      assert!(
        IgnitionAdmission::from_cache(
          &cache,
          [0; 32],
          &source,
          admission.source_manifest_digest,
        )
        .is_err()
      );
      fs::remove_file(cache).unwrap();
    }
    fs::remove_file(source).unwrap();
    let path = directory.0.join("admission.json");
    let bytes = admission.to_bytes().unwrap();
    fs::write(&path, &bytes).unwrap();
    let loaded =
      IgnitionAdmission::read(&path, *blake3::hash(&bytes).as_bytes()).unwrap();
    loaded.check_verifier(&VerifierParams::from_srs(&srs)).unwrap();
  }

  #[test]
  fn cache_admission_rejects_relabelled_identity_and_different_source_pin() {
    let directory = Directory::new();
    let (admission, srs) = test_admission(7, 16, 1);
    let source = directory.0.join("source.json");
    fs::write(&source, &admission.source_manifest_json).unwrap();
    let cache = directory.0.join("cache.bin");
    let dev_setup = PublicSetup::known_trapdoor(15, b"admission-relabel");
    let mut output = cache::CacheWriter::create(
      &cache,
      16,
      dev_setup,
      admission.source_manifest_digest,
    )
    .unwrap();
    output.push(&srs.g1).unwrap();
    let receipt = output
      .finish(&super::super::Anchors {
        g1: admission.g1,
        tau_g2: admission.tau_g2,
        contribution_g2: admission.tau_g2,
      })
      .unwrap();
    assert!(
      IgnitionAdmission::from_cache(
        &cache,
        receipt.digest,
        &source,
        admission.source_manifest_digest,
      )
      .is_err()
    );

    let real_cache = directory.0.join("valid-cache.bin");
    let receipt = test_admission_cache(&real_cache, &admission, &srs);
    let mut changed_source = admission.source_manifest_json.clone();
    changed_source.push(' ');
    fs::write(&source, &changed_source).unwrap();
    assert!(
      IgnitionAdmission::from_cache(
        &real_cache,
        receipt.digest,
        &source,
        *blake3::hash(changed_source.as_bytes()).as_bytes(),
      )
      .is_err()
    );
  }

  #[test]
  fn admission_requires_exact_external_pin_and_bounded_schema() {
    let (admission, _) = test_admission(7, 16, 1);
    let bytes = admission.to_bytes().unwrap();
    assert!(IgnitionAdmission::from_bytes(&bytes, [0; 32]).is_err());
    let mut changed = bytes.clone();
    changed.push(b' ');
    assert!(
      IgnitionAdmission::from_bytes(&changed, *blake3::hash(&bytes).as_bytes())
        .is_err()
    );
    let oversized =
      vec![b' '; usize::try_from(MAX_ADMISSION_BYTES).unwrap() + 1];
    assert!(
      IgnitionAdmission::from_bytes(
        &oversized,
        *blake3::hash(&oversized).as_bytes()
      )
      .is_err()
    );
    let mut value: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    value["extra"] = true.into();
    assert!(repin(&value).is_err());
  }

  #[test]
  fn admission_rejects_inconsistent_source_identity_and_anchors() {
    let (admission, _) = test_admission(7, 16, 1);
    let original: serde_json::Value =
      serde_json::from_slice(&admission.to_bytes().unwrap()).unwrap();
    let zero_digest = "00".repeat(32);
    for (field, replacement) in [
      ("curve", "bls12-381"),
      ("basis", "unshifted"),
      ("source_manifest_blake3", zero_digest.as_str()),
      ("setup_id", zero_digest.as_str()),
    ] {
      let mut value = original.clone();
      value[field] = replacement.into();
      assert!(repin(&value).is_err());
    }
    let mut wrong_degree = original.clone();
    wrong_degree["public_max_degree"] = 31.into();
    assert!(repin(&wrong_degree).is_err());
    let mut wrong_g1 = original.clone();
    wrong_g1["g1"][0] = hex(&encode_g1(&G1Affine::generator())).into();
    assert!(repin(&wrong_g1).is_err());
    let mut noncanonical = original.clone();
    noncanonical["g2"] = "ff".repeat(128).into();
    assert!(repin(&noncanonical).is_err());
    let mut wrong_source = original;
    let (other, _) = test_admission(7, 16, 2);
    wrong_source["source_manifest_json"] = other.source_manifest_json.into();
    wrong_source["source_manifest_blake3"] =
      hex(&other.source_manifest_digest).into();
    assert!(repin(&wrong_source).is_err());
  }

  #[test]
  fn admission_rejects_known_development_identity_and_relabelled_verifier() {
    let (admission, _) = test_admission(7, 16, 1);
    let mut development = Srs::unsafe_dev_setup(16, b"ignition-admission-dev");
    let mut value: serde_json::Value =
      serde_json::from_slice(&admission.to_bytes().unwrap()).unwrap();
    value["setup_id"] = hex(&development.public_setup.id).into();
    assert!(repin(&value).is_err());
    assert!(
      admission
        .check_verifier(&VerifierParams::from_srs(&development))
        .is_err()
    );
    development.public_setup = admission.public_setup();
    assert!(
      admission
        .check_verifier(&VerifierParams::from_srs(&development))
        .is_err()
    );
  }

  #[test]
  fn admission_checks_cache_source_receipt_and_all_anchors() {
    let (admission, mut srs) = test_admission(7, 16, 1);
    let identity = IgnitionCacheIdentity {
      prefix_len: 16,
      digest: [9; 32],
      public_setup: admission.public_setup(),
      source_manifest_digest: admission.source_manifest_digest(),
    };
    admission.check_cache(&srs, &identity).unwrap();
    let mut bad = identity;
    bad.source_manifest_digest[0] ^= 1;
    assert!(admission.check_cache(&srs, &bad).is_err());
    let mut bad = identity;
    bad.public_setup.max_degree += 1;
    assert!(admission.check_cache(&srs, &bad).is_err());
    let mut bad = identity;
    bad.prefix_len = 8;
    assert!(admission.check_cache(&srs, &bad).is_err());
    srs.g1[0] = -srs.g1[0];
    assert!(admission.check_cache(&srs, &identity).is_err());
  }
}
