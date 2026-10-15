//! Compression and verification of aggregate root proofs.
mod stages;
pub use stages::{
  FixedRoot, FriVerifier, KzgVerifier, Prepared, RecursiveProof,
  RecursiveStage, RecursiveVerifier, prepare_kzg, prepare_recursive,
  prepare_root, setup,
};

mod first;
mod fixed_cache;
#[cfg(test)]
mod init_claim;
mod init_fri;
mod prover;
mod root;
mod setup;
mod statement;
mod storage;
mod verifier;
mod wrap;

use std::{
  fs,
  path::{Path, PathBuf},
  process::{Command, Stdio},
};

pub const PROOF_TAG: &[u8; 8] = b"IXCMP\0\0\x04";
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

pub fn command(stage: &str, args: &[String]) -> Result<()> {
  configure_backend(stage)?;
  match stage {
    "fri" => root::run(args),
    "kzg" | "wrap" => {
      let config = WorkerConfig::from_env(
        stage,
        args.iter().any(|arg| arg == "--dev-srs"),
      )?;
      let args: Vec<_> =
        args.iter().filter(|arg| *arg != "--dev-srs").cloned().collect();
      if stage == "kzg" {
        first::run(&args, &config)
      } else {
        wrap::run(&args, &config)
      }
    },
    _ => Err("unknown compression stage".into()),
  }
}

pub(crate) struct WorkerConfig {
  setup: setup::SetupConfig,
  fixed_cache_root: Option<PathBuf>,
  prefetch_bytes: usize,
}

impl WorkerConfig {
  fn from_env(stage: &str, allow_development: bool) -> Result<Self> {
    let setup = setup::SetupConfig::from_env(allow_development)?;
    let prefetch_gib = if stage == "kzg" {
      match std::env::var("IX_KZG_PREFETCH_GIB") {
        Ok(value) => value.parse::<usize>()?,
        Err(std::env::VarError::NotPresent) => 32,
        Err(error) => return Err(error.into()),
      }
    } else {
      0
    };
    Ok(Self {
      setup,
      fixed_cache_root: std::env::var_os("IX_KZG_FIXED_CACHE")
        .map(PathBuf::from),
      prefetch_bytes: prefetch_gib
        .checked_mul(1 << 30)
        .ok_or("prefetch budget overflow")?,
    })
  }

  fn fixed_cache(
    &self,
    stage: &Path,
    profile: &[u8],
  ) -> Result<fixed_cache::FixedCache> {
    let root = self
      .fixed_cache_root
      .clone()
      .unwrap_or_else(|| stage.join("kzg/fixed-cache"));
    fixed_cache::FixedCache::from_profile(&root, profile)
  }

  #[cfg(test)]
  const fn development() -> Self {
    Self {
      setup: setup::SetupConfig::Development { cache_directory: None },
      fixed_cache_root: None,
      prefetch_bytes: 0,
    }
  }
}

/// Install the KZG CUDA backend settings from the environment before the
/// first proving operation. Settings already installed in this process are
/// kept. The recursive stage caps device residency unless the environment
/// sets it, so its constraint passes can be admitted beside the resident
/// columns.
///
/// The pipeline proves on one device unless the environment selects more.
#[cfg(feature = "cuda")]
fn configure_backend(stage: &str) -> Result<()> {
  use crate::kzg::cuda::{PassMode, Settings};
  let var = |name: &str| std::env::var(name).ok();
  let devices = match var("IX_KZG_CUDA_DEVICES") {
    Some(list) => list
      .split(',')
      .map(|id| id.trim().parse())
      .collect::<std::result::Result<Vec<i32>, _>>()
      .map_err(|_error| "IX_KZG_CUDA_DEVICES must list CUDA ordinals")?,
    None => vec![0],
  };
  let mut settings = Settings { devices: Some(devices), ..Settings::default() };
  if let Some(value) = var("IX_KZG_MSM_CHUNK_POINTS") {
    settings.msm_chunk_points = value
      .parse()
      .ok()
      .filter(|points| (1..=1 << 28).contains(points))
      .ok_or("IX_KZG_MSM_CHUNK_POINTS must be in 1..=2^28")?;
  }
  if let Some(value) = var("IX_KZG_CUDA_RESIDENT_GIB") {
    settings.resident_limit_bytes = Some(
      value
        .parse::<usize>()
        .ok()
        .and_then(|gib| gib.checked_mul(1 << 30))
        .ok_or("IX_KZG_CUDA_RESIDENT_GIB must be a whole number of GiB")?,
    );
  } else if stage == "wrap" {
    settings.resident_limit_bytes = Some(wrap::DEFAULT_CUDA_RESIDENT_BYTES);
  }
  let switch = |name: &str, on: &str, off: &str| -> Result<Option<bool>> {
    match var(name).as_deref() {
      None => Ok(None),
      Some(value) if value == on => Ok(Some(true)),
      Some(value) if value == off => Ok(Some(false)),
      Some(other) => {
        Err(format!("{name} must be {on} or {off}, not {other}").into())
      },
    }
  };
  if let Some(value) = switch("IX_KZG_CUDA_SRS_CACHE", "1", "0")? {
    settings.srs_cache = value;
  }
  settings.passes = match var("IX_KZG_CUDA_PASSES").as_deref() {
    None | Some("1") => PassMode::Fallback,
    Some("0") => PassMode::Off,
    Some("force") => PassMode::Force,
    Some(other) => {
      return Err(
        format!("IX_KZG_CUDA_PASSES must be 0, 1 or force, not {other}").into(),
      );
    },
  };
  crate::kzg::cuda::configure(settings);
  Ok(())
}

#[cfg(not(feature = "cuda"))]
#[allow(clippy::unnecessary_wraps)]
fn configure_backend(_stage: &str) -> Result<()> {
  Ok(())
}

/// The stage worker executable installed beside `ix`.
pub const WORKER_EXECUTABLE: &str = "ix-compression-worker";

/// The stage worker: `IX_COMPRESSION_WORKER` when set, otherwise the
/// executable of that name beside the running one. Stages run there rather
/// than in this process so the Lean executable links no KZG proving code or
/// its CUDA runtime.
fn worker_executable() -> Result<PathBuf> {
  if let Some(path) = std::env::var_os("IX_COMPRESSION_WORKER") {
    return Ok(PathBuf::from(path));
  }
  let current = std::env::current_exe()?;
  let sibling = current.with_file_name(WORKER_EXECUTABLE);
  if sibling.is_file() {
    return Ok(sibling);
  }
  Err(
    format!(
      "{WORKER_EXECUTABLE} not found beside {}; build it with the ix \
       executable or name it in IX_COMPRESSION_WORKER",
      current.display()
    )
    .into(),
  )
}

fn child(stage: &str, args: &[&str], caches: &Caches) -> Result<()> {
  let status = Command::new(worker_executable()?)
    .arg(stage)
    .args(args)
    .env("IX_KZG_FIXED_CACHE", &caches.fixed)
    .env("IX_KZG_SRS_CACHE", &caches.development_srs)
    .stdout(Stdio::from(std::io::stderr()))
    .stderr(Stdio::inherit())
    .status()?;
  if !status.success() {
    return Err(
      format!("compression {stage} failed ({status}); checkpoints retained")
        .into(),
    );
  }
  Ok(())
}

/// The statement a compressed proof of `claim` exposes, as the caller
/// derived it from its aggregation backend, checked to end in the packed
/// digest of the claim itself.
pub fn check_claim(
  claim: &[u8],
  statement: &[u8],
) -> Result<statement::Statement> {
  let words = statement::from_claims_bytes(statement)?;
  statement::bind_claim(claim, &words)?;
  Ok(words)
}

/// Describe the setup a new run would prove under, or why none is allowed.
pub fn setup_description(allow_development: bool) -> Result<&'static str> {
  Ok(setup::SetupConfig::from_env(allow_development)?.class().description())
}

/// Verify a compressed proof of `claim` with the profile bundled under the
/// packet's id, needing neither the proving backend nor any file.
pub fn verify(
  proof: &[u8],
  claim: &[u8],
  allow_development: bool,
) -> Result<setup::SetupClass> {
  let packet = proof
    .strip_prefix(PROOF_TAG)
    .ok_or("unsupported compressed proof version")?;
  verifier::verify(packet, claim, allow_development)
}

/// Cross-run caches the stages share: fixed preprocessing keyed by the
/// executable and profile, and development SRS files. Variables already set
/// in the environment take precedence over the directory given to `compress`.
struct Caches {
  fixed: PathBuf,
  development_srs: PathBuf,
}

impl Caches {
  fn under(root: &Path) -> Self {
    let named = |name: &str, default: &str| {
      std::env::var_os(name).map_or_else(|| root.join(default), PathBuf::from)
    };
    Self {
      fixed: named("IX_KZG_FIXED_CACHE", "fixed-preprocessing"),
      development_srs: named("IX_KZG_SRS_CACHE", "development-srs"),
    }
  }
}

/// Run the three stages into an empty `out` directory, each as a child
/// process so every heavy phase releases its memory and device state before
/// the next starts. Only each stage's proof and verifying metadata are
/// written; a rerun starts over, reusing the caches under `cache_root`.
pub fn compress(
  vk: &[u8],
  proof: &[u8],
  claim: &[u8],
  statement: &[u8],
  out: &Path,
  cache_root: &Path,
  allow_development: bool,
  log_height: u32,
) -> Result<Vec<u8>> {
  let words = check_claim(claim, statement)?;
  if !matches!(log_height, 24 | 25) {
    return Err(
      "--log-height must be 24 or 25 for the supported recursive profiles"
        .into(),
    );
  }
  // Child stages re-read the same environment; the policy is enforced once
  // here so an unconfigured run fails before any checkpoint is written.
  setup::SetupConfig::from_env(allow_development)?;
  if std::env::var_os("IX_ROOT_GENERIC_HASHES").is_some() {
    return Err(
      "unset IX_ROOT_GENERIC_HASHES for the supported compression profile"
        .into(),
    );
  }
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err(
      "output directory must be empty; use a new --out directory".into(),
    );
  }
  let caches = Caches::under(cache_root);
  let root = out.join("root");
  fs::create_dir_all(&root)?;
  fs::write(root.join("root-vk.bin"), vk)?;
  fs::write(root.join("root-proof.bin"), proof)?;
  fs::write(root.join("root-claims.bin"), statement::to_claims_bytes(&words))?;
  let fri = out.join("fri");
  let first = out.join("first-kzg");
  let final_dir = out.join("final-kzg");
  let path = |p: &Path| -> Result<String> {
    Ok(p.to_str().ok_or("non-UTF8 output path")?.to_owned())
  };
  let (root_s, fri_s, first_s, final_s) =
    (path(&root)?, path(&fri)?, path(&first)?, path(&final_dir)?);
  // Each KZG worker re-reads the environment and decides its own setup;
  // the permission to use development parameters travels as its flag.
  let kzg = |stage, args: &[&str]| {
    let mut args = args.to_vec();
    if allow_development {
      args.push("--dev-srs");
    }
    child(stage, &args, &caches)
  };
  child("fri", &[&root_s, &fri_s, "--prove-outer"], &caches)?;
  let height = log_height.to_string();
  kzg("kzg", &["run", &fri_s, &first_s, &height])?;
  kzg("wrap", &["stage-and-prove", &first_s, &final_s])?;
  let mut result = PROOF_TAG.to_vec();
  result.extend(fs::read(final_dir.join("kzg/packet.bin"))?);
  let packet = &result[PROOF_TAG.len()..];
  wrap::verify(&final_dir, packet, Some(&words))?;
  // A bundled profile pins the aggregation program its proofs attest; the
  // backend this run proved under must be that program, or the bundle is
  // stale and verification elsewhere would accept the wrong statement.
  if let Some(prefix) = verifier::bundled_prefix(packet[..32].try_into()?)
    && *prefix != words[..10]
  {
    return Err(
      "the bundled verifier profile pins a different aggregation program \
       than this build's backend; update the bundle"
        .into(),
    );
  }
  Ok(result)
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn unsupported_claim_is_rejected_before_io() {
    assert!(
      compress(
        b"",
        b"",
        b"wrong",
        &statement::to_claims_bytes(&statement::with_claim(&[0; 10], b"wrong")),
        Path::new("/does-not-exist"),
        Path::new("/does-not-exist"),
        true,
        24
      )
      .is_err()
    );
    assert!(verify(PROOF_TAG, b"wrong", true).is_err());
  }
}
