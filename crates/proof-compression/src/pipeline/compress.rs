//! Compression of a normalized aggregate root through FRI, first KZG,
//! recursive KZG and an optional terminal proof, in this process.
//!
//! Each stage reads its predecessor's directory under the output directory
//! and writes its own, ending with a `complete` marker that names the
//! configuration it was proved under. A rerun into the same directory loads
//! and checks every marked stage up to the first unmarked one, then deletes
//! and reruns that stage and all after it.
use super::{
  FixedRoot, Result, TerminalOptions, TerminalSystem, first, fixed_cache,
  groth16, init_fri, plonk, root,
  setup::{SetupClass, SetupConfig},
  stages, statement, storage, wrap,
};
use std::{
  fs, io,
  path::{Path, PathBuf},
  sync::mpsc,
  time::Duration,
};

/// The proof `compress` returns, also left in its output directory.
const COMPRESSED_PROOF: &str = "compressed.bin";
/// Written last into a stage directory, once its output has been checked.
const COMPLETE: &str = "complete";
/// The root input directory under the output directory.
const ROOT: &str = "root";

/// The proof `compress` compresses and where its stages are kept.
#[derive(Clone, Copy)]
pub struct CompressInput<'a> {
  /// The aggregation backend's verifying key.
  pub vk: &'a [u8],
  /// The aggregate root proof.
  pub proof: &'a [u8],
  /// The claim the root proves.
  pub claim: &'a [u8],
  /// The root statement the caller derived for `claim`.
  pub statement: &'a [u8],
  /// The fixed layout the root is normalized to, as JSON.
  pub fixed_root: Option<&'a str>,
  /// Stage directories: empty or missing to start, or an earlier run of the
  /// same root to resume.
  pub out: &'a Path,
}

/// Everything the stages read besides their input directories.
pub struct CompressConfig {
  pub setup: SetupConfig,
  /// Fixed preprocessing shared between runs, keyed by executable and
  /// stage verifying key.
  pub fixed_cache: PathBuf,
  /// Compiled PLONK circuits, keys and parameter exports.
  pub plonk_cache: PathBuf,
  /// Log2 of the first KZG stage's trace height: 24 or 25.
  pub log_height: u32,
  pub terminal: TerminalOptions,
  /// Host memory the first KZG stage may spend prefetching partitions.
  pub prefetch_bytes: usize,
  /// KZG CUDA backend settings, installed once before the first KZG stage.
  #[cfg(feature = "cuda")]
  pub cuda: crate::kzg::cuda::Settings,
}

impl CompressConfig {
  /// The configuration `ix compress` runs with. `development` selects the
  /// known-trapdoor setup. Cross-run caches live under `cache_root` unless
  /// `IX_KZG_FIXED_CACHE` or `IX_KZG_SRS_CACHE` name other directories; the
  /// setup, prefetch budget (`IX_KZG_PREFETCH_GIB`) and CUDA settings
  /// (`IX_KZG_CUDA_*`, `IX_KZG_MSM_CHUNK_POINTS`) come from the environment.
  pub fn from_env(
    cache_root: &Path,
    development: bool,
    log_height: u32,
    terminal: TerminalOptions,
  ) -> Result<Self> {
    let mut setup = SetupConfig::from_env(development)?;
    if let SetupConfig::Development { cache_directory: directory @ None } =
      &mut setup
    {
      *directory = Some(cache_root.join("development-srs"));
    }
    let prefetch_gib = match std::env::var("IX_KZG_PREFETCH_GIB") {
      Ok(value) => value.parse::<usize>()?,
      Err(std::env::VarError::NotPresent) => 32,
      Err(error) => return Err(error.into()),
    };
    Ok(Self {
      setup,
      fixed_cache: std::env::var_os("IX_KZG_FIXED_CACHE")
        .map_or_else(|| cache_root.join("fixed-preprocessing"), PathBuf::from),
      plonk_cache: cache_root.join("plonk"),
      log_height,
      terminal,
      prefetch_bytes: prefetch_gib
        .checked_mul(1 << 30)
        .ok_or("prefetch budget overflow")?,
      #[cfg(feature = "cuda")]
      cuda: cuda_settings_from_env()?,
    })
  }

  /// Reject unsupported combinations before any checkpoint is written.
  fn validate(&self) -> Result<()> {
    let terminal = self.terminal;
    if terminal.allow_development && terminal.system != TerminalSystem::Groth16
    {
      return Err(
        "development terminal keys are supported only for Groth16".into(),
      );
    }
    if terminal.system != TerminalSystem::None
      && self.setup.class() == SetupClass::Development
    {
      return Err(
        "terminal proofs require admitted inner KZG parameters; omit --dev-srs"
          .into(),
      );
    }
    match terminal.system {
      TerminalSystem::Plonk if !cfg!(feature = "plonk") => {
        return Err(
          "this ix was built without PLONK; rebuild with IX_PLONK=1".into(),
        );
      },
      TerminalSystem::Plonk
        if std::env::var("IX_PLONK_BACKEND").as_deref() == Ok("cuda")
          && !cfg!(feature = "cuda") =>
      {
        return Err(
          "IX_PLONK_BACKEND=cuda requires a build with IX_CUDA=1".into(),
        );
      },
      TerminalSystem::Groth16 if !cfg!(feature = "groth16") => {
        return Err(
          "this ix was built without Groth16; rebuild with IX_GROTH16=1".into(),
        );
      },
      TerminalSystem::Groth16 => {
        groth16::preflight(terminal.allow_development)?
      },
      _ => {},
    }
    if !matches!(self.log_height, 24 | 25) {
      return Err(
        "--log-height must be 24 or 25 for the supported recursive verifying keys"
          .into(),
      );
    }
    if std::env::var_os("IX_ROOT_GENERIC_HASHES").is_some() {
      return Err(
        "unset IX_ROOT_GENERIC_HASHES for the supported compression verifying key"
          .into(),
      );
    }
    Ok(())
  }

  /// The setup a KZG stage's marker records: a stage proved under other
  /// parameters is rerun.
  fn setup_key(&self) -> String {
    match &self.setup {
      SetupConfig::Ignition { manifest, .. } => {
        format!("ignition {}", blake3::Hash::from_bytes(*manifest).to_hex())
      },
      SetupConfig::Development { .. } => "development".into(),
    }
  }
}

/// Read the KZG CUDA backend settings from the environment. The pipeline
/// proves on device 0 unless `IX_KZG_CUDA_DEVICES` lists others.
#[cfg(feature = "cuda")]
fn cuda_settings_from_env() -> Result<crate::kzg::cuda::Settings> {
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
  }
  match var("IX_KZG_CUDA_SRS_CACHE").as_deref() {
    None => {},
    Some("1") => settings.srs_cache = true,
    Some("0") => settings.srs_cache = false,
    Some(other) => {
      return Err(
        format!("IX_KZG_CUDA_SRS_CACHE must be 1 or 0, not {other}").into(),
      );
    },
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
  Ok(settings)
}

/// What the KZG stage functions read from a compression's configuration.
pub(crate) struct StageConfig {
  pub(super) setup: SetupConfig,
  /// The fixed-preprocessing cache root; `None` keeps the cache inside the
  /// stage directory.
  pub(super) fixed_cache_root: Option<PathBuf>,
  pub(super) prefetch_bytes: usize,
}

impl StageConfig {
  fn from_config(config: &CompressConfig) -> Self {
    Self {
      setup: config.setup.clone(),
      fixed_cache_root: Some(config.fixed_cache.clone()),
      prefetch_bytes: config.prefetch_bytes,
    }
  }

  pub(super) fn fixed_cache(
    &self,
    stage: &Path,
    vk: &[u8],
  ) -> fixed_cache::FixedCache {
    let root = self
      .fixed_cache_root
      .clone()
      .unwrap_or_else(|| stage.join("kzg/fixed-cache"));
    fixed_cache::FixedCache::from_identity(&root, vk)
  }

  #[cfg(test)]
  pub(super) const fn development() -> Self {
    Self {
      setup: SetupConfig::Development { cache_directory: None },
      fixed_cache_root: None,
      prefetch_bytes: 0,
    }
  }
}

/// The files of a root input directory: the backend key, root proof,
/// expected statement and, for a normalized root, its fixed layout.
pub(super) fn root_files(
  vk: &[u8],
  proof: &[u8],
  words: &statement::Statement,
  fixed_root: Option<&str>,
) -> Result<Vec<(&'static str, Vec<u8>)>> {
  let mut files = vec![
    ("root-vk.bin", vk.to_vec()),
    ("root-proof.bin", proof.to_vec()),
    ("root-claims.bin", statement::to_claims_bytes(words)),
  ];
  if let Some(layout) = fixed_root {
    files.push((
      root::FIXED_ROOT_LAYOUT,
      FixedRoot::from_json(layout)?.to_json().into_bytes(),
    ));
  }
  Ok(files)
}

/// Prepare `out` to hold the stages of the root in `files`. An empty or
/// missing directory starts a new compression; any other must hold a `root/`
/// whose files match these, or it is refused unchanged. Root files an
/// interrupted run did not write are written.
fn open_output(out: &Path, files: &[(&'static str, Vec<u8>)]) -> Result<()> {
  fs::create_dir_all(out)?;
  let root = out.join(ROOT);
  if fs::read_dir(out)?.next().is_some() {
    let refused = || -> Box<dyn std::error::Error> {
      format!(
        "{} holds another compression: its root/ differs from this proof, \
         layout or statement; choose another --out directory",
        out.display()
      )
      .into()
    };
    if !root.is_dir() {
      return Err(refused());
    }
    for name in [
      "root-vk.bin",
      "root-proof.bin",
      "root-claims.bin",
      root::FIXED_ROOT_LAYOUT,
    ] {
      let expected = files.iter().find(|(file, _)| *file == name);
      match fs::read(root.join(name)) {
        Ok(bytes) => match expected {
          Some((_, expected))
            if blake3::hash(&bytes) == blake3::hash(expected) => {},
          _ => return Err(refused()),
        },
        Err(error) if error.kind() == io::ErrorKind::NotFound => {},
        Err(error) => return Err(error.into()),
      }
    }
  }
  fs::create_dir_all(&root)?;
  for (name, bytes) in files {
    let path = root.join(name);
    if !path.try_exists()? {
      storage::write_atomic(&path, bytes)?;
    }
  }
  Ok(())
}

/// Compress the normalized root in `input` to a recursive KZG proof, or with
/// a terminal system to that system's proof envelope, and return it. Stages
/// run in this process and keep their directories under `input.out`, so an
/// interrupted run resumes from its last complete stage when rerun with the
/// same input and output directory.
pub fn compress(
  input: CompressInput<'_>,
  config: &CompressConfig,
) -> Result<Vec<u8>> {
  let words = super::check_claim(input.claim, input.statement)?;
  config.validate()?;
  if config.terminal.system == TerminalSystem::Groth16 {
    groth16::check_statement(&words, config.terminal.allow_development)?;
  }
  let files = root_files(input.vk, input.proof, &words, input.fixed_root)?;
  open_output(input.out, &files)?;
  drop(files);
  let _monitor = MemoryMonitor::start();
  let mut checkpoints = Checkpoints { out: input.out, rerun: false };
  let proof = run_stages(&mut checkpoints, config, &words)?;
  storage::write_atomic(&input.out.join(COMPRESSED_PROOF), &proof)?;
  Ok(proof)
}

/// Every stage from the root input to the returned proof.
fn run_stages(
  checkpoints: &mut Checkpoints<'_>,
  config: &CompressConfig,
  words: &statement::Statement,
) -> Result<Vec<u8>> {
  let root = checkpoints.out.join(ROOT);
  let fri = checkpoints.stage(
    "fri",
    "fri/v1",
    &tracing::info_span!("compression/fri"),
    |dir| root::run(&root, dir, true),
    |dir| check_fri(dir, words),
  )?;
  #[cfg(feature = "cuda")]
  crate::kzg::cuda::configure(config.cuda.clone());
  let stage = StageConfig::from_config(config);
  let setup = config.setup_key();
  let log_height = usize::try_from(config.log_height)?;
  let first = checkpoints.stage(
    "first-kzg",
    &format!("first-kzg/v1 log-height={log_height} setup={setup}"),
    &tracing::info_span!("compression/kzg"),
    |dir| first::run(&fri, dir, log_height, &stage),
    |dir| check_first(dir, words),
  )?;
  let final_dir = checkpoints.stage(
    "final-kzg",
    &format!("final-kzg/v1 setup={setup}"),
    &tracing::info_span!("compression/wrap"),
    |dir| wrap::run(&first, dir, &stage),
    |dir| check_final(dir, words, &config.setup),
  )?;
  drop(stage);
  let terminal = config.terminal;
  let key = format!(
    "{:?}/v1 allow-development={} setup={setup}",
    terminal.system, terminal.allow_development
  );
  let dir = match terminal.system {
    TerminalSystem::None => {
      let mut proof = super::PROOF_TAG.to_vec();
      proof.extend(fs::read(final_dir.join("kzg/packet.bin"))?);
      return Ok(proof);
    },
    TerminalSystem::Plonk => checkpoints.stage(
      "plonk",
      &key,
      &tracing::info_span!("compression/plonk"),
      |dir| prove_plonk(&final_dir, dir, words, config),
      |dir| check_envelope(dir, plonk::PROOF_TAG),
    )?,
    TerminalSystem::Groth16 => checkpoints.stage(
      "groth16",
      &key,
      &tracing::info_span!("compression/groth16"),
      |dir| prove_groth16(&final_dir, dir, words, config),
      |dir| check_envelope(dir, groth16::PROOF_TAG),
    )?,
  };
  Ok(fs::read(dir.join("proof.envelope.bin"))?)
}

/// The stage directories under a compression's output directory.
struct Checkpoints<'a> {
  out: &'a Path,
  /// Set once a stage has run, so every later stage runs too.
  rerun: bool,
}

impl Checkpoints<'_> {
  /// The directory of stage `name`. When it is marked complete under `key`
  /// and no earlier stage ran, it is checked and reused; otherwise it is
  /// deleted, proved again, checked and marked. Pooled GPU memory is
  /// returned to the driver after the stage proves, whether or not it
  /// succeeded.
  fn stage(
    &mut self,
    name: &str,
    key: &str,
    span: &tracing::Span,
    prove: impl FnOnce(&Path) -> Result<()>,
    check: impl FnOnce(&Path) -> Result<()>,
  ) -> Result<PathBuf> {
    let dir = self.out.join(name);
    let marker = dir.join(COMPLETE);
    if !self.rerun {
      match fs::read(&marker) {
        Ok(recorded) if recorded == key.as_bytes() => {
          check(&dir).map_err(|error| {
            format!(
              "completed compression {name} stage in {} fails its check: \
               {error}; delete it to prove it again",
              dir.display()
            )
          })?;
          tracing::info!("compression {name}: reusing the completed stage");
          return Ok(dir);
        },
        Ok(_) => {},
        Err(error) if error.kind() == io::ErrorKind::NotFound => {},
        Err(error) => return Err(error.into()),
      }
    }
    self.rerun = true;
    match fs::remove_dir_all(&dir) {
      Ok(()) => {},
      Err(error) if error.kind() == io::ErrorKind::NotFound => {},
      Err(error) => return Err(error.into()),
    }
    let proved = span.in_scope(|| prove(&dir));
    #[cfg(feature = "cuda")]
    multi_stark::cuda::release_device_memory();
    proved.and_then(|()| check(&dir)).map_err(|error| {
      format!(
        "compression {name} failed: {error}; completed stages are kept for a \
         rerun"
      )
    })?;
    storage::write_atomic(&marker, key.as_bytes())?;
    Ok(dir)
  }
}

/// The saved FRI proof exposes the expected root statement.
fn check_fri(dir: &Path, words: &statement::Statement) -> Result<()> {
  let fixture = init_fri::load(dir)?;
  let actual =
    statement::from_scalars(&stages::scalar_statement(&fixture.public))?;
  if actual != *words {
    return Err(
      "saved FRI statement differs from the expected root statement".into(),
    );
  }
  Ok(())
}

/// The first KZG packet carries the expected statement after its verifying
/// key id. The recursive stage verifies its proof.
fn check_first(dir: &Path, words: &statement::Statement) -> Result<()> {
  let packet = fs::read(dir.join("kzg/packet.bin"))?;
  let encoded: Vec<u8> =
    words.iter().flat_map(|word| word.to_le_bytes()).collect();
  if packet.get(32..32 + encoded.len()) != Some(encoded.as_slice()) {
    return Err(
      "first KZG packet differs from the expected root statement".into(),
    );
  }
  Ok(())
}

/// The recursive verifying key is admitted by the setup and verifies the
/// recursive packet for the expected statement.
fn check_final(
  dir: &Path,
  words: &statement::Statement,
  setup: &SetupConfig,
) -> Result<()> {
  let vk = wrap::VerifyingKey::from_bytes(&fs::read(dir.join("vk.bin"))?)?;
  if let Some(admission) = setup.ignition_admission() {
    vk.check_ignition_admission(admission)?;
  } else {
    vk.check_setup_class(setup.class())?;
  }
  vk.verify(&fs::read(dir.join("kzg/packet.bin"))?, words)?;
  Ok(())
}

/// The terminal stage left a proof envelope of its system.
fn check_envelope(dir: &Path, tag: &[u8]) -> Result<()> {
  let envelope = fs::read(dir.join("proof.envelope.bin"))?;
  if envelope.len() <= tag.len() + 32 || !envelope.starts_with(tag) {
    return Err("terminal proof envelope is malformed".into());
  }
  Ok(())
}

#[cfg(feature = "plonk")]
fn prove_plonk(
  final_dir: &Path,
  out: &Path,
  words: &statement::Statement,
  config: &CompressConfig,
) -> Result<()> {
  let verifier = final_dir.join("vk.bin");
  let trusted = blake3::hash(&fs::read(&verifier)?).to_hex();
  plonk::wrap_packet(
    &verifier,
    &final_dir.join("kzg/packet.bin"),
    trusted.as_str(),
    words,
    &config.plonk_cache,
    out,
    &config.setup,
  )
}

#[cfg(not(feature = "plonk"))]
fn prove_plonk(
  _final_dir: &Path,
  _out: &Path,
  _words: &statement::Statement,
  _config: &CompressConfig,
) -> Result<()> {
  Err("this ix was built without PLONK; rebuild with IX_PLONK=1".into())
}

#[cfg(feature = "groth16")]
fn prove_groth16(
  final_dir: &Path,
  out: &Path,
  words: &statement::Statement,
  config: &CompressConfig,
) -> Result<()> {
  let verifier = final_dir.join("vk.bin");
  let trusted = blake3::hash(&fs::read(&verifier)?).to_hex();
  groth16::wrap_packet(
    &verifier,
    &final_dir.join("kzg/packet.bin"),
    trusted.as_str(),
    words,
    out,
    config.terminal.allow_development,
    &config.setup,
  )
}

#[cfg(not(feature = "groth16"))]
fn prove_groth16(
  _final_dir: &Path,
  _out: &Path,
  _words: &statement::Statement,
  _config: &CompressConfig,
) -> Result<()> {
  Err("this ix was built without Groth16; rebuild with IX_GROTH16=1".into())
}

/// Logs the process's resident and peak resident size every 30 seconds
/// until dropped, so a long stage's memory profile is visible in its log.
struct MemoryMonitor {
  _stop: mpsc::Sender<()>,
}

impl MemoryMonitor {
  fn start() -> Self {
    let (stop, stopped) = mpsc::channel::<()>();
    std::thread::spawn(move || {
      while let Err(mpsc::RecvTimeoutError::Timeout) =
        stopped.recv_timeout(Duration::from_secs(30))
      {
        if let Ok(status) = fs::read_to_string("/proc/self/status") {
          eprintln!(
            "{}",
            status
              .lines()
              .filter(|l| l.starts_with("VmRSS:") || l.starts_with("VmHWM:"))
              .collect::<Vec<_>>()
              .join(" ")
          );
        }
      }
    });
    Self { _stop: stop }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn scratch(name: &str) -> PathBuf {
    let path = std::env::temp_dir()
      .join(format!("ix-compress-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&path);
    path
  }

  fn files(proof: &[u8]) -> Vec<(&'static str, Vec<u8>)> {
    root_files(b"vk", proof, &[7; statement::WORDS], None).unwrap()
  }

  #[test]
  fn output_resumes_only_the_same_root() -> Result<()> {
    let out = scratch("open-output");
    open_output(&out, &files(b"proof"))?;
    assert_eq!(fs::read(out.join("root/root-proof.bin"))?, b"proof");
    // An interrupted root write is completed.
    fs::remove_file(out.join("root/root-claims.bin"))?;
    open_output(&out, &files(b"proof"))?;
    assert!(out.join("root/root-claims.bin").is_file());
    // Another proof, or a layout the earlier run did not have, is refused
    // without changing the directory.
    fs::create_dir(out.join("fri"))?;
    assert!(open_output(&out, &files(b"other")).is_err());
    fs::write(out.join("root").join(root::FIXED_ROOT_LAYOUT), b"{}")?;
    assert!(open_output(&out, &files(b"proof")).is_err());
    fs::remove_file(out.join("root").join(root::FIXED_ROOT_LAYOUT))?;
    assert_eq!(fs::read(out.join("root/root-proof.bin"))?, b"proof");
    assert!(out.join("fri").is_dir());
    // A non-empty directory without a root is refused.
    let other = scratch("open-output-foreign");
    fs::create_dir_all(other.join("data"))?;
    assert!(open_output(&other, &files(b"proof")).is_err());
    assert!(!other.join(ROOT).exists());
    fs::remove_dir_all(other)?;
    fs::remove_dir_all(out)?;
    Ok(())
  }

  fn checkpoints(out: &Path) -> Checkpoints<'_> {
    Checkpoints { out, rerun: false }
  }

  #[test]
  fn completed_stages_are_reused_until_one_reruns() -> Result<()> {
    let out = scratch("checkpoints");
    let proved = std::cell::RefCell::new(Vec::new());
    let run =
      |checkpoints: &mut Checkpoints<'_>, keys: [&str; 3]| -> Result<()> {
        for (name, key) in ["a", "b", "c"].into_iter().zip(keys) {
          checkpoints.stage(
            name,
            key,
            &tracing::Span::none(),
            |dir| {
              proved.borrow_mut().push(name);
              fs::create_dir_all(dir)?;
              Ok(fs::write(dir.join("output"), name)?)
            },
            |dir| {
              if fs::read(dir.join("output"))? == name.as_bytes() {
                Ok(())
              } else {
                Err("damaged".into())
              }
            },
          )?;
        }
        Ok(())
      };
    run(&mut checkpoints(&out), ["1", "1", "1"])?;
    assert_eq!(proved.take(), ["a", "b", "c"]);
    run(&mut checkpoints(&out), ["1", "1", "1"])?;
    assert!(proved.take().is_empty());
    // A stage without its marker reruns, and so does every later stage.
    fs::remove_file(out.join("b").join(COMPLETE))?;
    fs::write(out.join("b/stale"), "")?;
    run(&mut checkpoints(&out), ["1", "1", "1"])?;
    assert_eq!(proved.take(), ["b", "c"]);
    assert!(!out.join("b/stale").exists());
    // A stage marked under another configuration reruns.
    run(&mut checkpoints(&out), ["1", "1", "2"])?;
    assert_eq!(proved.take(), ["c"]);
    // A marked stage that fails its check is reported, not overwritten.
    fs::write(out.join("a/output"), "x")?;
    assert!(run(&mut checkpoints(&out), ["1", "1", "2"]).is_err());
    assert!(proved.take().is_empty());
    // A failed stage is left unmarked.
    let failing = checkpoints(&out).stage(
      "d",
      "1",
      &tracing::Span::none(),
      |dir| {
        fs::create_dir_all(dir)?;
        Err("failed".into())
      },
      |_dir| Ok(()),
    );
    assert!(failing.is_err());
    assert!(!out.join("d").join(COMPLETE).exists());
    fs::remove_dir_all(out)?;
    Ok(())
  }
}
