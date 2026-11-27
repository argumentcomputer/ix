//! The compression stages, run in one process.
//!
//! The pipeline is data: a manifest (`ix-aiur-stages-v1`) lists the stages,
//! each one of the stage kinds below with the setup products it reads and
//! their digests. The manifest's own bytes are pinned by the caller.
//!
//! Every stage runs on its own thread. A stage first does the work that its
//! configuration alone determines (artifact, circuits, Lean export, SRS,
//! fixed-slot setup, PLONK key), then waits for its predecessor's output,
//! which is passed in memory, and proves. A stage's `start` names the stage
//! whose end starts its thread (`null`: the run's start), which reproduces
//! the process-level pipelining of `target/e2e-l3/run.sh`. Each stage
//! verifies its proof natively, checks that a changed output is rejected and
//! compares the key it produced with the pinned one before its output is
//! handed on.
//!
//! Memory: each stage declares, in GB, what it holds while preparing, once
//! prepared and while proving; a stage reserves that from the run's budget
//! before it allocates, so a stage's proving peak waits for another stage's
//! transient preparation to end instead of overrunning the process limit.
//!
//! GPU: unless disabled, the sections that run device work hold a
//! process-wide lock, and the time spent waiting for it is reported.
//!
//! The stage kinds, named after what each stage does:
//! - `fri`: the Goldilocks FRI wrap of the aggregate root;
//! - `fri-verifier`: CompressGL, the FRI verifier over BN254, with a KZG proof;
//! - `kzg-verifier`: the fixed-key narrow stage, which verifies CompressGL's
//!   KZG proof;
//! - `plonk`: the terminal KZG verifier, proved with native Rust (+ Ix-CUDA)
//!   or legacy gnark PLONK.
//!
//! Each stage writes into a directory named after it, with `span` and a
//! GNU-time-style `time.txt` as in `run.sh`'s run directory, and
//! `checks.json` records the checks `run.sh` makes.
pub mod exports;
mod gl;
mod narrow;
mod terminal;
mod wrap;

use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{
  collections::BTreeMap,
  fs,
  path::{Path, PathBuf},
  sync::{
    Condvar, Mutex,
    atomic::{AtomicBool, Ordering},
    mpsc,
  },
  time::{Instant, SystemTime, UNIX_EPOCH},
};

pub const FORMAT: &str = "ix-aiur-stages-v1";

pub type Error = String;

fn io(path: &Path) -> impl Fn(std::io::Error) -> String + '_ {
  move |e| format!("{}: {e}", path.display())
}

pub(crate) fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

pub fn sha256_hex(bytes: &[u8]) -> String {
  format!("{:x}", Sha256::digest(bytes))
}

pub(crate) fn unix_now() -> f64 {
  SystemTime::now().duration_since(UNIX_EPOCH).map_or(0.0, |d| d.as_secs_f64())
}

/// `VmHWM` and `VmRSS` of this process, in bytes.
pub(crate) fn rss() -> (u64, u64) {
  let status = fs::read_to_string("/proc/self/status").unwrap_or_default();
  let field = |name: &str| {
    status
      .lines()
      .find(|l| l.starts_with(name))
      .and_then(|l| l.split_whitespace().nth(1))
      .and_then(|v| v.parse::<u64>().ok())
      .map_or(0, |kib| kib * 1024)
  };
  (field("VmHWM:"), field("VmRSS:"))
}

/// This process's peak resident set (`VmHWM`) in GB.
#[allow(clippy::cast_precision_loss)]
pub(crate) fn peak_rss_gb() -> f64 {
  rss().0 as f64 / 1e9
}

/// A parsed, pinned manifest.
pub struct Manifest {
  pub pin: String,
  pub base: PathBuf,
  pub value: Value,
}

impl Manifest {
  /// Parses `bytes` after checking them against `pin` (BLAKE3, hex).
  /// Relative paths resolve against `base` (the manifest's `base` field when
  /// present).
  pub fn new(bytes: &[u8], pin: &str, base: &Path) -> Result<Self, Error> {
    let digest = blake3::hash(bytes).to_hex().to_string();
    if digest != pin.to_ascii_lowercase() {
      return Err(format!(
        "stages manifest digest {digest} differs from the pin {pin}"
      ));
    }
    let value: Value =
      serde_json::from_slice(bytes).map_err(|e| format!("manifest: {e}"))?;
    if value["format"] != FORMAT {
      return Err(format!("manifest format is not {FORMAT}"));
    }
    let base =
      value["base"].as_str().map_or_else(|| base.to_path_buf(), PathBuf::from);
    let manifest = Self { pin: digest, base, value };
    let names: Vec<_> =
      manifest.stages()?.iter().map(|s| s.name.clone()).collect();
    for stage in manifest.stages()? {
      if let Some(after) = &stage.start
        && !names.contains(after)
      {
        return Err(format!(
          "stage {} starts after unknown {after}",
          stage.name
        ));
      }
    }
    Ok(manifest)
  }

  pub fn path(&self, value: &Value) -> Result<PathBuf, Error> {
    let text = value.as_str().ok_or("manifest path is not a string")?;
    Ok(self.base.join(text))
  }

  pub fn stages(&self) -> Result<Vec<StageSpec>, Error> {
    let stages = self.value["stages"].as_array().ok_or("manifest stages")?;
    stages
      .iter()
      .map(|s| {
        let gb = |k: &str| s["memory_gb"][k].as_f64().unwrap_or(0.0);
        Ok(StageSpec {
          name: s["name"].as_str().ok_or("stage name")?.to_owned(),
          kind: s["kind"].as_str().ok_or("stage kind")?.to_owned(),
          start: s["start"].as_str().map(str::to_owned),
          memory: [gb("prepare"), gb("prepared"), gb("prove")],
          spec: s.clone(),
        })
      })
      .collect()
  }
}

/// A setup product: a file and the digests the manifest pins it by
/// (`blake3` and/or `sha256`, hex), read and checked.
pub struct Product {
  pub path: PathBuf,
  pub bytes: Vec<u8>,
}

impl Product {
  pub fn load(manifest: &Manifest, spec: &Value) -> Result<Self, Error> {
    let path = manifest.path(&spec["path"])?;
    let bytes = fs::read(&path).map_err(io(&path))?;
    Self::check(&path, &bytes, spec)?;
    Ok(Self { path, bytes })
  }

  /// Checks `bytes` against every digest in `spec`; at least one is required.
  pub fn check(path: &Path, bytes: &[u8], spec: &Value) -> Result<(), Error> {
    let mut pinned = false;
    if let Some(pin) = spec["blake3"].as_str() {
      pinned = true;
      let digest = blake3::hash(bytes).to_hex().to_string();
      if digest != pin {
        return Err(format!(
          "{}: BLAKE3 {digest} differs from the pinned {pin}",
          path.display()
        ));
      }
    }
    if let Some(pin) = spec["sha256"].as_str() {
      pinned = true;
      let digest = sha256_hex(bytes);
      if digest != pin {
        return Err(format!(
          "{}: SHA-256 {digest} differs from the pinned {pin}",
          path.display()
        ));
      }
    }
    if !pinned {
      return Err(format!("{}: the manifest pins no digest", path.display()));
    }
    Ok(())
  }
}

#[derive(Clone, Debug)]
pub struct StageSpec {
  pub name: String,
  pub kind: String,
  pub start: Option<String>,
  /// GB held while preparing, once prepared, while proving.
  pub memory: [f64; 3],
  pub spec: Value,
}

/// A counting semaphore over the process's memory, in GB.
pub struct Budget {
  total: f64,
  used: Mutex<f64>,
  changed: Condvar,
}

impl Budget {
  pub fn new(total: f64) -> Self {
    Self { total, used: Mutex::new(0.0), changed: Condvar::new() }
  }

  /// Changes a holder's reservation from `from` to `to` GB, waiting while
  /// the budget cannot cover a growth. A single reservation larger than the
  /// whole budget is granted once nothing else is held. Returns the seconds
  /// waited.
  pub fn resize(&self, from: f64, to: f64) -> f64 {
    let started = Instant::now();
    let mut used =
      self.used.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    if to > from {
      while *used - from + to > self.total && *used - from > 1e-9 {
        used = self
          .changed
          .wait(used)
          .unwrap_or_else(std::sync::PoisonError::into_inner);
      }
    }
    *used = (*used - from + to).max(0.0);
    self.changed.notify_all();
    started.elapsed().as_secs_f64()
  }
}

/// The process-wide lock over GPU sections.
pub struct Gpu {
  enabled: bool,
  lock: Mutex<()>,
}

impl Gpu {
  /// Runs `f` holding the GPU lock (when enabled); adds the seconds spent
  /// waiting for it to `waited`.
  pub fn section<T>(&self, waited: &mut f64, f: impl FnOnce() -> T) -> T {
    if !self.enabled {
      return f();
    }
    let started = Instant::now();
    let guard =
      self.lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    *waited += started.elapsed().as_secs_f64();
    let value = f();
    drop(guard);
    value
  }
}

/// What one stage hands to the next.
#[derive(Clone, Default)]
pub struct Handoff {
  pub key: Vec<u8>,
  pub claims: Vec<u8>,
  pub proof: Vec<u8>,
  /// The narrow stage's number and statement, for the terminal.
  pub stage: u32,
  pub statement: Option<[u8; 32]>,
  /// The final PLONK proof's Solidity encoding.
  pub solidity: Vec<u8>,
}

/// One stage's view of the run.
pub struct Stage<'l> {
  pub stages: &'l Stages,
  pub spec: StageSpec,
  pub dir: PathBuf,
  input: Mutex<Option<mpsc::Receiver<Handoff>>>,
  reserved: Mutex<f64>,
  pub started: f64,
  /// Seconds waited for the predecessor, the budget and the GPU lock.
  pub waits: Mutex<BTreeMap<&'static str, f64>>,
}

impl Stage<'_> {
  pub fn product(&self, field: &str) -> Result<Product, Error> {
    Product::load(&self.stages.manifest, &self.spec.spec[field])
      .map_err(|e| format!("{} {field}: {e}", self.spec.name))
  }

  pub fn path(&self, field: &str) -> Result<PathBuf, Error> {
    self.stages.manifest.path(&self.spec.spec[field])
  }

  pub fn cancelled(&self) -> Result<(), Error> {
    if self.stages.cancelled.load(Ordering::SeqCst) {
      Err("cancelled after an earlier stage failed".into())
    } else {
      Ok(())
    }
  }

  fn add_wait(&self, name: &'static str, seconds: f64) {
    *self
      .waits
      .lock()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .entry(name)
      .or_default() += seconds;
  }

  /// Moves this stage's memory reservation to its phase `phase`
  /// (0 prepare, 1 prepared, 2 prove, 3 released).
  pub fn reserve(&self, phase: usize) {
    let to = self.spec.memory.get(phase).copied().unwrap_or(0.0);
    let mut reserved =
      self.reserved.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let waited = self.stages.budget.resize(*reserved, to);
    *reserved = to;
    drop(reserved);
    self.add_wait("memory", waited);
  }

  /// Runs `f` under the GPU lock.
  pub fn gpu<T>(&self, f: impl FnOnce() -> T) -> T {
    let mut waited = 0.0;
    let value = self.stages.gpu.section(&mut waited, f);
    self.add_wait("gpu_lock", waited);
    value
  }

  /// The predecessor's output; returns the seconds waited.
  pub fn input(&self) -> Result<(Handoff, f64), Error> {
    let started = Instant::now();
    let receiver = self
      .input
      .lock()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .take()
      .ok_or("this stage has no predecessor")?;
    let handoff = receiver.recv().map_err(|_error| {
      "cancelled: the predecessor stage failed".to_string()
    })?;
    let waited = started.elapsed().as_secs_f64();
    self.add_wait("predecessor", waited);
    Ok((handoff, waited))
  }

  pub fn write(&self, name: &str, bytes: &[u8]) -> Result<(), Error> {
    let path = self.dir.join(name);
    if let Some(parent) = path.parent() {
      fs::create_dir_all(parent).map_err(io(parent))?;
    }
    fs::write(&path, bytes).map_err(io(&path))
  }

  pub fn write_json(&self, name: &str, value: &Value) -> Result<(), Error> {
    self.write(
      name,
      &serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?,
    )
  }

  /// The pinned key file named by `field` must equal `key` byte for byte.
  pub fn check_key(&self, field: &str, key: &[u8]) -> Result<(), Error> {
    let pinned = self.product(field)?;
    if pinned.bytes != key {
      return Err(format!(
        "{}: the key produced (BLAKE3 {}) differs from the pinned {}",
        self.spec.name,
        blake3::hash(key).to_hex(),
        pinned.path.display()
      ));
    }
    Ok(())
  }
}

/// Runs `f` in a rayon pool of its own, as wide as the global pool would be,
/// whose threads are named after the stage.
///
/// Stages overlap (one proves while the next prepares). In one shared pool a
/// thread blocked in `join` on its own stage's work steals and runs another
/// stage's tasks, so a stage's parallel phase can end only after unrelated
/// long tasks do. Separate pools leave the sharing of cores to the kernel's
/// scheduler, as separate processes did.
#[cfg(any(feature = "parallel", feature = "cuda"))]
fn in_stage_pool<T: Send>(
  name: &str,
  f: impl FnOnce() -> T + Send,
) -> Result<T, Error> {
  let prefix = format!("stage-{name}");
  let pool = rayon::ThreadPoolBuilder::new()
    .thread_name(move |i| format!("{prefix}-{i}"))
    .build()
    .map_err(|e| format!("stage {name} thread pool: {e}"))?;
  Ok(pool.install(f))
}

#[cfg(not(any(feature = "parallel", feature = "cuda")))]
#[allow(clippy::unnecessary_wraps)]
fn in_stage_pool<T: Send>(
  _name: &str,
  f: impl FnOnce() -> T + Send,
) -> Result<T, Error> {
  Ok(f())
}

/// Run options.
pub struct Options {
  /// `root-vk.bin`, `root-claims.bin`, `root-proof.bin`.
  pub root_dir: PathBuf,
  pub out: PathBuf,
  /// The memory budget in GB.
  pub memory_gb: f64,
  pub gpu_lock: bool,
}

pub struct Stages {
  pub manifest: Manifest,
  pub exports: exports::Exports,
  pub budget: Budget,
  pub gpu: Gpu,
  pub cancelled: AtomicBool,
  pub root: stark_verifier::compress_wrap::Input,
  pub root_bytes: [Vec<u8>; 3],
  pub out: PathBuf,
  pub checks: Checks,
}

/// The checks of `run.sh`'s `checks.json`, from the stages' reports.
#[derive(Default)]
pub struct Checks(Mutex<BTreeMap<String, bool>>);

impl Checks {
  pub fn set(&self, name: &str, ok: bool) {
    self
      .0
      .lock()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .insert(name.into(), ok);
  }
}

impl Stages {
  pub fn open(
    manifest: Manifest,
    exports: exports::Exports,
    options: &Options,
  ) -> Result<Self, Error> {
    let read = |name: &str| {
      let path = options.root_dir.join(name);
      fs::read(&path).map_err(io(&path))
    };
    let root_bytes =
      [read("root-vk.bin")?, read("root-claims.bin")?, read("root-proof.bin")?];
    let pin = manifest.value["root"]["key_blake3"]
      .as_str()
      .ok_or("manifest root.key_blake3")?;
    let root = stark_verifier::compress_wrap::Input::from_bytes(
      &root_bytes[0],
      *blake3::Hash::from_hex(pin).map_err(|e| e.to_string())?.as_bytes(),
      &root_bytes[1],
      &root_bytes[2],
    )?;
    for (name, expected) in
      [("IX_KZG_SRS", "kzg_srs"), ("IX_PARAMS_DIR", "params_dir")]
    {
      if let Some(value) = manifest.value["env"][expected].as_str() {
        let wanted = manifest.base.join(value);
        let actual = std::env::var_os(name).map(PathBuf::from);
        if actual.as_deref() != Some(wanted.as_path()) {
          return Err(format!(
            "{name} is {actual:?}; the manifest names {}",
            wanted.display()
          ));
        }
      }
    }
    Ok(Self {
      manifest,
      exports,
      budget: Budget::new(options.memory_gb),
      gpu: Gpu { enabled: options.gpu_lock, lock: Mutex::new(()) },
      cancelled: AtomicBool::new(false),
      root,
      root_bytes,
      out: options.out.clone(),
      checks: Checks::default(),
    })
  }

  /// Runs every stage; returns the final stage's output and the run summary.
  pub fn run(&self) -> Result<(Handoff, Value), Error> {
    let stages = self.manifest.stages()?;
    fs::create_dir_all(&self.out).map_err(io(&self.out))?;
    let start = unix_now();
    fs::write(self.out.join("start"), format!("{start}\n"))
      .map_err(io(&self.out))?;
    #[cfg(feature = "cuda")]
    {
      use crate::kzg::cuda;
      let srs_cache =
        std::env::var("IX_KZG_CUDA_SRS_CACHE").as_deref() == Ok("1");
      let settings = cuda::Settings { srs_cache, ..cuda::Settings::default() };
      if !cuda::configure(settings.clone()) && cuda::settings() != &settings {
        return Err(
          "KZG CUDA settings were fixed by an earlier operation".into(),
        );
      }
    }
    // Each stage's end, signalled to the stages that start after it.
    let ended: Vec<(Mutex<Option<bool>>, Condvar)> =
      stages.iter().map(|_| (Mutex::new(None), Condvar::new())).collect();
    let mut senders = vec![];
    let mut receivers = vec![None];
    for _ in 1..stages.len() {
      let (tx, rx) = mpsc::channel::<Handoff>();
      senders.push(Some(tx));
      receivers.push(Some(rx));
    }
    senders.push(None);
    let errors: Mutex<Vec<(String, String)>> = Mutex::new(vec![]);
    let reports: Mutex<BTreeMap<String, Value>> = Mutex::new(BTreeMap::new());
    let last: Mutex<Option<Handoff>> = Mutex::new(None);
    let index_of = |name: &str| stages.iter().position(|s| s.name == name);
    std::thread::scope(|scope| {
      for (i, (spec, (sender, receiver))) in
        stages.iter().zip(senders.into_iter().zip(receivers)).enumerate()
      {
        let (ended, errors, reports, last) = (&ended, &errors, &reports, &last);
        let after = spec.start.as_deref().and_then(index_of);
        let is_last = i + 1 == stages.len();
        std::thread::Builder::new()
          .name(format!("stage-{}", spec.name))
          .spawn_scoped(scope, move || {
            let signal = |ok: bool| {
              let (lock, cv) = &ended[i];
              *lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner) = Some(ok);
              cv.notify_all();
            };
            if let Some(j) = after {
              let (lock, cv) = &ended[j];
              let mut state = lock.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
              while state.is_none() {
                state = cv.wait(state).unwrap_or_else(std::sync::PoisonError::into_inner);
              }
              if *state != Some(true) {
                signal(false);
                return;
              }
            }
            let stage = Stage {
              stages: self,
              spec: spec.clone(),
              dir: self.out.join(&spec.name),
              input: Mutex::new(receiver),
              reserved: Mutex::new(0.0),
              started: unix_now(),
              waits: Mutex::new(BTreeMap::new()),
            };
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
              fs::create_dir_all(&stage.dir).map_err(io(&stage.dir))?;
              stage.reserve(0);
              let output = in_stage_pool(&spec.name, || self.run_stage(&stage))?;
              stage.reserve(3);
              output
            }))
            .unwrap_or_else(|panic| {
              Err(format!(
                "panicked: {}",
                panic
                  .downcast_ref::<&str>()
                  .copied()
                  .or_else(|| panic.downcast_ref::<String>().map(String::as_str))
                  .unwrap_or("non-string panic payload")
              ))
            });
            let end = unix_now();
            let _ = fs::write(stage.dir.join("span"), format!("{} {end}\n", stage.started));
            let (hwm, now) = rss();
            let wall = end - stage.started;
            let _ = fs::write(
              stage.dir.join("time.txt"),
              format!(
                "\tCommand being timed: \"stage {}\"\n\tElapsed (wall clock) time (h:mm:ss or m:ss): {}:{:05.2}\n\tMaximum resident set size (kbytes): {}\n",
                spec.name,
                (wall / 60.0).floor(),
                wall % 60.0,
                hwm / 1024
              ),
            );
            let waits = stage.waits.lock().unwrap_or_else(std::sync::PoisonError::into_inner).clone();
            let mut report = json!({
              "start": stage.started, "end": end, "seconds": wall,
              "process_peak_rss_bytes": hwm, "rss_bytes_at_end": now, "waits": waits,
            });
            match result {
              Ok(handoff) => {
                if let Some(tx) = sender {
                  let _ = tx.send(handoff.clone());
                }
                if is_last {
                  *last.lock().unwrap_or_else(std::sync::PoisonError::into_inner) = Some(handoff);
                }
                signal(true);
              },
              Err(error) => {
                self.cancelled.store(true, Ordering::SeqCst);
                self.exports_close();
                report["error"] = json!(error);
                eprintln!("[stages] stage {} failed: {error}", spec.name);
                errors
                  .lock()
                  .unwrap_or_else(std::sync::PoisonError::into_inner)
                  .push((spec.name.clone(), error));
                signal(false);
              },
            }
            reports
              .lock()
              .unwrap_or_else(std::sync::PoisonError::into_inner)
              .insert(spec.name.clone(), report);
          })
          .expect("spawn a stage thread");
      }
    });
    self.exports.close();
    let end = unix_now();
    fs::write(self.out.join("end"), format!("{end}\n"))
      .map_err(io(&self.out))?;
    let errors =
      errors.into_inner().unwrap_or_else(std::sync::PoisonError::into_inner);
    let checks = self
      .checks
      .0
      .lock()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .clone();
    let (hwm, _) = rss();
    let mut summary = json!({
      "format": "ix-aiur-stages-run-v1",
      "manifest_blake3": self.manifest.pin,
      "name": self.manifest.value["name"],
      "status": if errors.is_empty() { "ok" } else { "failed" },
      "errors": errors.iter().map(|(s, e)| json!({"stage": s, "error": e})).collect::<Vec<_>>(),
      "start": start, "end": end, "end_to_end_s": end - start,
      "process_peak_rss_bytes": hwm,
      "gpu_lock": self.gpu.enabled,
      "memory_budget_gb": self.budget.total,
      "exporter_ids": {
        "wide": self.exports.exporter_id(exports::Kind::Wide),
        "tiling2": self.exports.exporter_id(exports::Kind::Tiling2),
      },
      "stages": reports.into_inner().unwrap_or_else(std::sync::PoisonError::into_inner),
      "checks": checks,
    });
    let failed: Vec<_> =
      checks.iter().filter(|(_, ok)| !**ok).map(|(k, _)| k.clone()).collect();
    if errors.is_empty() && !failed.is_empty() {
      summary["status"] = json!("failed");
    }
    fs::write(
      self.out.join("checks.json"),
      serde_json::to_vec_pretty(&checks).map_err(|e| e.to_string())?,
    )
    .map_err(io(&self.out))?;
    fs::write(
      self.out.join("stages.json"),
      serde_json::to_vec_pretty(&summary).map_err(|e| e.to_string())?,
    )
    .map_err(io(&self.out))?;
    if let Some((stage, error)) = errors.first() {
      return Err(format!("stage {stage}: {error}"));
    }
    if !failed.is_empty() {
      return Err(format!("checks failed: {}", failed.join(", ")));
    }
    let last = last
      .into_inner()
      .unwrap_or_else(std::sync::PoisonError::into_inner)
      .ok_or("the manifest has no stages")?;
    Ok((last, summary))
  }

  fn exports_close(&self) {
    self.exports.close();
  }

  /// Ends the export server's loop once no stage needs an export.
  pub fn finish(&self) {
    self.exports.close();
  }

  fn run_stage(&self, stage: &Stage<'_>) -> Result<Handoff, Error> {
    match stage.spec.kind.as_str() {
      "fri" => wrap::run(stage),
      "fri-verifier" => gl::run(stage),
      "kzg-verifier" => narrow::run(stage),
      "plonk" => terminal::run(stage),
      other => Err(format!("unknown or unavailable stage kind {other:?}")),
    }
  }
}
