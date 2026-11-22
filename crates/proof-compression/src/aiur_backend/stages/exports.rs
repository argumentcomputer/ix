//! The Lean exports the compression stages prove, cached on disk.
//!
//! An export is a function of the exporter and its input only (the circuits
//! are execution-independent), so an entry is keyed by
//! `BLAKE3("ix/aiur-stages-export/v1\0" ‖ kind ‖ 0 ‖ exporter id ‖ BLAKE3(input))`.
//! The exporter id identifies the exporter code: the BLAKE3 of the exporter
//! binary, or, for exporters linked into the calling process, ids that
//! process supplies (in `ix`, the Lake trace hash of each exporter's module,
//! else the digest of its own executable). A replayed export is
//! validated exactly as a fresh one, and a wrong one changes a stage key that
//! the manifest pins, so the cache affects time only.
//!
//! An entry `ROOT/exports/<kind>/<key>/` holds `input.json`, `layout.json`,
//! `fixed.bin`, for `tiling2` also `tables.bin`, the exporter's `export.log`
//! and, written last, `complete`. Entries are built in a staging directory and
//! renamed into place.
use std::{
  collections::{HashMap, VecDeque},
  fs,
  path::{Path, PathBuf},
  process::Command,
  sync::{Condvar, Mutex},
  time::Instant,
};

/// The exporters a stage can request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
  /// `wide_export INPUT LAYOUT FIXED`
  Wide,
  /// `tiling_export2 INPUT LAYOUT FIXED TABLES`
  Tiling2,
}

impl Kind {
  pub const fn name(self) -> &'static str {
    match self {
      Self::Wide => "wide",
      Self::Tiling2 => "tiling2",
    }
  }

  pub fn parse(name: &str) -> Result<Self, String> {
    match name {
      "wide" => Ok(Self::Wide),
      "tiling2" => Ok(Self::Tiling2),
      other => Err(format!("unknown exporter kind {other:?}")),
    }
  }
}

/// An export request handed to the exporters linked into the calling
/// process: write `layout.json`, `fixed.bin` (and for `tiling2`
/// `tables.bin`) in `dir` from `dir/input.json`.
#[derive(Clone, Debug)]
pub struct Request {
  pub id: u64,
  pub kind: Kind,
  pub dir: PathBuf,
}

#[derive(Default)]
struct BrokerState {
  queue: VecDeque<Request>,
  done: HashMap<u64, Result<(), String>>,
  next: u64,
  closed: bool,
}

/// Hands export requests to a server that polls [`Broker::next`] and answers
/// with [`Broker::complete`]. The stages never call the server; the server
/// pulls, so it can run on its own runtime's threads.
#[derive(Default)]
pub struct Broker {
  state: Mutex<BrokerState>,
  changed: Condvar,
}

impl Broker {
  fn lock(&self) -> std::sync::MutexGuard<'_, BrokerState> {
    self.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
  }

  /// Queues a request and waits for its answer.
  fn request(&self, kind: Kind, dir: &Path) -> Result<(), String> {
    let mut state = self.lock();
    if state.closed {
      return Err("the export server has stopped".into());
    }
    let id = state.next;
    state.next += 1;
    state.queue.push_back(Request { id, kind, dir: dir.to_path_buf() });
    self.changed.notify_all();
    loop {
      if let Some(result) = state.done.remove(&id) {
        return result;
      }
      if state.closed {
        return Err("the export server stopped before answering".into());
      }
      state = self
        .changed
        .wait(state)
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    }
  }

  /// The next request, or `None` once the broker is closed.
  pub fn next(&self) -> Option<Request> {
    let mut state = self.lock();
    loop {
      if let Some(request) = state.queue.pop_front() {
        return Some(request);
      }
      if state.closed {
        return None;
      }
      state = self
        .changed
        .wait(state)
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    }
  }

  /// The answer to request `id`.
  pub fn complete(&self, id: u64, result: Result<(), String>) {
    let mut state = self.lock();
    state.done.insert(id, result);
    self.changed.notify_all();
  }

  /// Stops serving: pending and later requests fail, [`Self::next`]
  /// returns `None`.
  pub fn close(&self) {
    let mut state = self.lock();
    state.closed = true;
    self.changed.notify_all();
  }
}

/// Who runs an export on a cache miss.
pub enum Runner {
  /// Exporter executables, one per kind.
  Binaries { wide: PathBuf, tiling2: PathBuf },
  /// Exporters linked into the calling process, reached through a broker.
  Broker(std::sync::Arc<Broker>),
}

/// A cache entry's files.
#[derive(Clone, Debug)]
pub struct Entry {
  pub dir: PathBuf,
  pub key: String,
  pub cached: bool,
  pub seconds: f64,
}

impl Entry {
  pub fn layout(&self) -> PathBuf {
    self.dir.join("layout.json")
  }

  pub fn fixed(&self) -> PathBuf {
    self.dir.join("fixed.bin")
  }

  pub fn tables(&self) -> PathBuf {
    self.dir.join("tables.bin")
  }

  pub fn input(&self) -> PathBuf {
    self.dir.join("input.json")
  }
}

pub struct Exports {
  root: PathBuf,
  runner: Runner,
  /// Per kind: the exporter id (32 bytes).
  ids: HashMap<&'static str, [u8; 32]>,
}

fn io(path: &Path) -> impl Fn(std::io::Error) -> String + '_ {
  move |e| format!("{}: {e}", path.display())
}

impl Exports {
  /// `exporter_id` is used for every kind with [`Runner::Broker`]; with
  /// [`Runner::Binaries`] each kind's id is its binary's BLAKE3.
  pub fn new(
    root: &Path,
    runner: Runner,
    exporter_id: Option<[u8; 32]>,
  ) -> Result<Self, String> {
    let mut ids = HashMap::new();
    match &runner {
      Runner::Binaries { wide, tiling2 } => {
        for (kind, path) in [(Kind::Wide, wide), (Kind::Tiling2, tiling2)] {
          let bytes = fs::read(path).map_err(io(path))?;
          ids.insert(kind.name(), *blake3::hash(&bytes).as_bytes());
        }
      },
      Runner::Broker(_) => {
        let id = exporter_id.ok_or("linked exporters need an exporter id")?;
        for kind in [Kind::Wide, Kind::Tiling2] {
          ids.insert(kind.name(), id);
        }
      },
    }
    fs::create_dir_all(root).map_err(io(root))?;
    let exports = Self { root: root.to_path_buf(), runner, ids };
    exports.sweep();
    Ok(exports)
  }

  /// [`Self::new`] with one exporter id per kind, for exporters linked into
  /// the calling process whose code is identified separately.
  pub fn with_ids(
    root: &Path,
    runner: Runner,
    ids: [(Kind, [u8; 32]); 2],
  ) -> Result<Self, String> {
    let mut exports = Self::new(root, runner, Some(ids[0].1))?;
    for (kind, id) in ids {
      exports.ids.insert(kind.name(), id);
    }
    Ok(exports)
  }

  /// Stops the broker's server, if any.
  pub fn close(&self) {
    if let Runner::Broker(broker) = &self.runner {
      broker.close();
    }
  }

  pub fn root(&self) -> &Path {
    &self.root
  }

  pub fn exporter_id(&self, kind: Kind) -> String {
    blake3::Hash::from(self.ids[kind.name()]).to_hex().to_string()
  }

  /// Removes staging directories that no running process owns.
  fn sweep(&self) {
    let Ok(kinds) = fs::read_dir(self.root.join("exports")) else { return };
    for kind in kinds.flatten() {
      let Ok(entries) = fs::read_dir(kind.path()) else { continue };
      for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(pid) = name
          .to_str()
          .and_then(|n| n.strip_prefix(".tmp-"))
          .and_then(|n| n.split('-').next())
          .and_then(|p| p.parse::<u32>().ok())
        else {
          continue;
        };
        if !Path::new(&format!("/proc/{pid}")).exists() {
          let _ = fs::remove_dir_all(entry.path());
        }
      }
    }
  }

  pub fn key(&self, kind: Kind, input: &[u8]) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix/aiur-stages-export/v1\0");
    hasher.update(kind.name().as_bytes());
    hasher.update(&[0]);
    hasher.update(&self.ids[kind.name()]);
    hasher.update(blake3::hash(input).as_bytes());
    hasher.finalize().to_hex().to_string()
  }

  /// The export of `input` (stored as `input.json` byte for byte), from the
  /// cache or from the exporter.
  pub fn export(&self, kind: Kind, input: &[u8]) -> Result<Entry, String> {
    let started = Instant::now();
    let key = self.key(kind, input);
    let base = self.root.join("exports").join(kind.name());
    let dir = base.join(&key);
    if dir.join("complete").is_file() {
      return Ok(Entry {
        dir,
        key,
        cached: true,
        seconds: started.elapsed().as_secs_f64(),
      });
    }
    fs::create_dir_all(&base).map_err(io(&base))?;
    let staging = base.join(format!(
      ".tmp-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos())
    ));
    fs::create_dir_all(&staging).map_err(io(&staging))?;
    let result = (|| {
      fs::write(staging.join("input.json"), input).map_err(io(&staging))?;
      match &self.runner {
        Runner::Binaries { wide, tiling2 } => {
          let exe = match kind {
            Kind::Wide => wide,
            Kind::Tiling2 => tiling2,
          };
          let log = fs::File::create(staging.join("export.log"))
            .map_err(io(&staging))?;
          let mut command = Command::new(exe);
          command
            .arg(staging.join("input.json"))
            .arg(staging.join("layout.json"))
            .arg(staging.join("fixed.bin"));
          if kind == Kind::Tiling2 {
            command.arg(staging.join("tables.bin"));
          }
          let status =
            command.stderr(log).status().map_err(io(exe.as_path()))?;
          if !status.success() {
            return Err(format!(
              "{} failed ({status}); see {}",
              exe.display(),
              staging.join("export.log").display()
            ));
          }
        },
        Runner::Broker(broker) => broker.request(kind, &staging)?,
      }
      for file in ["layout.json", "fixed.bin"] {
        if !staging.join(file).is_file() {
          return Err(format!("the {} export wrote no {file}", kind.name()));
        }
      }
      fs::write(staging.join("complete"), b"").map_err(io(&staging))
    })();
    if let Err(error) = result {
      let _ = fs::remove_dir_all(&staging);
      return Err(error);
    }
    if fs::rename(&staging, &dir).is_err() {
      // Another process published the same entry first.
      let _ = fs::remove_dir_all(&staging);
      if !dir.join("complete").is_file() {
        return Err(format!("could not publish {}", dir.display()));
      }
    }
    Ok(Entry {
      dir,
      key,
      cached: false,
      seconds: started.elapsed().as_secs_f64(),
    })
  }

  /// The artifact's bytes at `ROOT/artifacts/<digest>.ixa`, for exporter
  /// inputs that name the artifact by path.
  pub fn artifact(
    &self,
    bytes: &[u8],
    digest: &str,
  ) -> Result<PathBuf, String> {
    let directory = self.root.join("artifacts");
    let path = directory.join(format!("{digest}.ixa"));
    if fs::read(&path).is_ok_and(|stored| stored == bytes) {
      return std::path::absolute(&path).map_err(|e| e.to_string());
    }
    fs::create_dir_all(&directory).map_err(io(&directory))?;
    let staging = directory.join(format!(".{digest}.{}", std::process::id()));
    fs::write(&staging, bytes)
      .and_then(|()| fs::rename(&staging, &path))
      .map_err(io(&path))?;
    std::path::absolute(&path).map_err(|e| e.to_string())
  }
}

/// The wrapper's `wide_export` source over the stages' export cache.
pub struct WideSource<'e>(pub &'e Exports);

impl stark_verifier::compress_wrap::WideExporter for WideSource<'_> {
  fn artifact(&self, bytes: &[u8], digest: &str) -> Result<PathBuf, String> {
    self.0.artifact(bytes, digest)
  }

  fn export(
    &self,
    input: &serde_json::Value,
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    let input = serde_json::to_vec_pretty(input).map_err(|e| e.to_string())?;
    let entry = self.0.export(Kind::Wide, &input)?;
    let layout = entry.layout();
    let fixed = entry.fixed();
    Ok((
      fs::read(&layout).map_err(io(&layout))?,
      fs::read(&fixed).map_err(io(&fixed))?,
    ))
  }
}
