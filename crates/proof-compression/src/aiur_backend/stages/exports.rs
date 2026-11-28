//! The Lean exports the compression stages prove, cached on disk.
//!
//! An export is a function of the exporter and its input only (the circuits
//! are execution-independent), so an entry is keyed by
//! `BLAKE3("ix/aiur-stages-export/v1\0" ‖ kind ‖ 0 ‖ exporter id ‖ BLAKE3(input))`.
//! The exporter id identifies the exporter code: the BLAKE3 of the exporter
//! binary, or, for exporters linked into the calling process, ids that
//! process supplies (in `ix`, the Lake trace hash of each exporter's module,
//! else the digest of its own executable).
//!
//! An entry `ROOT/exports/<kind>/<key>/` holds `input.json`, `layout.json`,
//! `fixed.bin`, for `tiling2` also `tables.bin`, the exporter's `export.log`
//! and, written last, `complete` — a JSON manifest recording BLAKE3 digests of
//! `input.json`, the pinned artifact (when referenced), `layout.json`,
//! `fixed.bin`, and `tables.bin`. Cache hits verify every recorded digest
//! before adoption and refuse empty, legacy, or tampered markers. Entries are
//! built in a staging directory and renamed into place.
use serde::{Deserialize, Serialize};
use std::{
  collections::{HashMap, VecDeque},
  fs,
  path::{Path, PathBuf},
  process::Command,
  sync::{Condvar, Mutex},
  time::Instant,
};

const COMPLETE_FORMAT: &str = "ix-aiur-export-complete-v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompleteMarker {
  format: String,
  kind: String,
  key: String,
  exporter_id: String,
  input_blake3: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  artifact_blake3: Option<String>,
  layout_blake3: String,
  fixed_blake3: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  tables_blake3: Option<String>,
}

fn blake3_file(path: &Path) -> Result<String, String> {
  let meta = fs::metadata(path).map_err(io(path))?;
  let mut hasher = blake3::Hasher::new();
  if meta.len() >= 1 << 20 {
    if hasher.update_mmap_rayon(path).is_err() {
      hasher = blake3::Hasher::new();
      let mut file = fs::File::open(path).map_err(io(path))?;
      std::io::copy(&mut file, &mut hasher).map_err(io(path))?;
    }
  } else {
    let mut file = fs::File::open(path).map_err(io(path))?;
    std::io::copy(&mut file, &mut hasher).map_err(io(path))?;
  }
  Ok(hasher.finalize().to_hex().to_string())
}

fn check_input_artifact(
  input: &[u8],
  base_dir: &Path,
) -> Result<Option<String>, String> {
  let Ok(value) = serde_json::from_slice::<serde_json::Value>(input) else {
    return Ok(None);
  };
  let Some(obj) = value.as_object() else {
    return Ok(None);
  };
  let artifact_path_str = obj.get("artifact").and_then(|v| v.as_str());
  let artifact_pin_str = obj.get("artifact_blake3").and_then(|v| v.as_str());
  match (artifact_path_str, artifact_pin_str) {
    (Some(_), None) => Err(
      "export input references an artifact without an artifact_blake3 pin"
        .into(),
    ),
    (_, Some(pin)) => {
      let normalized = pin.to_ascii_lowercase();
      if normalized.len() != 64
        || !normalized.bytes().all(|b| b.is_ascii_hexdigit())
      {
        return Err(format!("invalid export artifact_blake3 pin: {pin}"));
      }
      if let Some(rel) = artifact_path_str {
        let p = Path::new(rel);
        let resolved =
          if p.is_absolute() { p.to_path_buf() } else { base_dir.join(p) };
        let actual = blake3_file(&resolved)?;
        if actual != normalized {
          return Err(format!(
            "export artifact {} BLAKE3 {actual} differs from pinned {normalized}",
            resolved.display()
          ));
        }
      }
      Ok(Some(normalized))
    },
    (None, None) => Ok(None),
  }
}

/// The prime field passed to `wide_export` and `tiling_export2`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Field {
  #[default]
  Bn254,
  Bls12381,
  Goldilocks,
}

impl Field {
  pub const fn name(self) -> &'static str {
    match self {
      Self::Bn254 => "bn254",
      Self::Bls12381 => "bls12-381",
      Self::Goldilocks => "goldilocks",
    }
  }

  pub fn parse(name: &str) -> Result<Self, String> {
    match name {
      "bn254" => Ok(Self::Bn254),
      "bls12-381" | "bls12_381" | "bls12381" => Ok(Self::Bls12381),
      "goldilocks" => Ok(Self::Goldilocks),
      other => Err(format!(
        "unknown exporter field {other:?}; expected bn254, bls12-381, or goldilocks"
      )),
    }
  }
}

/// Optional manifest `"field"` selector for KZG/PLONK stages (`"bn254"` default
/// or `"bls12-381"`).
pub(super) fn parse_stage_field(
  spec: &serde_json::Value,
) -> Result<Field, String> {
  match &spec["field"] {
    serde_json::Value::Null => Ok(Field::Bn254),
    serde_json::Value::String(name) => match Field::parse(name)? {
      Field::Bn254 => Ok(Field::Bn254),
      Field::Bls12381 => Ok(Field::Bls12381),
      Field::Goldilocks => {
        Err("stage field must be \"bn254\" or \"bls12-381\"".into())
      },
    },
    _ => {
      Err("manifest field must be a string (\"bn254\" or \"bls12-381\")".into())
    },
  }
}

/// Optional manifest `"entry"` override (for plugging in `ixcc-aiur`-compiled
/// circuits).
pub(super) fn parse_optional_entry(
  spec: &serde_json::Value,
) -> Result<Option<&str>, String> {
  match &spec["entry"] {
    serde_json::Value::Null => Ok(None),
    serde_json::Value::String(s) if !s.is_empty() => Ok(Some(s.as_str())),
    _ => Err("manifest entry must be a non-empty string".into()),
  }
}

fn input_field(input: &[u8]) -> Result<Option<Field>, String> {
  let Ok(value) = serde_json::from_slice::<serde_json::Value>(input) else {
    return Ok(None);
  };
  let Some(object) = value.as_object() else {
    return Ok(None);
  };
  match object.get("field") {
    None | Some(serde_json::Value::Null) => Ok(None),
    Some(serde_json::Value::String(name)) => Field::parse(name).map(Some),
    Some(_) => Err("exporter input.json \"field\" must be a string".into()),
  }
}

fn resolve_export_field(
  explicit: Option<Field>,
  input: &[u8],
) -> Result<(Option<Field>, Option<Field>), String> {
  let json_field = input_field(input)?;
  if let (Some(cli), Some(in_json)) = (explicit, json_field)
    && cli != in_json
  {
    return Err(format!(
      "exporter field {} conflicts with input.json field {}",
      cli.name(),
      in_json.name()
    ));
  }
  Ok((explicit.or(json_field), json_field))
}

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

  /// Cache key for `export_with_field`. Identical to [`Self::key`] when
  /// `field` is `None`, matches `"field"` inside `input`, or defaults to BN254.
  pub fn key_with_field(
    &self,
    kind: Kind,
    field: Option<Field>,
    input: &[u8],
  ) -> Result<String, String> {
    let (effective, json_field) = resolve_export_field(field, input)?;
    match (effective, json_field) {
      (Some(f), None) if f != Field::Bn254 => {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"ix/aiur-stages-export/v1\0");
        hasher.update(kind.name().as_bytes());
        hasher.update(&[0]);
        hasher.update(&self.ids[kind.name()]);
        hasher.update(blake3::hash(input).as_bytes());
        hasher.update(b"\0field=");
        hasher.update(f.name().as_bytes());
        Ok(hasher.finalize().to_hex().to_string())
      },
      _ => Ok(self.key(kind, input)),
    }
  }

  fn staged_input_bytes(
    &self,
    effective: Option<Field>,
    json_field: Option<Field>,
    input: &[u8],
  ) -> Result<Vec<u8>, String> {
    match (&self.runner, effective, json_field) {
      (Runner::Broker(_), Some(f), None) if f != Field::Bn254 => {
        let mut value: serde_json::Value = serde_json::from_slice(input)
          .map_err(|e| format!("exporter input.json: {e}"))?;
        if let Some(obj) = value.as_object_mut() {
          obj.insert("field".into(), serde_json::json!(f.name()));
        }
        serde_json::to_vec(&value).map_err(|e| e.to_string())
      },
      _ => Ok(input.to_vec()),
    }
  }

  fn build_complete_marker(
    &self,
    kind: Kind,
    key: &str,
    staged_input: &[u8],
    dir: &Path,
  ) -> Result<CompleteMarker, String> {
    for file in ["input.json", "layout.json", "fixed.bin"] {
      if !dir.join(file).is_file() {
        return Err(format!("the {} export wrote no {file}", kind.name()));
      }
    }
    if kind == Kind::Tiling2 && !dir.join("tables.bin").is_file() {
      return Err("the tiling2 export wrote no tables.bin".into());
    }
    let input_blake3 = blake3::hash(staged_input).to_hex().to_string();
    let stored_input = blake3_file(&dir.join("input.json"))?;
    if stored_input != input_blake3 {
      return Err(format!(
        "export staging input.json BLAKE3 {stored_input} differs from request {input_blake3}"
      ));
    }
    let artifact_blake3 = check_input_artifact(staged_input, dir)?;
    let layout_blake3 = blake3_file(&dir.join("layout.json"))?;
    let fixed_blake3 = blake3_file(&dir.join("fixed.bin"))?;
    let tables_blake3 = if kind == Kind::Tiling2 {
      Some(blake3_file(&dir.join("tables.bin"))?)
    } else {
      None
    };
    Ok(CompleteMarker {
      format: COMPLETE_FORMAT.to_owned(),
      kind: kind.name().to_owned(),
      key: key.to_owned(),
      exporter_id: self.exporter_id(kind),
      input_blake3,
      artifact_blake3,
      layout_blake3,
      fixed_blake3,
      tables_blake3,
    })
  }

  fn verify_complete_entry(
    &self,
    kind: Kind,
    key: &str,
    staged_input: &[u8],
    dir: &Path,
  ) -> Result<CompleteMarker, String> {
    let complete_path = dir.join("complete");
    let raw = fs::read(&complete_path).map_err(io(&complete_path))?;
    if raw.is_empty() {
      return Err(format!(
        "{}: unauthenticated empty complete marker; refusing stale cache entry",
        complete_path.display()
      ));
    }
    let marker: CompleteMarker = serde_json::from_slice(&raw).map_err(|e| {
      format!(
        "{}: malformed complete marker ({e}); refusing cache entry",
        complete_path.display()
      )
    })?;
    if marker.format != COMPLETE_FORMAT {
      return Err(format!(
        "{}: unsupported complete marker format {:?}",
        complete_path.display(),
        marker.format
      ));
    }
    if marker.kind != kind.name()
      || marker.key != key
      || marker.exporter_id != self.exporter_id(kind)
    {
      return Err(format!(
        "{}: complete marker metadata differs from requested export",
        complete_path.display()
      ));
    }
    let expected_input = blake3::hash(staged_input).to_hex().to_string();
    if marker.input_blake3 != expected_input {
      return Err(format!(
        "{}: complete marker input_blake3 differs from request",
        complete_path.display()
      ));
    }
    let expected_artifact = check_input_artifact(staged_input, dir)?;
    if marker.artifact_blake3 != expected_artifact {
      return Err(format!(
        "{}: complete marker artifact_blake3 differs from request",
        complete_path.display()
      ));
    }
    let check_file = |name: &str, expected: &str| -> Result<(), String> {
      let path = dir.join(name);
      let actual = blake3_file(&path)?;
      if actual != expected {
        return Err(format!(
          "{}: BLAKE3 {actual} differs from complete marker {expected}",
          path.display()
        ));
      }
      Ok(())
    };
    check_file("input.json", &marker.input_blake3)?;
    check_file("layout.json", &marker.layout_blake3)?;
    check_file("fixed.bin", &marker.fixed_blake3)?;
    match (kind, &marker.tables_blake3) {
      (Kind::Tiling2, Some(expected)) => check_file("tables.bin", expected)?,
      (Kind::Tiling2, None) => {
        return Err(format!(
          "{}: tiling2 complete marker is missing tables_blake3",
          complete_path.display()
        ));
      },
      (Kind::Wide, None) => {},
      (Kind::Wide, Some(_)) => {
        return Err(format!(
          "{}: unexpected tables_blake3 in wide complete marker",
          complete_path.display()
        ));
      },
    }
    Ok(marker)
  }

  fn run_in_staging(
    &self,
    kind: Kind,
    key: &str,
    effective: Option<Field>,
    staged_input: &[u8],
    base: &Path,
  ) -> Result<(PathBuf, CompleteMarker), String> {
    fs::create_dir_all(base).map_err(io(base))?;
    let staging = base.join(format!(
      ".tmp-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos())
    ));
    fs::create_dir_all(&staging).map_err(io(&staging))?;
    let result = (|| -> Result<CompleteMarker, String> {
      fs::write(staging.join("input.json"), staged_input)
        .map_err(io(&staging))?;
      let _ = check_input_artifact(staged_input, &staging)?;
      match &self.runner {
        Runner::Binaries { wide, tiling2 } => {
          let exe = match kind {
            Kind::Wide => wide,
            Kind::Tiling2 => tiling2,
          };
          let log = fs::File::create(staging.join("export.log"))
            .map_err(io(&staging))?;
          let mut command = Command::new(exe);
          if let Some(f) = effective {
            command.arg("--field").arg(f.name());
          }
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
      let marker =
        self.build_complete_marker(kind, key, staged_input, &staging)?;
      let marker_bytes =
        serde_json::to_vec_pretty(&marker).map_err(|e| e.to_string())?;
      fs::write(staging.join("complete"), &marker_bytes)
        .map_err(io(&staging))?;
      Ok(marker)
    })();
    match result {
      Ok(marker) => Ok((staging, marker)),
      Err(error) => {
        let _ = fs::remove_dir_all(&staging);
        Err(error)
      },
    }
  }

  /// The export of `input` (stored as `input.json` byte for byte), from the
  /// authenticated cache or from the exporter. Forwards `--field <name>` when
  /// `input` specifies `"field"`.
  ///
  /// Any existing cache entry whose `complete` marker is empty, malformed, or
  /// whose `input.json`, `layout.json`, `fixed.bin`, `tables.bin`, or pinned
  /// artifact digest differs is refused fail-closed.
  pub fn export(&self, kind: Kind, input: &[u8]) -> Result<Entry, String> {
    self.export_with_field(kind, None, input)
  }

  /// Like [`Self::export`], with an optional explicit [`Field`] forwarded via
  /// `--field <name>` to `wide_export` and `tiling_export2`.
  pub fn export_with_field(
    &self,
    kind: Kind,
    field: Option<Field>,
    input: &[u8],
  ) -> Result<Entry, String> {
    let started = Instant::now();
    let (effective, json_field) = resolve_export_field(field, input)?;
    let key = self.key_with_field(kind, field, input)?;
    let staged_input = self.staged_input_bytes(effective, json_field, input)?;
    let base = self.root.join("exports").join(kind.name());
    let dir = base.join(&key);
    if dir.exists() {
      self.verify_complete_entry(kind, &key, &staged_input, &dir)?;
      return Ok(Entry {
        dir,
        key,
        cached: true,
        seconds: started.elapsed().as_secs_f64(),
      });
    }
    let (staging, _marker) =
      self.run_in_staging(kind, &key, effective, &staged_input, &base)?;
    if fs::rename(&staging, &dir).is_err() {
      // Another process published the same entry first; verify its marker
      // before adopting it.
      let _ = fs::remove_dir_all(&staging);
      self.verify_complete_entry(kind, &key, &staged_input, &dir)?;
    }
    Ok(Entry {
      dir,
      key,
      cached: false,
      seconds: started.elapsed().as_secs_f64(),
    })
  }

  /// Clean-state export bypassing cache reuse: always runs the exporter into
  /// staging and, if a cached entry already exists, verifies that every digest
  /// matches the fresh export before returning.
  pub fn export_fresh(
    &self,
    kind: Kind,
    input: &[u8],
  ) -> Result<Entry, String> {
    self.export_fresh_with_field(kind, None, input)
  }

  /// Clean-state variant of [`Self::export_with_field`].
  pub fn export_fresh_with_field(
    &self,
    kind: Kind,
    field: Option<Field>,
    input: &[u8],
  ) -> Result<Entry, String> {
    let started = Instant::now();
    let (effective, json_field) = resolve_export_field(field, input)?;
    let key = self.key_with_field(kind, field, input)?;
    let staged_input = self.staged_input_bytes(effective, json_field, input)?;
    let base = self.root.join("exports").join(kind.name());
    let dir = base.join(&key);
    let (staging, fresh_marker) =
      self.run_in_staging(kind, &key, effective, &staged_input, &base)?;
    if dir.exists() {
      let cached_marker = self
        .verify_complete_entry(kind, &key, &staged_input, &dir)
        .inspect_err(|_| {
          let _ = fs::remove_dir_all(&staging);
        })?;
      let _ = fs::remove_dir_all(&staging);
      if cached_marker != fresh_marker {
        return Err(format!(
          "{}: cached export differs from clean-state re-export",
          dir.display()
        ));
      }
      return Ok(Entry {
        dir,
        key,
        cached: false,
        seconds: started.elapsed().as_secs_f64(),
      });
    }
    if fs::rename(&staging, &dir).is_err() {
      let _ = fs::remove_dir_all(&staging);
      let published =
        self.verify_complete_entry(kind, &key, &staged_input, &dir)?;
      if published != fresh_marker {
        return Err(format!(
          "{}: concurrently published export differs from clean-state export",
          dir.display()
        ));
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
    let actual = blake3::hash(bytes).to_hex().to_string();
    if actual != digest.to_ascii_lowercase() {
      return Err(format!(
        "export artifact bytes BLAKE3 {actual} differ from declared digest {digest}"
      ));
    }
    let directory = self.root.join("artifacts");
    let path = directory.join(format!("{actual}.ixa"));
    if fs::read(&path).is_ok_and(|stored| stored == bytes) {
      return std::path::absolute(&path).map_err(|e| e.to_string());
    }
    fs::create_dir_all(&directory).map_err(io(&directory))?;
    let staging = directory.join(format!(".{actual}.{}", std::process::id()));
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

#[cfg(test)]
mod tests {
  use super::*;
  use serde_json::json;
  use std::os::unix::fs::PermissionsExt;

  fn temp_dir(label: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
      "ix-exports-test-{label}-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos())
    ));
    fs::create_dir_all(&dir).unwrap();
    dir
  }

  fn write_mock_exporter(path: &Path) {
    let script = "#!/bin/sh\nset -e\n\
      FIELD=\"\"\n\
      if [ \"$1\" = \"--field\" ]; then FIELD=\"$2\"; shift 2; fi\n\
      INPUT=\"$1\"; LAYOUT=\"$2\"; FIXED=\"$3\"; TABLES=\"$4\"\n\
      printf '{\"field\":\"%s\"}' \"$FIELD\" > \"$LAYOUT\"\n\
      printf 'fixed' > \"$FIXED\"\n\
      if [ -n \"$TABLES\" ]; then printf 'tables' > \"$TABLES\"; fi\n";
    fs::write(path, script).unwrap();
    fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
  }

  #[test]
  fn cache_key_compatibility_and_field_forwarding() {
    let root = temp_dir("field");
    let wide = root.join("mock_wide.sh");
    let tiling2 = root.join("mock_tiling2.sh");
    write_mock_exporter(&wide);
    write_mock_exporter(&tiling2);
    let exports = Exports::new(
      &root.join("cache"),
      Runner::Binaries { wide, tiling2 },
      None,
    )
    .unwrap();

    // BN254 cache key is 100% backward-compatible whether field is omitted or
    // explicit.
    let bn_no_field = br#"{"format":"ix-tiling-v2-input-2","width":8}"#;
    let legacy_key = exports.key(Kind::Tiling2, bn_no_field);
    assert_eq!(
      exports.key_with_field(Kind::Tiling2, None, bn_no_field).unwrap(),
      legacy_key
    );
    assert_eq!(
      exports
        .key_with_field(Kind::Tiling2, Some(Field::Bn254), bn_no_field)
        .unwrap(),
      legacy_key
    );

    // Explicit BLS12-381 gets a distinct key from BN254.
    let bls_key = exports
      .key_with_field(Kind::Tiling2, Some(Field::Bls12381), bn_no_field)
      .unwrap();
    assert_ne!(bls_key, legacy_key);

    // Input JSON with `"field": "bls12-381"` forwards `--field bls12-381`.
    let wide_bls = br#"{"format":"ix-wide-input-1","field":"bls12-381"}"#;
    let entry = exports.export(Kind::Wide, wide_bls).unwrap();
    assert!(!entry.cached);
    let layout: serde_json::Value =
      serde_json::from_slice(&fs::read(entry.layout()).unwrap()).unwrap();
    assert_eq!(layout["field"], "bls12-381");
    let cached = exports.export(Kind::Wide, wide_bls).unwrap();
    assert!(cached.cached);
    assert_eq!(cached.key, entry.key);

    // Explicit `--field bls12-381` forwarded to tiling_export2.
    let t_entry = exports
      .export_with_field(Kind::Tiling2, Some(Field::Bls12381), bn_no_field)
      .unwrap();
    let t_layout: serde_json::Value =
      serde_json::from_slice(&fs::read(t_entry.layout()).unwrap()).unwrap();
    assert_eq!(t_layout["field"], "bls12-381");

    // Explicit `--field bn254` forwarded to tiling_export2.
    let bn_entry = exports
      .export_with_field(Kind::Tiling2, Some(Field::Bn254), bn_no_field)
      .unwrap();
    let bn_layout: serde_json::Value =
      serde_json::from_slice(&fs::read(bn_entry.layout()).unwrap()).unwrap();
    assert_eq!(bn_layout["field"], "bn254");
    assert_eq!(bn_entry.key, legacy_key);

    // Conflicting CLI and input.json field fails closed.
    assert!(
      exports
        .export_with_field(Kind::Wide, Some(Field::Bn254), wide_bls)
        .is_err()
    );
    // Unknown field in input.json fails closed.
    let bad_field = br#"{"format":"ix-wide-input-1","field":"secp256k1"}"#;
    assert!(exports.export(Kind::Wide, bad_field).is_err());

    let _ = fs::remove_dir_all(&root);
  }

  #[test]
  fn manifest_field_and_entry_parsing() {
    assert_eq!(parse_stage_field(&json!({})).unwrap(), Field::Bn254);
    assert_eq!(
      parse_stage_field(&json!({"field": "bn254"})).unwrap(),
      Field::Bn254
    );
    assert_eq!(
      parse_stage_field(&json!({"field": "bls12-381"})).unwrap(),
      Field::Bls12381
    );
    assert!(parse_stage_field(&json!({"field": "goldilocks"})).is_err());
    assert!(parse_stage_field(&json!({"field": 123})).is_err());

    assert_eq!(parse_optional_entry(&json!({})).unwrap(), None);
    assert_eq!(
      parse_optional_entry(&json!({"entry": "Prog::main"})).unwrap(),
      Some("Prog::main")
    );
    assert!(parse_optional_entry(&json!({"entry": ""})).is_err());
    assert!(parse_optional_entry(&json!({"entry": 42})).is_err());
  }

  fn spawn_mock_broker(
    broker: std::sync::Arc<Broker>,
    fixed_payload: &'static [u8],
    tables_payload: &'static [u8],
  ) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
      while let Some(req) = broker.next() {
        let res = (|| -> Result<(), String> {
          fs::write(req.dir.join("layout.json"), b"{\"ok\":true}")
            .map_err(|e| e.to_string())?;
          fs::write(req.dir.join("fixed.bin"), fixed_payload)
            .map_err(|e| e.to_string())?;
          if req.kind == Kind::Tiling2 {
            fs::write(req.dir.join("tables.bin"), tables_payload)
              .map_err(|e| e.to_string())?;
          }
          Ok(())
        })();
        broker.complete(req.id, res);
      }
    })
  }

  #[test]
  fn complete_marker_authenticates_all_outputs_and_rejects_stale_or_tampered_cache()
   {
    let tmp = temp_dir("hardening");
    let broker = std::sync::Arc::new(Broker::default());
    let server = spawn_mock_broker(
      std::sync::Arc::clone(&broker),
      b"fixed-matrix-bytes",
      b"compact-tables-bytes",
    );
    let exports = Exports::new(
      &tmp,
      Runner::Broker(std::sync::Arc::clone(&broker)),
      Some([0x33; 32]),
    )
    .unwrap();

    // Artifact pinned in input JSON must match its BLAKE3.
    let artifact_bytes = b"sample-ixa-artifact";
    let artifact_hex = blake3::hash(artifact_bytes).to_hex().to_string();
    let artifact_path =
      exports.artifact(artifact_bytes, &artifact_hex).unwrap();
    assert!(exports.artifact(artifact_bytes, &"00".repeat(32)).is_err());

    let input = serde_json::to_vec(&json!({
      "format": "ix-tiling-v2-input-2",
      "artifact": artifact_path,
      "artifact_blake3": artifact_hex,
    }))
    .unwrap();

    // Input referencing an artifact without artifact_blake3 must fail closed.
    let unpinned_input = serde_json::to_vec(&json!({
      "format": "ix-tiling-v2-input-2",
      "artifact": artifact_path,
    }))
    .unwrap();
    assert!(exports.export(Kind::Tiling2, &unpinned_input).is_err());

    // First export succeeds (cache miss) and writes an authenticated complete marker.
    let entry = exports.export(Kind::Tiling2, &input).unwrap();
    assert!(!entry.cached);
    // Second export is an authenticated cache hit.
    let hit = exports.export(Kind::Tiling2, &input).unwrap();
    assert!(hit.cached);
    assert_eq!(hit.dir, entry.dir);

    // Clean-state re-export agrees with the valid cache entry.
    let fresh = exports.export_fresh(Kind::Tiling2, &input).unwrap();
    assert!(!fresh.cached);

    // Tampering with fixed.bin must cause cache hit to fail closed.
    let orig_fixed = fs::read(entry.fixed()).unwrap();
    fs::write(entry.fixed(), b"tampered-fixed-bytes").unwrap();
    assert!(exports.export(Kind::Tiling2, &input).is_err());
    fs::write(entry.fixed(), &orig_fixed).unwrap();
    assert!(exports.export(Kind::Tiling2, &input).unwrap().cached);

    // Tampering with tables.bin must cause cache hit to fail closed.
    let orig_tables = fs::read(entry.tables()).unwrap();
    fs::write(entry.tables(), b"tampered-tables-bytes").unwrap();
    assert!(exports.export(Kind::Tiling2, &input).is_err());
    fs::write(entry.tables(), &orig_tables).unwrap();

    // Tampering with layout.json must cause cache hit to fail closed.
    let orig_layout = fs::read(entry.layout()).unwrap();
    fs::write(entry.layout(), b"{\"ok\":false}").unwrap();
    assert!(exports.export(Kind::Tiling2, &input).is_err());
    fs::write(entry.layout(), &orig_layout).unwrap();

    // Replacing complete with a legacy 0-byte marker must be refused.
    let orig_complete = fs::read(entry.dir.join("complete")).unwrap();
    fs::write(entry.dir.join("complete"), b"").unwrap();
    assert!(exports.export(Kind::Tiling2, &input).is_err());

    // Tampering with the complete marker to match tampered fixed.bin is caught
    // by export_fresh (clean-state reproduction).
    fs::write(entry.fixed(), b"self-consistent-tampered-fixed").unwrap();
    let mut forged_marker: CompleteMarker =
      serde_json::from_slice(&orig_complete).unwrap();
    forged_marker.fixed_blake3 =
      blake3::hash(b"self-consistent-tampered-fixed").to_hex().to_string();
    fs::write(
      entry.dir.join("complete"),
      serde_json::to_vec(&forged_marker).unwrap(),
    )
    .unwrap();
    assert!(exports.export_fresh(Kind::Tiling2, &input).is_err());

    // Restore valid marker and verify tampering with the referenced artifact fails.
    fs::write(entry.fixed(), &orig_fixed).unwrap();
    fs::write(entry.dir.join("complete"), &orig_complete).unwrap();
    fs::write(&artifact_path, b"corrupted-artifact").unwrap();
    assert!(exports.export(Kind::Tiling2, &input).is_err());

    exports.close();
    server.join().unwrap();
    let _ = fs::remove_dir_all(&tmp);
  }
}
