//! The compression ladder (`ix_proof_compression::aiur_backend::ladder`) in
//! the `ix` process, with the Lean exporters linked into it.
//!
//! The ladder never calls into Lean: Lean serves export requests by polling
//! `rs_ladder_next_export` from its own task and answering with
//! `rs_ladder_complete_export`, while `rs_ladder_run` blocks the calling
//! thread until every stage has ended. All Lean arguments are borrowed and
//! copied before the call returns.
use ix_proof_compression::aiur_backend::ladder::{
  Ladder, Manifest, Options,
  exports::{Broker, Exports, Kind, Runner},
};
use lean_ffi::object::{
  ExternalClass, LeanBorrowed, LeanExternal, LeanIOResult, LeanOwned,
  LeanString,
};
use serde_json::Value;
use std::{
  path::{Path, PathBuf},
  sync::{Arc, LazyLock},
};

pub struct LadderHandle {
  ladder: Ladder,
  broker: Arc<Broker>,
}

static LADDER_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<LadderHandle>);

fn io<T: Into<LeanOwned>>(
  f: impl FnOnce() -> Result<T, String>,
) -> LeanIOResult<LeanOwned> {
  match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
    Ok(Ok(value)) => LeanIOResult::ok(value),
    Ok(Err(error)) => LeanIOResult::error_string(&error),
    Err(_) => LeanIOResult::error_string("the compression ladder panicked"),
  }
}

/// BLAKE3 of this process's executable: the identity of the exporters
/// linked into it.
fn own_executable_id() -> Result<[u8; 32], String> {
  let path = std::fs::read_link("/proc/self/exe").map_err(|e| e.to_string())?;
  let mut hasher = blake3::Hasher::new();
  hasher
    .update_mmap_rayon(&path)
    .map_err(|e| format!("{}: {e}", path.display()))?;
  Ok(*hasher.finalize().as_bytes())
}

/// Per-kind exporter ids from `options.exporter_trace`: the Lake trace hash
/// (`depHash`) of each linked exporter's module, which `ix` records when it
/// is compiled. `None` unless both kinds have one.
fn trace_ids(options: &Value) -> Option<[(Kind, [u8; 32]); 2]> {
  let id = |kind: Kind| {
    let hash = options["exporter_trace"][kind.name()].as_str()?;
    if hash.is_empty() {
      return None;
    }
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix/aiur-ladder-exporter/lake-trace/v1\0");
    hasher.update(kind.name().as_bytes());
    hasher.update(&[0]);
    hasher.update(hash.as_bytes());
    Some((kind, *hasher.finalize().as_bytes()))
  };
  Some([id(Kind::Wide)?, id(Kind::Tiling2)?])
}

fn open(
  manifest_path: &str,
  pin: &str,
  options: &str,
) -> Result<LadderHandle, String> {
  let _ = tracing_subscriber::fmt()
    .with_env_filter(
      tracing_subscriber::EnvFilter::try_from_default_env()
        .unwrap_or_else(|_error| "info".into()),
    )
    .with_writer(std::io::stderr)
    .try_init();
  let options: Value =
    serde_json::from_str(options).map_err(|e| e.to_string())?;
  let manifest_path =
    std::path::absolute(manifest_path).map_err(|e| e.to_string())?;
  let bytes = std::fs::read(&manifest_path)
    .map_err(|e| format!("{}: {e}", manifest_path.display()))?;
  let base = manifest_path.parent().unwrap_or(Path::new(".")).to_path_buf();
  let manifest = Manifest::new(&bytes, pin, &base)?;
  let cache = match options["cache"].as_str() {
    Some(dir) => PathBuf::from(dir),
    None => manifest.path(&manifest.value["cache"])?,
  };
  let broker = Arc::new(Broker::default());
  let runner = Runner::Broker(Arc::clone(&broker));
  let exports = match (options["exporter_id"].as_str(), trace_ids(&options)) {
    (Some(hex), _) if hex != "self" => Exports::new(
      &cache,
      runner,
      Some(*blake3::Hash::from_hex(hex).map_err(|e| e.to_string())?.as_bytes()),
    )?,
    (None, Some(ids)) => Exports::with_ids(&cache, runner, ids)?,
    _ => {
      if options["exporter_id"].is_null() {
        eprintln!(
          "[ladder] no Lake trace for the linked exporters; the export cache \
           is keyed by this executable's digest"
        );
      }
      Exports::new(&cache, runner, Some(own_executable_id()?))?
    },
  };
  let memory_gb = options["memory_gb"]
    .as_f64()
    .or_else(|| manifest.value["memory_gb"].as_f64())
    .ok_or("no memory budget (options or manifest memory_gb)")?;
  let options = Options {
    root_dir: PathBuf::from(options["root_dir"].as_str().ok_or("root_dir")?),
    out: PathBuf::from(options["out"].as_str().ok_or("out")?),
    memory_gb,
    gpu_lock: options["gpu_lock"].as_bool().unwrap_or(true),
  };
  let ladder = Ladder::open(manifest, exports, &options)?;
  Ok(LadderHandle { ladder, broker })
}

/// `Ladder.open (manifest pin options : @& String) : IO Ladder`
#[unsafe(no_mangle)]
extern "C" fn rs_ladder_open(
  manifest: LeanString<LeanBorrowed<'_>>,
  pin: LeanString<LeanBorrowed<'_>>,
  options: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let (manifest, pin, options) =
    (manifest.to_string(), pin.to_string(), options.to_string());
  io(|| {
    let handle = open(&manifest, &pin, &options)?;
    Ok(LeanExternal::alloc(&LADDER_CLASS, handle))
  })
}

/// `Ladder.nextExport (l : @& Ladder) : IO String`: blocks until a stage
/// needs an export; `id\tkind\tdir`, or empty once the ladder has ended.
#[unsafe(no_mangle)]
extern "C" fn rs_ladder_next_export(
  handle: LeanExternal<LadderHandle, LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let broker = Arc::clone(&handle.get().broker);
  io(move || {
    Ok(LeanString::new(&match broker.next() {
      None => String::new(),
      Some(request) => format!(
        "{}\t{}\t{}",
        request.id,
        request.kind.name(),
        request.dir.display()
      ),
    }))
  })
}

/// `Ladder.completeExport (l : @& Ladder) (id : UInt64) (error : @& String)
/// : IO Unit`: the answer to request `id` (empty `error`: success).
#[unsafe(no_mangle)]
extern "C" fn rs_ladder_complete_export(
  handle: LeanExternal<LadderHandle, LeanBorrowed<'_>>,
  id: u64,
  error: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let error = error.to_string();
  let broker = Arc::clone(&handle.get().broker);
  io(move || {
    broker.complete(id, if error.is_empty() { Ok(()) } else { Err(error) });
    Ok(LeanOwned::box_usize(0))
  })
}

/// `Ladder.run (l : @& Ladder) : IO String`: proves every stage; the run
/// summary (JSON). The export server's loop ends when this returns.
#[unsafe(no_mangle)]
extern "C" fn rs_ladder_run(
  handle: LeanExternal<LadderHandle, LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let handle = handle.get();
  io(|| {
    let result = handle.ladder.run();
    handle.broker.close();
    let (_, summary) = result?;
    Ok(LeanString::new(
      &serde_json::to_string_pretty(&summary).map_err(|e| e.to_string())?,
    ))
  })
}
