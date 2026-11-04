//! Lean adapter for the formal Aiur prover library (`ix-prover`).
//! Environments and requests are opaque Rust-owned handles. Lean byte
//! arrays are borrowed only for the duration of a call.
//!
//! Errors become Lean `IO` errors. A panic is caught at this boundary when
//! the build unwinds, and aborts the process under the workspace's
//! `panic = "abort"` profiles; it never unwinds into Lean.
//!
//! Lean declarations: `Ix/FormalProver.lean`.
use std::{
  panic::{AssertUnwindSafe, catch_unwind},
  path::Path,
  sync::{Arc, LazyLock},
};

use ix_prover::{
  protocol::{Kind, Options},
  request::{Environment, Request},
  tools,
};
use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExternal,
  LeanIOResult, LeanOwned, LeanProd, LeanRef, LeanString,
};

struct FormalEnvironment(Arc<Environment>);
struct FormalRequest(Request);

static ENVIRONMENT_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalEnvironment>);
static REQUEST_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalRequest>);

fn io(
  f: impl FnOnce() -> Result<LeanOwned, String>,
) -> LeanIOResult<LeanOwned> {
  match catch_unwind(AssertUnwindSafe(f)) {
    Ok(Ok(value)) => LeanIOResult::ok(value),
    Ok(Err(error)) => LeanIOResult::error_string(&error),
    Err(_) => LeanIOResult::error_string("formal prover panicked"),
  }
}

fn small_nat(n: LeanBorrowed<'_>) -> Result<usize, String> {
  if n.is_scalar() {
    Ok(n.unbox_usize())
  } else {
    Err("natural number argument is too large".into())
  }
}

fn options(json: &str) -> Result<Options, String> {
  serde_json::from_str(json).map_err(|e| format!("invalid job options: {e}"))
}

/// Run `f` on a pool of `threads` threads, or on the global pool for zero.
fn with_threads<T: Send>(
  threads: usize,
  f: impl FnOnce() -> T + Send,
) -> Result<T, String> {
  if threads == 0 {
    return Ok(f());
  }
  let pool = rayon::ThreadPoolBuilder::new()
    .num_threads(threads)
    .build()
    .map_err(|e| e.to_string())?;
  Ok(pool.install(f))
}

fn completion(status: u32, report: &serde_json::Value) -> LeanOwned {
  LeanProd::new(
    LeanOwned::box_u32(status),
    LeanString::new(&report.to_string()),
  )
  .into()
}

/// `Ix.FormalProver.Env.ofHandle : @& Aiur.EnvHandle → IO Env`: a copy of
/// the environment Lean loaded, normalized or compiled; constant bytes are
/// shared.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_env_of_handle(
  handle: LeanExternal<crate::lean_ixon::EnvHandle, LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let env = Environment::new(handle.get().env.clone());
    Ok(
      LeanExternal::alloc(&ENVIRONMENT_CLASS, FormalEnvironment(Arc::new(env)))
        .into(),
    )
  })
}

fn request(request: Result<Request, String>) -> Result<LeanOwned, String> {
  Ok(LeanExternal::alloc(&REQUEST_CLASS, FormalRequest(request?)).into())
}

/// `Ix.FormalProver.Request.check : @& Env → (target claim : @& ByteArray)
/// → IO Request`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_request_check(
  env: LeanExternal<FormalEnvironment, LeanBorrowed<'_>>,
  target: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    request(Request::check(
      env.get().0.clone(),
      target.as_bytes(),
      claim.as_bytes(),
    ))
  })
}

/// `Ix.FormalProver.Request.shard : @& Env → (blocks claim : @& ByteArray)
/// → IO Request`, with the blocks as concatenated addresses.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_request_shard(
  env: LeanExternal<FormalEnvironment, LeanBorrowed<'_>>,
  blocks: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    request(Request::shard(
      env.get().0.clone(),
      blocks.as_bytes(),
      claim.as_bytes(),
    ))
  })
}

/// `Ix.FormalProver.Request.buffers : (entry : @& String) →
/// (args : @& Array UInt64) → (meta bytes words : @& ByteArray) →
/// IO Request`: an existing witness, copied once into compact advice.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_request_buffers(
  entry: LeanString<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  meta: LeanByteArray<LeanBorrowed<'_>>,
  bytes: LeanByteArray<LeanBorrowed<'_>>,
  words: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    request(Request::buffers(
      entry.as_str().to_owned(),
      args.map(|word| word.unbox_u64()),
      meta.as_bytes(),
      bytes.as_bytes(),
      words.as_bytes(),
    ))
  })
}

/// `Ix.FormalProver.resources : IO String`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_resources() -> LeanIOResult<LeanOwned> {
  io(|| Ok(LeanString::new(&tools::resources().to_string()).into()))
}

/// `Ix.FormalProver.executors : IO (Array String)`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_executors() -> LeanIOResult<LeanOwned> {
  io(|| {
    let names = ix_prover::executors();
    let array = LeanArray::alloc(names.len());
    for (i, name) in names.iter().enumerate() {
      array.set(i, LeanString::new(name));
    }
    Ok(array.into())
  })
}

/// `Ix.FormalProver.verify : (artifact entry : @& String) →
/// (args : @& Array UInt64) → (proof : @& ByteArray) → IO Nat`: the number
/// of trace shards of a proof that verifies.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_verify(
  artifact: LeanString<LeanBorrowed<'_>>,
  entry: LeanString<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let args = args.map(|word| word.unbox_u64());
    let shards = tools::verify(
      Path::new(artifact.as_str()),
      entry.as_str(),
      &args,
      proof.as_bytes(),
    )?;
    Ok(LeanOwned::box_usize(shards))
  })
}

/// `Ix.FormalProver.identity : (artifact : @& String) → (recursive : Bool) →
/// IO (ByteArray × Nat × Nat)`: the verifying key, function index and call
/// channel.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_identity(
  artifact: LeanString<LeanBorrowed<'_>>,
  recursive: bool,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let kind = if recursive { Kind::Recursion } else { Kind::Ixvm };
    let identity = tools::identity(Path::new(artifact.as_str()), kind)?;
    let nat = |n: u64| {
      usize::try_from(n)
        .map(LeanOwned::box_usize)
        .map_err(|e| format!("identity word: {e}"))
    };
    Ok(
      LeanProd::new(
        LeanByteArray::from_bytes(&identity.key),
        LeanProd::new(
          nat(identity.function_index)?,
          nat(identity.call_channel)?,
        ),
      )
      .into(),
    )
  })
}

/// `Ix.FormalProver.prove : (artifact : @& String) → @& Request →
/// (output options : @& String) → (threads : @& Nat) → IO (UInt32 × String)`:
/// prove one IxVM claim, writing the proof next to `output`.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_prove(
  artifact: LeanString<LeanBorrowed<'_>>,
  job_request: LeanExternal<FormalRequest, LeanBorrowed<'_>>,
  output: LeanString<LeanBorrowed<'_>>,
  job_options: LeanString<LeanBorrowed<'_>>,
  threads: LeanBorrowed<'_>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let options = options(job_options.as_str())?;
    let (status, report) = tools::prove(
      Path::new(artifact.as_str()),
      &job_request.get().0,
      &options,
      Path::new(output.as_str()),
      small_nat(threads)?,
    )?;
    Ok(completion(status, &report))
  })
}

/// `Ix.FormalProver.check : (plan : Bool) → (artifact : @& String) →
/// @& Request → (options : @& String) → (threads : @& Nat) →
/// IO (UInt32 × String)`: execute an IxVM claim, and with `plan` also plan
/// its proof, without proving.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_check(
  plan: bool,
  artifact: LeanString<LeanBorrowed<'_>>,
  job_request: LeanExternal<FormalRequest, LeanBorrowed<'_>>,
  job_options: LeanString<LeanBorrowed<'_>>,
  threads: LeanBorrowed<'_>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let mode = if plan { tools::Check::Plan } else { tools::Check::Execute };
    let options = options(job_options.as_str())?;
    let artifact = Path::new(artifact.as_str());
    let job_request = &job_request.get().0;
    let (status, report) = with_threads(small_nat(threads)?, || {
      tools::check(mode, artifact, job_request, &options)
    })??;
    Ok(completion(status, &report))
  })
}

/// `Ix.FormalProver.proveLanes : @& Aiur.EnvHandle → @& String → IO String`:
/// the whole lane run over the handle's environment from its JSON
/// configuration (`ix_prover::aggregate::LaneConfig`) on the aggregate
/// controller, returning the verified root's store address. The environment
/// is borrowed for the call, not copied.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_prove_lanes(
  env: LeanExternal<crate::lean_ixon::EnvHandle, LeanBorrowed<'_>>,
  config: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config: ix_prover::aggregate::LaneConfig =
      serde_json::from_str(config.as_str())
        .map_err(|e| format!("invalid lane configuration: {e}"))?;
    let root = ix_prover::aggregate::prove_lanes(&config, &env.get().env)?;
    Ok(LeanString::new(&root).into())
  })
}

/// `Ix.FormalProver.aggregate : @& Aiur.EnvHandle → @& String →
/// IO (String × ByteArray)`: `ix aggregate` over the handle's environment
/// from its JSON configuration (`ix_prover::aggregate::AggregateConfig`),
/// returning the address of the proof it produced (an empty string for a
/// plan) and, when the run did not persist that proof, its encoded wrapper
/// (otherwise empty).
#[unsafe(no_mangle)]
extern "C" fn rs_formal_aggregate(
  env: LeanExternal<crate::lean_ixon::EnvHandle, LeanBorrowed<'_>>,
  config: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config: ix_prover::aggregate::AggregateConfig =
      serde_json::from_str(config.as_str())
        .map_err(|e| format!("invalid aggregate configuration: {e}"))?;
    let output = ix_prover::aggregate::aggregate(&config, &env.get().env)?;
    let (address, wrapper) = match output {
      Some(output) => {
        (output.address.hex(), output.wrapper.unwrap_or_default())
      },
      None => (String::new(), Vec::new()),
    };
    Ok(
      LeanProd::new(
        LeanString::new(&address),
        LeanByteArray::from_bytes(&wrapper),
      )
      .into(),
    )
  })
}

/// `Ix.FormalProver.aggregateCatalog : @& String → IO String`:
/// `ix aggregate --ixc` from its JSON configuration
/// (`ix_prover::aggregate::CatalogConfig`), returning the address of the
/// catalog root's proof wrapper.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_aggregate_catalog(
  config: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config: ix_prover::aggregate::CatalogConfig =
      serde_json::from_str(config.as_str())
        .map_err(|e| format!("invalid catalog configuration: {e}"))?;
    Ok(
      LeanString::new(&ix_prover::aggregate::aggregate_catalog(&config)?)
        .into(),
    )
  })
}

/// `Ix.FormalProver.normalizeRoot : @& String → @& ByteArray →
/// @& ByteArray → @& ByteArray → IO ByteArray`: the raw proof of one more wrap of the
/// aggregate root `proof` of `claim`, proved at the heights of the fixed
/// layout `layout` (`.ixl` bytes) from the JSON configuration
/// (`ix_prover::aggregate::NormalizeConfig`).
#[unsafe(no_mangle)]
extern "C" fn rs_formal_normalize_root(
  config: LeanString<LeanBorrowed<'_>>,
  layout: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config: ix_prover::aggregate::NormalizeConfig =
      serde_json::from_str(config.as_str())
        .map_err(|e| format!("invalid normalization configuration: {e}"))?;
    let layout =
      ix_proof_compression::pipeline::FixedRoot::from_bytes(layout.as_bytes())
        .map_err(|e| e.to_string())?;
    let normalized = ix_prover::aggregate::normalize_root(
      &config,
      layout.log_heights(),
      claim.as_bytes(),
      proof.as_bytes(),
    )?;
    Ok(LeanByteArray::from_bytes(&normalized).into())
  })
}
