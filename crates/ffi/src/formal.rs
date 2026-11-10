//! Lean adapter for the formal Aiur prover library (`ix-prover`).
//! Registries, programs, systems, environments and requests are opaque
//! Rust-owned handles. Lean byte arrays are borrowed only for the duration
//! of a call; work that outlives a call holds the handles' shared data.
//!
//! Errors become Lean `IO` errors. The workspace profiles abort on panic,
//! so a panic never unwinds into Lean.
//!
//! Lean declarations: `Ix/FormalProver.lean`.
use std::{
  path::Path,
  sync::{Arc, LazyLock},
};

mod records;

use ix_prover::{
  aggregate::LaneResult,
  protocol::Kind,
  request::{Environment, Request},
  system::{Program, Registry, System},
  tools,
};
use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExternal,
  LeanIOResult, LeanNat, LeanOption, LeanOwned, LeanProd, LeanRef, LeanString,
};
use records::{
  LeanAggregateConfig, LeanCatalogConfig, LeanJobOptions, LeanLaneConfig,
  LeanLaneResult, LeanNormalizeConfig, LeanProtocolParameters,
};

struct FormalEnvironment(Arc<Environment>);
struct FormalRequest(Request);
struct FormalRegistry(Registry);
struct FormalProgram(Program);
struct FormalSystem(System);

static ENVIRONMENT_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalEnvironment>);
static REQUEST_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalRequest>);
static REGISTRY_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalRegistry>);
static PROGRAM_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalProgram>);
static SYSTEM_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<FormalSystem>);

type Borrowed<'a, T> = LeanExternal<T, LeanBorrowed<'a>>;

fn io<T: Into<LeanOwned>>(
  f: impl FnOnce() -> Result<T, String>,
) -> LeanIOResult<LeanOwned> {
  match f() {
    Ok(value) => LeanIOResult::ok(value),
    Err(error) => LeanIOResult::error_string(&error),
  }
}

fn small_nat(n: LeanNat<LeanBorrowed<'_>>) -> Result<usize, String> {
  records::nat(*n.inner())
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

/// `Ix.FormalProver.Env.ofHandle : @& Aiur.EnvHandle → IO Env`: a copy of
/// the environment Lean loaded, normalized or compiled; constant bytes are
/// shared.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_env_of_handle(
  handle: LeanExternal<crate::lean_ixon::EnvHandle, LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let env = Environment::new(handle.get().env.clone());
    Ok(LeanExternal::alloc(
      &ENVIRONMENT_CLASS,
      FormalEnvironment(Arc::new(env)),
    ))
  })
}

fn request(
  request: Result<Request, String>,
) -> Result<LeanExternal<FormalRequest, LeanOwned>, String> {
  Ok(LeanExternal::alloc(&REQUEST_CLASS, FormalRequest(request?)))
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

/// `Ix.FormalProver.resources : IO Resources`: available bytes, when known,
/// and logical cores.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_resources() -> LeanIOResult<LeanOwned> {
  io(|| {
    let (available, cores) = tools::resources();
    Ok(records::resources(available, cores))
  })
}

/// `Ix.FormalProver.executors : IO (Array String)`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_executors() -> LeanIOResult<LeanOwned> {
  io(|| {
    Ok(records::lean_array(
      ix_prover::executors().iter().map(|name| LeanString::new(name)),
    ))
  })
}

fn nat(n: u64) -> Result<LeanOwned, String> {
  usize::try_from(n)
    .map(LeanOwned::box_usize)
    .map_err(|e| format!("natural number result: {e}"))
}

/// `Ix.FormalProver.Registry.new : IO Registry`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_registry_new() -> LeanIOResult<LeanOwned> {
  io(|| {
    Ok(LeanExternal::alloc(
      &REGISTRY_CLASS,
      FormalRegistry(Registry::default()),
    ))
  })
}

/// `Ix.FormalProver.Registry.load : @& Registry → (path : @& String) →
/// IO Program`: the compiled package at `path`, decoded and checked once per
/// registry.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_registry_load(
  registry: Borrowed<'_, FormalRegistry>,
  path: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let path = Path::new(path.as_str());
    let canonical = std::fs::canonicalize(path)
      .map_err(|e| format!("{}: {e}", path.display()))?;
    let key = canonical.to_str().ok_or("artifact path is not UTF-8")?;
    let program =
      registry.get().0.program(key, || ix_prover::load_program(&canonical))?;
    Ok(LeanExternal::alloc(&PROGRAM_CLASS, FormalProgram(program)))
  })
}

/// `Ix.FormalProver.Program.identity : @& Program → IO ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_program_identity(
  program: Borrowed<'_, FormalProgram>,
) -> LeanIOResult<LeanOwned> {
  io(|| Ok(LeanByteArray::from_bytes(program.get().0.identity())))
}

/// `Ix.FormalProver.Registry.system : @& Registry → @& Program →
/// @& ProtocolParameters → IO System`: the program's verifying system under
/// the parameters, prepared once per registry.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_registry_system(
  registry: Borrowed<'_, FormalRegistry>,
  program: Borrowed<'_, FormalProgram>,
  params: LeanProtocolParameters<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let system = registry
      .get()
      .0
      .system(&program.get().0, records::parameters(params)?)?;
    Ok(LeanExternal::alloc(&SYSTEM_CLASS, FormalSystem(system)))
  })
}

/// `Ix.FormalProver.counters : IO (Nat × Nat × Nat × Nat)`: programs, plans,
/// systems and proving backends constructed by this process.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_counters() -> LeanIOResult<LeanOwned> {
  io(|| {
    let c = ix_prover::system::counters();
    let n = |x: usize| LeanOwned::box_usize(x);
    Ok(LeanProd::new(
      n(c.programs),
      LeanProd::new(n(c.plans), LeanProd::new(n(c.systems), n(c.provers))),
    ))
  })
}

/// `Ix.FormalProver.System.verify : @& System → (entry : @& String) →
/// (args : @& Array UInt64) → (proof : @& ByteArray) → IO Nat`: the number
/// of trace shards of a proof that verifies.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_system_verify(
  system: Borrowed<'_, FormalSystem>,
  entry: LeanString<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let args = args.map(|word| word.unbox_u64());
    let shards =
      tools::verify(&system.get().0, entry.as_str(), &args, proof.as_bytes())?;
    Ok(LeanOwned::box_usize(shards))
  })
}

/// `Ix.FormalProver.System.key : @& System → IO ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_formal_system_key(
  system: Borrowed<'_, FormalSystem>,
) -> LeanIOResult<LeanOwned> {
  io(|| Ok(LeanByteArray::from_bytes(system.get().0.key())))
}

/// `Ix.FormalProver.System.identity : @& System → (recursive : Bool) →
/// IO (ByteArray × Nat × Nat)`: the verifying key, function index and call
/// channel.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_system_identity(
  system: Borrowed<'_, FormalSystem>,
  recursive: bool,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let kind = if recursive { Kind::Recursion } else { Kind::Ixvm };
    let identity = tools::identity(&system.get().0, kind)?;
    Ok(LeanProd::new(
      LeanByteArray::from_bytes(&identity.key),
      LeanProd::new(nat(identity.function_index)?, nat(identity.call_channel)?),
    ))
  })
}

/// `Ix.FormalProver.System.prove : @& System → @& Request →
/// (output : @& String) → @& JobOptions → (threads : @& Nat) →
/// (report : Bool) → IO Outcome`: prove one IxVM claim, writing the proof
/// next to `output`.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_system_prove(
  system: Borrowed<'_, FormalSystem>,
  job_request: Borrowed<'_, FormalRequest>,
  output: LeanString<LeanBorrowed<'_>>,
  job_options: LeanJobOptions<LeanBorrowed<'_>>,
  threads: LeanNat<LeanBorrowed<'_>>,
  report: bool,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let options = records::options(*job_options.inner())?;
    let outcome = tools::prove(
      &system.get().0,
      &job_request.get().0,
      &options,
      Path::new(output.as_str()),
      small_nat(threads)?,
    )?;
    Ok(records::outcome(&outcome, report))
  })
}

/// `Ix.FormalProver.System.check : @& System → @& Request →
/// (threads : @& Nat) → (report : Bool) → IO Outcome`: execute an IxVM
/// claim on the system's program without proving.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_system_check(
  system: Borrowed<'_, FormalSystem>,
  job_request: Borrowed<'_, FormalRequest>,
  threads: LeanNat<LeanBorrowed<'_>>,
  report: bool,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let system = &system.get().0;
    let job_request = &job_request.get().0;
    let outcome = with_threads(small_nat(threads)?, || {
      tools::execute(system, job_request)
    })??;
    Ok(records::outcome(&outcome, report))
  })
}

/// `Ix.FormalProver.System.plan : @& System → @& Request → @& JobOptions →
/// (threads : @& Nat) → (report : Bool) → IO Outcome`: execute an IxVM
/// claim and plan its proof without proving.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_system_plan(
  system: Borrowed<'_, FormalSystem>,
  job_request: Borrowed<'_, FormalRequest>,
  job_options: LeanJobOptions<LeanBorrowed<'_>>,
  threads: LeanNat<LeanBorrowed<'_>>,
  report: bool,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let options = records::options(*job_options.inner())?;
    let system = &system.get().0;
    let job_request = &job_request.get().0;
    let outcome = with_threads(small_nat(threads)?, || {
      tools::plan(system, job_request, &options)
    })??;
    Ok(records::outcome(&outcome, report))
  })
}

/// `Ix.FormalProver.proveLanes : (ixvm aggr : @& System) →
/// @& Aiur.EnvHandle → @& LaneConfig → IO LaneResult`: the whole lane run
/// over the handle's environment on the aggregate controller: the verified
/// root's store address, or each proven claim's shard id and address. The
/// environment is borrowed for the call, not copied.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_prove_lanes(
  ixvm: Borrowed<'_, FormalSystem>,
  aggr: Borrowed<'_, FormalSystem>,
  env: LeanExternal<crate::lean_ixon::EnvHandle, LeanBorrowed<'_>>,
  config: LeanLaneConfig<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config = records::lane_config(config)?;
    let result = ix_prover::aggregate::prove_lanes(
      &config,
      &env.get().env,
      &ixvm.get().0,
      &aggr.get().0,
    )?;
    Ok(match result {
      LaneResult::Root(address) => {
        let root = LeanLaneResult::alloc(0);
        root.set_obj(0, records::lean_address(&address));
        root
      },
      LaneResult::Claims(claims) => {
        let proven = LeanLaneResult::alloc(1);
        proven.set_obj(
          0,
          records::lean_array(claims.iter().map(|(id, address)| {
            LeanProd::new(
              LeanOwned::box_usize(*id as usize),
              records::lean_address(address),
            )
          })),
        );
        proven
      },
    })
  })
}

/// `Ix.FormalProver.aggregate : (ixvm aggr : @& System) →
/// @& Aiur.EnvHandle → @& AggregateConfig →
/// (bindingProof : @& Option ByteArray) → IO (Option (ByteArray × ByteArray))`:
/// `ix aggregate` over the handle's environment. A supplied binding proof is
/// the encoded wrapper of a run that writes nothing to the store. Returns
/// nothing for a plan; otherwise the address of the proof it produced and,
/// when the run did not persist that proof, its encoded wrapper (otherwise
/// empty).
#[unsafe(no_mangle)]
extern "C" fn rs_formal_aggregate(
  ixvm: Borrowed<'_, FormalSystem>,
  aggr: Borrowed<'_, FormalSystem>,
  env: LeanExternal<crate::lean_ixon::EnvHandle, LeanBorrowed<'_>>,
  config: LeanAggregateConfig<LeanBorrowed<'_>>,
  binding_proof: LeanOption<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config = records::aggregate_config(config)?;
    let binding = binding_proof
      .to_option()
      .map(|bytes| bytes.as_byte_array().as_bytes().to_vec());
    let output = ix_prover::aggregate::aggregate(
      &config,
      &env.get().env,
      &ixvm.get().0,
      &aggr.get().0,
      binding,
    )?;
    Ok(records::some_or_none(output.map(|output| {
      LeanProd::new(
        records::lean_address(&output.address),
        LeanByteArray::from_bytes(&output.wrapper.unwrap_or_default()),
      )
    })))
  })
}

/// `Ix.FormalProver.aggregateCatalog : (ixvm aggr : @& System) →
/// @& CatalogConfig → IO ByteArray`: `ix aggregate --ixc`, returning the
/// address of the catalog root's proof wrapper.
#[unsafe(no_mangle)]
extern "C" fn rs_formal_aggregate_catalog(
  ixvm: Borrowed<'_, FormalSystem>,
  aggr: Borrowed<'_, FormalSystem>,
  config: LeanCatalogConfig<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config = records::catalog_config(config)?;
    let root = ix_prover::aggregate::aggregate_catalog(
      &config,
      &ixvm.get().0,
      &aggr.get().0,
    )?;
    Ok(records::lean_address(&root))
  })
}

/// `Ix.FormalProver.normalizeRoot : (ixvm aggr : @& System) →
/// @& NormalizeConfig → (layout claim proof : @& ByteArray) → IO ByteArray`:
/// the raw proof of one more wrap of the aggregate root `proof` of `claim`,
/// proved at the heights of the fixed layout `layout` (`.ixl` bytes).
#[unsafe(no_mangle)]
extern "C" fn rs_formal_normalize_root(
  ixvm: Borrowed<'_, FormalSystem>,
  aggr: Borrowed<'_, FormalSystem>,
  config: LeanNormalizeConfig<LeanBorrowed<'_>>,
  layout: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  io(|| {
    let config = records::normalize_config(config)?;
    let layout =
      ix_proof_compression::pipeline::FixedRoot::from_bytes(layout.as_bytes())
        .map_err(|e| e.to_string())?;
    let normalized = ix_prover::aggregate::normalize_root(
      &config,
      &ixvm.get().0,
      &aggr.get().0,
      layout.log_heights(),
      claim.as_bytes(),
      proof.as_bytes(),
    )?;
    Ok(LeanByteArray::from_bytes(&normalized))
  })
}
