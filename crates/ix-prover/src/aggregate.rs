//! The formal provers behind the aggregate controller: `IxVM::verify_claim`
//! for environment claims and `MultiStark::ix_aggr` for joins and root
//! wraps. The controller decides what runs when; this adapter
//! executes, proves, verifies and encodes one unit of work.
//!
//! A claim's witness is rebuilt from the environment and must reproduce the
//! controller's statement, so every leaf also checks the Rust fold against
//! `ixon`. Aggregation advice comes from [`aggregate_controller::streams`].
use std::{path::PathBuf, sync::Arc};

use aggregate_controller::{
  Backend, BackendSlot, ChildProof, ExtraNode, Identity, PrepareFailure,
  ProvenClaim, Run, catalog,
  discharge::BindingSource,
  lanes::{self, cell_workspace},
  plan::PlanOp,
  protocol::{ChildKind, WordIdentity, packed_digest},
  store::{load_cached, persist_cached},
  streams::{self, Child, Keys, Streams, Transport},
};
use aiur::{
  Execution,
  field::FieldBackend,
  library::advice::AdviceBuilder,
  trace::stark::{BatchProof, ShardFeed, fri_parameter_bytes, planning},
};
use ix_common::address::Address;
use ixon::witness::WitnessRequest;
use multi_stark::p3_field::PrimeField64;
use record_pool::{BudgetError, RecordReservation};

use crate::{
  Field, PrepFailure,
  protocol::{Kind, Options},
  request::{IXVM_ENTRY, bind_advice, leaf_advice},
  system::{Prover, System},
};

pub const AGGR_ENTRY: &str = "MultiStark::ix_aggr";
/// The call namespace of formal entry claims.
const FORMAL_CALL_CHANNEL: u64 = 1;
pub const IXVM_MAGIC: &[u8] = b"IXAIUR2\0";
pub const AGGR_MAGIC: &[u8] = b"IXAGGR2\0";

type Element = <Field as FieldBackend>::Element;

/// A formal proof as the controller holds it: raw `BatchProof` bytes, the
/// system that proves it, and its trace-shard count.
#[derive(Clone)]
pub struct FormalProof {
  pub kind: ChildKind,
  pub raw: Arc<[u8]>,
  pub shards: usize,
}

impl FormalProof {
  fn new(kind: ChildKind, proof: &BatchProof) -> Result<Self, String> {
    let raw = proof.to_bytes().map_err(|e| e.to_string())?;
    Ok(Self { kind, raw: raw.into(), shards: proof.proofs.len() })
  }
}

fn magic(kind: ChildKind) -> &'static [u8] {
  match kind {
    ChildKind::Ixvm => IXVM_MAGIC,
    ChildKind::Aggr => AGGR_MAGIC,
  }
}

fn index(kind: ChildKind) -> usize {
  match kind {
    ChildKind::Ixvm => 0,
    ChildKind::Aggr => 1,
  }
}

/// The run as `ix prove --lanes` configures it.
pub struct LaneConfig {
  pub manifest: PathBuf,
  pub lanes: usize,
  /// The first lane's CUDA device; `None` proves on the CPU.
  pub device: Option<i32>,
  /// Zero detects the host's allowance.
  pub max_ram_bytes: usize,
  pub exec_jobs: usize,
  pub structural_above: usize,
  pub use_cache: bool,
  pub use_index: bool,
  pub out_manifest: Option<PathBuf>,
  /// Prove the claims only, without joins or a root.
  pub claims_only: bool,
  /// With `claims_only`, the shard ids to prove; every claim otherwise.
  pub select: Option<Vec<u32>>,
  /// Claims assume their role binding meets the specifications instead of
  /// validating it.
  pub assume_binding: bool,
  /// The store address of a proof of the environment's `Binding` claim:
  /// the claims assume their binding and the root discharges it.
  pub binding_proof: Option<Address>,
  /// Planner options of every proof; the device and RAM budget are the
  /// lane's.
  pub options: Options,
}

/// What a lane run proved: the verified root, or with `claims_only` each
/// proven claim's shard id and proof address.
pub enum LaneResult {
  Root(Address),
  Claims(Vec<(u32, Address)>),
}

/// One resident prover per system on one device, the threads it proves
/// on, and as many that build its next trace shard meanwhile.
pub struct Lane {
  provers: [Prover; 2],
  pool: rayon::ThreadPool,
  feed: ShardFeed,
  device: Option<i32>,
}

/// The formal backend over the IxVM and aggregation systems the command
/// selected. Verification and keys come from the shared systems; each lane
/// builds its own proving backends.
pub struct Formal {
  systems: [System; 2],
  identity: WordIdentity,
  options: Options,
  device: Option<i32>,
  shared_devices: bool,
  threads_per_prover: usize,
  workspace: usize,
}

impl Formal {
  pub fn new(
    ixvm: &System,
    aggr: &System,
    lanes: usize,
    device: Option<i32>,
    options: Options,
  ) -> Result<Self, String> {
    options.validate()?;
    if ixvm.parameters() != aggr.parameters() {
      return Err(
        "the IxVM and aggregation systems use different STARK parameters"
          .into(),
      );
    }
    let function_index = |system: &System, entry, arity| {
      let identity = system.identity(entry, arity)?;
      if identity.call_channel != FORMAL_CALL_CHANNEL {
        return Err("claim lacks its call namespace".to_owned());
      }
      Ok(identity.function_index)
    };
    let ixvm_index = function_index(ixvm, IXVM_ENTRY, 8)?;
    let aggr_index = function_index(aggr, AGGR_ENTRY, 16)?;
    let identity = WordIdentity::new(
      FORMAL_CALL_CHANNEL,
      ixvm.key(),
      ixvm_index,
      aggr.key(),
      aggr_index,
      fri_parameter_bytes(ixvm.parameters().into()),
    );
    let workspace = match std::env::var("AIUR_HOST_WORKSPACE_BYTES") {
      Ok(value) => value
        .parse::<usize>()
        .ok()
        .filter(|&n| n > 0)
        .ok_or("AIUR_HOST_WORKSPACE_BYTES must be a positive integer")?,
      Err(std::env::VarError::NotPresent) => {
        let cells = usize::try_from(planning::configured_cells()?)
          .map_err(|e| e.to_string())?;
        cell_workspace(cells).ok_or("prover workspace budget overflow")?
      },
      Err(error) => return Err(format!("AIUR_HOST_WORKSPACE_BYTES: {error}")),
    };
    let cores = std::thread::available_parallelism().map_or(1, usize::from);
    ixvm::register_compiled_trace();
    Ok(Self {
      systems: [ixvm.clone(), aggr.clone()],
      identity,
      options,
      device,
      shared_devices: std::env::var("IX_PROVER_SHARED_DEVICES").as_deref()
        == Ok("1"),
      threads_per_prover: (cores / lanes.max(1)).max(1),
      workspace,
    })
  }

  fn keys(&self) -> Keys<'_> {
    Keys {
      allowed: &self.identity.allowed,
      ixvm: self.systems[0].key(),
      aggr: self.systems[1].key(),
    }
  }

  /// `Aggr.pubInput`: the packed digests of the identity blob and of the
  /// output statement.
  fn public_input(&self, statement: &[u8]) -> Vec<u64> {
    let mut args = packed_digest(&self.identity.allowed);
    args.extend(packed_digest(statement));
    args
  }

  /// Executes `ix_aggr` over `streams`, charged to `reservation`.
  fn execute_streams(
    &self,
    streams: &Streams<'_>,
    args: &[u64],
    reservation: &RecordReservation,
  ) -> Result<(Vec<Element>, Execution<Field>), PrepareFailure> {
    let program = self.systems[1].program().checked();
    let mut builder = AdviceBuilder::new(program.field())?;
    for (channel, key, payload) in streams.entries() {
      builder.push_bytes(*channel, key, payload)?;
    }
    let advice = builder.finish();
    reservation.reserve(advice.retained_bytes().total()).map_err(resource)?;
    let bound = bind_advice(
      program,
      Kind::Recursion,
      AGGR_ENTRY.to_owned(),
      args,
      &advice,
      reservation,
      serde_json::Map::new(),
    )
    .map_err(prep_failure)?;
    drop(advice);
    self.execute_bound(1, bound, reservation)
  }

  fn execute_bound(
    &self,
    artifact: usize,
    bound: crate::request::Bound<'_>,
    reservation: &RecordReservation,
  ) -> Result<(Vec<Element>, Execution<Field>), PrepareFailure> {
    let (record, _) = self.systems[artifact].program().executor().execute(
      &bound.hints,
      &bound.entry,
      bound.args.clone(),
      reservation,
    );
    let record = record.map_err(|error| match error.resource {
      Some(budget) => resource(budget),
      None => PrepareFailure::Other(format!("execution failed: {error}")),
    })?;
    if !record.output.is_empty() {
      return Err("verifier returned a value".into());
    }
    let args = bound.args.clone();
    let charged = bound.charged;
    drop(bound);
    reservation.release(charged);
    Ok((args, record))
  }

  /// Plans `record` within the lane workspace and proves it on `lane`.
  fn prove(
    &self,
    lane: &Lane,
    kind: ChildKind,
    record: &Execution<Field>,
    entry: &str,
    args: &[Element],
  ) -> Result<FormalProof, String> {
    let prover = &lane.provers[index(kind)];
    let mut options = self.options.clone();
    options.device = lane.device;
    let budget = self.workspace as u64;
    options.max_ram_bytes =
      Some(options.max_ram_bytes.unwrap_or(budget).min(budget));
    let batch = prover.plan_record(record, &options, 0)?;
    if !batch.fits {
      return Err(format!(
        "no trace-shard plan fits the {budget}-byte lane workspace \
         (generation peak {}, proving peak {}); raise --max-ram or \
         AIUR_HOST_WORKSPACE_BYTES",
        batch.generation_peak_bytes, batch.proving_peak_bytes
      ));
    }
    let layout = batch
      .layout
      .as_ref()
      .ok_or("the proving plan has no incremental layout")?;
    let run = lane.pool.install(|| {
      prover.prove_incremental_fed(
        record,
        entry,
        args,
        &[],
        layout,
        batch.retention(),
        batch.pipelined.then_some(&lane.feed),
      )
    })?;
    eprintln!(
      "[lanes] {} proof: {} trace shards, trace {:.1}s, proving {:.1}s, population stall {:.1}s{}",
      match kind {
        ChildKind::Ixvm => "claim",
        ChildKind::Aggr => "aggregate",
      },
      run.proof.proofs.len(),
      run.trace_seconds,
      run.proving_seconds,
      run.population.stall_seconds,
      if run.population.pipelined { ", pipelined" } else { "" },
    );
    FormalProof::new(kind, &run.proof)
  }
}

fn resource(error: BudgetError) -> PrepareFailure {
  match error {
    BudgetError::Exceeded { bytes, cap } => {
      PrepareFailure::OverRecordCap { bytes, cap }
    },
    BudgetError::Cancelled => PrepareFailure::MemoryContention,
    BudgetError::Shutdown => {
      PrepareFailure::Other("record pool shut down".into())
    },
  }
}

fn prep_failure(failure: PrepFailure) -> PrepareFailure {
  match failure {
    PrepFailure::Resource(error) => resource(error),
    PrepFailure::Other(error) => PrepareFailure::Other(error),
  }
}

fn child<'s>(slot: &'s BackendSlot<Formal>) -> Child<'s> {
  Child {
    kind: slot.kind,
    statement: &slot.statement,
    proof: &slot.proof.raw,
    claims: &slot.claims_bytes,
  }
}

fn transport(c: ChildProof<'_, FormalProof>) -> Transport<'_> {
  Transport { kind: c.kind, proof: &c.proof.raw, claims: c.claims_bytes }
}

impl Identity for Formal {
  type Claim = Vec<u64>;

  fn outer_claim(&self, kind: ChildKind, claim_bytes: &[u8]) -> Vec<u64> {
    self.identity.outer_claim(kind, claim_bytes)
  }

  fn claims_bytes(&self, outer: &Vec<u64>) -> Vec<u8> {
    self.identity.claims_bytes(outer)
  }

  fn cache_key(&self, outer: &Vec<u64>) -> Address {
    self.identity.cache_key(outer)
  }
}

pub struct ClaimRecord {
  claim: ixon::Claim,
  claim_bytes: Vec<u8>,
  args: Vec<Element>,
  record: Execution<Field>,
}

pub enum Staged {
  Cached(FormalProof, Address),
  Executed { args: Vec<Element>, record: Box<Execution<Field>> },
}

impl Backend for Formal {
  type Lane = Lane;
  type Proof = FormalProof;
  type ClaimRecord = ClaimRecord;
  type Staged = Staged;
  type Binding = ();

  fn lanes(&self, count: usize) -> Result<Vec<Lane>, String> {
    (0..count)
      .map(|lane| {
        let offset = if self.shared_devices { 0 } else { lane };
        let device = self
          .device
          .map(|first| {
            i32::try_from(offset)
              .ok()
              .and_then(|offset| first.checked_add(offset))
              .ok_or("CUDA device index overflow")
          })
          .transpose()?;
        let prover = |system: &System| {
          system.prover(device).map_err(|e| format!("lane {lane}: {e}"))
        };
        let provers = [prover(&self.systems[0])?, prover(&self.systems[1])?];
        let pool = rayon::ThreadPoolBuilder::new()
          .num_threads(self.threads_per_prover)
          .build()
          .map_err(|e| e.to_string())?;
        let feed = ShardFeed::new(self.threads_per_prover)?;
        Ok(Lane { provers, pool, feed, device })
      })
      .collect()
  }

  fn resident_bytes(&self) -> usize {
    let resident = planning::resident_memory().saturating_mul(5).div_ceil(4);
    usize::try_from(resident).unwrap_or(usize::MAX)
  }

  fn lane_workspace_bytes(&self, _cells: usize) -> Option<usize> {
    Some(self.workspace)
  }

  fn bind(&self, _reservation: &RecordReservation) {}

  fn execute_claim(
    &self,
    _lane: &Lane,
    env: &ixon::Env,
    owned: &[Address],
    expected: &ixon::Claim,
    _budget: Option<usize>,
    reservation: &RecordReservation,
  ) -> Result<ClaimRecord, PrepareFailure> {
    let program = self.systems[0].program().checked();
    let mut report = serde_json::Map::new();
    let assume_binding = expected.context().is_some_and(|c| c.binding_assumed);
    let (args, advice) = leaf_advice(
      env,
      WitnessRequest::ShardCheckEnv { owned, assume_binding },
      expected,
      program.field(),
      reservation,
      &mut report,
    )
    .map_err(prep_failure)?;
    let bound = bind_advice(
      program,
      Kind::Ixvm,
      IXVM_ENTRY.to_owned(),
      &args,
      &advice,
      reservation,
      report,
    )
    .map_err(prep_failure)?;
    drop(advice);
    let (args, record) = self.execute_bound(0, bound, reservation)?;
    let mut claim_bytes = Vec::new();
    expected.put(&mut claim_bytes);
    Ok(ClaimRecord { claim: expected.clone(), claim_bytes, args, record })
  }

  fn execute_aggregate(
    &self,
    _lane: &Lane,
    run: Run<'_, Vec<u64>>,
    slot: usize,
    children: &[Arc<BackendSlot<Self>>],
    reservation: &RecordReservation,
  ) -> Result<Staged, PrepareFailure> {
    let spec = run.specs.get(slot).ok_or("missing aggregate slot spec")?;
    if run.reprove_slot != Some(slot)
      && let Some((proof, address)) = load_cached(
        run.store_dir,
        run.cache_dir,
        slot,
        spec,
        |bytes| self.decode_proof(bytes),
        |outer, proof| self.verify(ChildKind::Aggr, outer, proof),
      )
    {
      return Ok(Staged::Cached(proof, address));
    }
    let shape = spec.shape.ok_or("aggregate proof slot has no shape")?;
    let keys = self.keys();
    let streams = match (spec.op, children) {
      (PlanOp::Join(..), [left, right]) => streams::pair(
        keys,
        shape,
        child(left),
        child(right),
        &spec.statement,
        spec.structural,
        run.owner_by_address,
      )?,
      _ => {
        return Err(
          "the formal backend proves joins of two children; wrap-first leaves are not scheduled"
            .into(),
        );
      },
    };
    let args = self.public_input(&spec.statement.claim_bytes);
    let (args, record) = self.execute_streams(&streams, &args, reservation)?;
    Ok(Staged::Executed { args, record: Box::new(record) })
  }

  fn prove_claim(
    &self,
    lane: &Lane,
    record: ClaimRecord,
  ) -> Result<ProvenClaim<FormalProof>, String> {
    let ClaimRecord { claim, claim_bytes, args, record } = record;
    let proof =
      self.prove(lane, ChildKind::Ixvm, &record, IXVM_ENTRY, &args)?;
    Ok(ProvenClaim { claim, claim_bytes, proof })
  }

  fn prove_aggregate(
    &self,
    lane: &Lane,
    run: Run<'_, Vec<u64>>,
    slot: usize,
    staged: Staged,
  ) -> Result<Arc<BackendSlot<Self>>, String> {
    let spec = run.specs.get(slot).ok_or("missing aggregate slot spec")?;
    let (proof, proof_address) = match staged {
      Staged::Cached(proof, address) => (proof, Some(address)),
      Staged::Executed { args, record } => {
        let proof =
          self.prove(lane, ChildKind::Aggr, &record, AGGR_ENTRY, &args)?;
        drop(record);
        let outer: Vec<u64> = lane.provers[1]
          .claim(AGGR_ENTRY, &args, &[])?
          .iter()
          .map(PrimeField64::as_canonical_u64)
          .collect();
        if outer != spec.outer_claim {
          return Err(
            "aggregate prover returned an unexpected outer claim".into(),
          );
        }
        let address = persist_cached(
          run.store_dir,
          run.cache_dir,
          run.write_outputs,
          slot,
          spec,
          || self.encode_proof(&proof),
        )?;
        (proof, address)
      },
    };
    Ok(Arc::new(BackendSlot::<Self> {
      kind: ChildKind::Aggr,
      statement: spec.statement.clone(),
      outer_claim: spec.outer_claim.clone(),
      proof,
      proof_address,
      claims_bytes: self.identity.claims_bytes(&spec.outer_claim),
    }))
  }

  fn wrap_root(
    &self,
    lane: &Lane,
    _run: Run<'_, Vec<u64>>,
    root: &BackendSlot<Self>,
    proof: &FormalProof,
    reservation: &RecordReservation,
  ) -> Result<FormalProof, String> {
    let streams = streams::wrap(
      self.keys(),
      aggregate_controller::protocol::shape_code(ChildKind::Aggr, None),
      Transport {
        kind: ChildKind::Aggr,
        proof: &proof.raw,
        claims: &root.claims_bytes,
      },
    );
    let args = self.public_input(&root.statement.claim_bytes);
    let (args, record) = self
      .execute_streams(&streams, &args, reservation)
      .map_err(String::from)?;
    self.prove(lane, ChildKind::Aggr, &record, AGGR_ENTRY, &args)
  }

  fn prove_extra(
    &self,
    lane: &Lane,
    node: ExtraNode<'_, FormalProof>,
    reservation: &RecordReservation,
  ) -> Result<FormalProof, String> {
    let keys = self.keys();
    let output = node.output();
    let streams = match node {
      ExtraNode::Discharge { child, binding, output } => streams::discharge(
        keys,
        transport(child),
        child.claim_bytes,
        transport(binding),
        binding.claim_bytes,
        output,
      )?,
      ExtraNode::Catalog { shape, children, output, preimages, trees } => {
        if children.iter().any(|c| c.kind != ChildKind::Aggr) {
          return Err("a catalog join folds aggregate proofs".into());
        }
        streams::catalog(
          keys,
          shape,
          children.map(transport),
          output,
          preimages,
          trees,
        )
      },
    };
    let args = self.public_input(output);
    let (args, record) = self
      .execute_streams(&streams, &args, reservation)
      .map_err(String::from)?;
    drop(streams);
    let proof =
      self.prove(lane, ChildKind::Aggr, &record, AGGR_ENTRY, &args)?;
    drop(record);
    let outer: Vec<u64> = lane.provers[1]
      .claim(AGGR_ENTRY, &args, &[])?
      .iter()
      .map(PrimeField64::as_canonical_u64)
      .collect();
    if outer != self.identity.outer_claim(ChildKind::Aggr, output) {
      return Err("aggregate prover returned an unexpected outer claim".into());
    }
    Ok(proof)
  }

  fn verify(
    &self,
    kind: ChildKind,
    outer: &Vec<u64>,
    proof: &FormalProof,
  ) -> Result<(), String> {
    if proof.kind != kind {
      return Err("proof belongs to the other recursion kind".into());
    }
    let (entry, arity) = match kind {
      ChildKind::Ixvm => (IXVM_ENTRY, 8),
      ChildKind::Aggr => (AGGR_ENTRY, 16),
    };
    let args = outer
      .get(2..)
      .filter(|args| args.len() == arity)
      .ok_or("outer claim has the wrong arity")?;
    let system = &self.systems[index(kind)];
    let verifier = system.verifier();
    let args = system.program().checked().field().decode(args)?;
    let batch =
      BatchProof::from_bytes(&proof.raw).map_err(|e| e.to_string())?;
    verifier.verify_batch(entry, &args, &[], &batch)
  }

  fn verify_on(
    &self,
    _lane: &Lane,
    kind: ChildKind,
    outer: &Vec<u64>,
    proof: &FormalProof,
  ) -> Result<(), String> {
    self.verify(kind, outer, proof)
  }

  fn trace_shards(&self, proof: &FormalProof) -> usize {
    proof.shards
  }

  fn encode_proof(&self, proof: &FormalProof) -> Result<Vec<u8>, String> {
    let mut bytes = magic(proof.kind).to_vec();
    bytes.extend_from_slice(&proof.raw);
    Ok(bytes)
  }

  fn decode_proof(&self, bytes: &[u8]) -> Result<FormalProof, String> {
    let (kind, raw) = if let Some(raw) = bytes.strip_prefix(IXVM_MAGIC) {
      (ChildKind::Ixvm, raw)
    } else if let Some(raw) = bytes.strip_prefix(AGGR_MAGIC) {
      (ChildKind::Aggr, raw)
    } else {
      return Err("not a formal Aiur proof".into());
    };
    let batch = BatchProof::from_bytes(raw).map_err(|e| e.to_string())?;
    if batch.to_bytes().map_err(|e| e.to_string())? != raw {
      return Err("noncanonical or trailing proof bytes".into());
    }
    Ok(FormalProof { kind, raw: raw.into(), shards: batch.proofs.len() })
  }
}

/// `ix aggregate` as configured: the supplied claim proofs, with any
/// supplied or cached aggregates above them, folded on the slot scheduler
/// with the lane controller's fold.
pub struct AggregateConfig {
  pub manifest: PathBuf,
  /// Store addresses of claim proofs and of aggregate proofs of plan slots.
  pub proofs: Vec<Address>,
  pub lanes: usize,
  pub device: Option<i32>,
  pub exec_ahead: usize,
  pub structural_above: usize,
  pub reprove_slot: Option<usize>,
  pub subtree: Option<usize>,
  pub plan_only: bool,
  pub use_cache: bool,
  pub write_outputs: bool,
  pub wrap_root: bool,
  /// The supplied claims assume their role binding.
  pub assume_binding: bool,
  /// The store address of a proof of the environment's `Binding` claim:
  /// the supplied claims assume their binding and the root discharges it.
  pub binding_proof: Option<Address>,
  pub options: Options,
}

fn store_address(hex: &str) -> Result<Address, String> {
  Address::from_hex(hex)
    .ok_or_else(|| format!("expected a 64-character hex address, got {hex}"))
}

/// `ix aggregate` for the formal provers over `env`, the environment Lean
/// checks: the proof it produced, or nothing with `plan_only`.
pub fn aggregate(
  config: &AggregateConfig,
  env: &ixon::Env,
  ixvm: &System,
  aggr: &System,
  binding_proof_bytes: Option<Vec<u8>>,
) -> Result<Option<aggregate_controller::aggregate::Output>, String> {
  let backend = Formal::new(
    ixvm,
    aggr,
    config.lanes,
    config.device,
    config.options.clone(),
  )?;
  let controller = aggregate_controller::aggregate::Config {
    lanes: config.lanes,
    exec_ahead: config.exec_ahead,
    structural_above: config.structural_above,
    reprove_slot: config.reprove_slot,
    subtree: config.subtree,
    plan_only: config.plan_only,
    use_cache: config.use_cache,
    write_outputs: config.write_outputs,
    wrap_root: config.wrap_root,
    assume_binding: config.assume_binding,
    binding_proof: match (&config.binding_proof, binding_proof_bytes) {
      (Some(_), Some(_)) => {
        return Err(
          "a binding proof is either stored or supplied as bytes".into(),
        );
      },
      (Some(address), None) => Some(BindingSource::Stored(address.clone())),
      (None, Some(bytes)) => Some(BindingSource::Bytes(bytes)),
      (None, None) => None,
    },
    store_dir: None,
    cache_dir: None,
  };
  aggregate_controller::aggregate::run(
    &controller,
    &backend,
    env,
    &config.manifest,
    &config.proofs.iter().map(Address::hex).collect::<Vec<_>>().join("\n"),
  )
}

/// `ix prove --lanes` for the formal provers over `env`, the environment
/// Lean checks: the whole run, returning the verified root's store address,
/// or with `claims_only` one `id address` line per proven claim.
pub fn prove_lanes(
  config: &LaneConfig,
  env: &ixon::Env,
  ixvm: &System,
  aggr: &System,
) -> Result<LaneResult, String> {
  let backend = Formal::new(
    ixvm,
    aggr,
    config.lanes,
    config.device,
    config.options.clone(),
  )?;
  let mut controller = lanes::Config::new(
    config.lanes,
    config.max_ram_bytes,
    config.exec_jobs,
    config.structural_above,
  );
  controller.use_cache = config.use_cache;
  controller.use_index = config.use_index;
  controller.out_manifest = config.out_manifest.clone();
  controller.claims_only = config.claims_only;
  controller.select = config.select.clone();
  controller.assume_binding = config.assume_binding;
  controller.binding_proof = config.binding_proof.clone();
  let text = lanes::run(&controller, &backend, env, &config.manifest)?;
  if !config.claims_only {
    return Ok(LaneResult::Root(store_address(text.trim())?));
  }
  text
    .lines()
    .filter(|line| !line.is_empty())
    .map(|line| {
      let (id, address) = line
        .split_once(' ')
        .ok_or_else(|| format!("malformed claim line {line}"))?;
      let id = id.parse::<u32>().map_err(|e| format!("claim id {id}: {e}"))?;
      Ok((id, store_address(address)?))
    })
    .collect::<Result<_, String>>()
    .map(LaneResult::Claims)
}

/// `ix aggregate --ixc` as configured: the catalog's members, in manifest
/// order, and the store addresses of their aggregate roots.
pub struct CatalogConfig {
  pub members: Vec<catalog::Member>,
  pub proofs: Vec<Address>,
  /// The root claim (`Ix.Claim.ser`) the caller's plan reaches.
  pub expected_root: Vec<u8>,
  pub device: Option<i32>,
  pub use_cache: bool,
  pub write_outputs: bool,
  pub options: Options,
}

/// `ix aggregate --ixc` for the formal provers: every join of the catalog's
/// plan, from its members' roots, returning the root proof's store address.
pub fn aggregate_catalog(
  config: &CatalogConfig,
  ixvm: &System,
  aggr: &System,
) -> Result<Address, String> {
  let backend =
    Formal::new(ixvm, aggr, 1, config.device, config.options.clone())?;
  let controller = catalog::Config {
    use_cache: config.use_cache,
    write_outputs: config.write_outputs,
    store_dir: None,
    cache_dir: None,
  };
  let proofs: Vec<String> = config.proofs.iter().map(Address::hex).collect();
  let root = catalog::run(
    &controller,
    &backend,
    &config.members,
    &proofs,
    Some(&config.expected_root),
  )?;
  store_address(root.trim())
}

/// `ix compress` normalization of a formal aggregate root, as configured.
pub struct NormalizeConfig {
  /// The CUDA device to prove on; `None` proves on the CPU.
  pub device: Option<i32>,
  /// Planner options; the layout comes from the normalization's heights.
  pub options: Options,
}

/// Wrap the aggregate root `proof` (an encoded `IXAGGR2` proof) of `claim`
/// once more with `ix_aggr` and prove the wrap as one trace shard with every
/// circuit active at the log2 heights `log_heights`, in system circuit
/// order. Every root that fits those heights then has a proof of one shape,
/// which a verifier circuit fixed in advance checks. The root is verified
/// before it is wrapped and the wrap after it is proved; returns the raw
/// proof of the wrap, whose outer claim is the root's.
pub fn normalize_root(
  config: &NormalizeConfig,
  ixvm: &System,
  aggr: &System,
  log_heights: &[u8],
  claim: &[u8],
  proof: &[u8],
) -> Result<Vec<u8>, String> {
  let mut options = config.options.clone();
  options.fixed_log_heights = Some(log_heights.to_vec());
  let backend = Formal::new(ixvm, aggr, 1, config.device, options)?;
  let root = backend.decode_proof(proof)?;
  if root.kind != ChildKind::Aggr {
    return Err("normalization wraps an aggregate proof".into());
  }
  let outer = backend.outer_claim(ChildKind::Aggr, claim);
  backend
    .verify(ChildKind::Aggr, &outer, &root)
    .map_err(|e| format!("aggregate root: {e}"))?;
  let claims = backend.claims_bytes(&outer);
  let streams = streams::wrap(
    backend.keys(),
    aggregate_controller::protocol::shape_code(ChildKind::Aggr, None),
    Transport { kind: ChildKind::Aggr, proof: &root.raw, claims: &claims },
  );
  let pool = record_pool::RecordPool::new(usize::MAX / 2, 16 << 20);
  let reservation = pool
    .try_admit()
    .map_err(|e| format!("record admission: {e:?}"))?
    .ok_or("record pool refused admission")?;
  let (args, record) = backend
    .execute_streams(&streams, &backend.public_input(claim), &reservation)
    .map_err(String::from)?;
  drop(streams);
  let lanes = backend.lanes(1)?;
  let normalized =
    backend.prove(&lanes[0], ChildKind::Aggr, &record, AGGR_ENTRY, &args)?;
  drop(record);
  backend
    .verify(ChildKind::Aggr, &outer, &normalized)
    .map_err(|e| format!("normalized root: {e}"))?;
  if normalized.shards != 1 {
    return Err(format!(
      "the normalized root has {} trace shards, not one",
      normalized.shards
    ));
  }
  Ok(normalized.raw.to_vec())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn cache_fri_bytes_follow_the_key_layout() {
    let parameters = aiur::trace::stark::Parameters::default();
    let bytes = fri_parameter_bytes(parameters);
    assert_eq!(bytes.len(), 40);
    assert_eq!(&bytes[8..16], &1u64.to_le_bytes());
    assert_eq!(&bytes[16..24], &(parameters.num_queries as u64).to_le_bytes());
  }

  #[test]
  fn magic_prefixes_select_the_kind() {
    assert_eq!(magic(ChildKind::Ixvm), b"IXAIUR2\0");
    assert_eq!(magic(ChildKind::Aggr), b"IXAGGR2\0");
  }
}
