//! GPU proving of the recursion tail via the open-source `sp1-gpu` prover
//! (feature `cuda`, selected at runtime by `IX_HC_GPU=1`; `IX_REC_GPU=0`
//! keeps the tail on the CPU while the Hypercube stage runs on the GPU).
//!
//! SP1's recursion chips already have device trace generation
//! (`sp1-gpu-tracegen`'s `recursion` module implements `CudaTracegenAir` for
//! `RecursionAir`), and its jagged-PCS, LogUp-GKR and zerocheck kernels are
//! machine-generic, so the four recursion machines of the pipeline are
//! proven by the same `CudaShardProver` the Hypercube stage uses
//! (`aiur_hypercube::cuda`), with two component selections:
//!
//! - [`InnerCudaComponents`] for the leaf, compress and shrink machines —
//!   KoalaBear Poseidon2 Merkle trees and the duplex challenger (SP1's
//!   `CompressAir` and `ShrinkAir` are the same AIR type; the three levels
//!   differ in their PCS parameters, so each gets its own prover);
//! - [`OuterCudaComponents`] for the BN254 wrap machine — Poseidon2 over
//!   BN254 and the multi-field challenger.
//!
//! **Lifetime.** A `TaskScope` is only valid inside the closure
//! `run_in_place` runs, so a proof-per-`run_in_place` design would rebuild
//! the provers (machine bytecode, interactions, pinned buffers) for every
//! one of the hundreds of leaf and compose proofs of a large execution.
//! Instead [`GpuRecursion`] owns one worker thread that enters a single
//! scope for its whole life and serves [`Job`]s from a channel; the
//! pipeline's proving calls block on a reply. The provers are built lazily
//! per level and grown when a program needs a larger trace buffer.
//!
//! **Keys.** Setup runs on the GPU too, and the pipeline's allowlist check
//! (`AiurRecursionProver::prove` compares each proof's verifying key against
//! the setup-time one) holds across CPU- and GPU-computed keys: both commit
//! to the same preprocessed traces under the same PCS.

use std::{collections::BTreeMap, sync::Arc, time::Instant};

use anyhow::{Result, anyhow};
use slop_air::BaseAir;
use slop_basefold::FriConfig;
use slop_bn254::Bn254Fr;
use slop_futures::queue::WorkerQueue;
use sp1_gpu_basefold::FriCudaProver;
use sp1_gpu_challenger::{DuplexChallenger, MultiField32Challenger};
use sp1_gpu_cudart::{PinnedBuffer, TaskScope, run_in_place};
use sp1_gpu_logup_gkr::Interactions;
use sp1_gpu_merkle_tree::{
  CudaTcsProver, Poseidon2Bn254CudaProver, Poseidon2SP1Field16CudaProver,
};
use sp1_gpu_shard_prover::{CudaShardProver, CudaShardProverComponents};
use sp1_hypercube::{
  Machine, MachineVerifyingKey, SP1InnerPcs, SP1OuterPcs, SP1PcsProofInner,
  SP1PcsProofOuter, ShardProof, ShardVerifier,
  air::MachineAir,
  prover::{ProvingKey, SimpleProver},
};
use sp1_primitives::{SP1Field, SP1GlobalContext, SP1OuterGlobalContext};
use sp1_prover::{CompressAir, RecursionSC, WrapAir, WrapSC};
use sp1_recursion_executor::{ExecutionRecord, RecursionProgram};

type F = SP1Field;
type Program = Arc<RecursionProgram<F>>;
type Record = ExecutionRecord<F>;

pub type InnerVk = MachineVerifyingKey<SP1GlobalContext>;
pub type InnerProof = ShardProof<SP1GlobalContext, SP1PcsProofInner>;
pub type OuterVk = MachineVerifyingKey<SP1OuterGlobalContext>;
pub type OuterProof = ShardProof<SP1OuterGlobalContext, SP1PcsProofOuter>;

/// The `sp1-gpu` component selection for SP1's KoalaBear recursion
/// machines (leaf, compress, shrink).
pub struct InnerCudaComponents;

impl CudaShardProverComponents<SP1GlobalContext> for InnerCudaComponents {
  type P = Poseidon2SP1Field16CudaProver;
  type Air = CompressAir<F>;
  type C = SP1InnerPcs;
  type DeviceChallenger = DuplexChallenger<F, TaskScope>;
}

/// The `sp1-gpu` component selection for SP1's BN254 wrap machine.
pub struct OuterCudaComponents;

impl CudaShardProverComponents<SP1OuterGlobalContext> for OuterCudaComponents {
  type P = Poseidon2Bn254CudaProver;
  type Air = WrapAir<F>;
  type C = SP1OuterPcs;
  type DeviceChallenger = MultiField32Challenger<F, Bn254Fr, TaskScope>;
}

/// The KoalaBear recursion levels, each its own machine configuration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
  Leaf,
  Compress,
  Shrink,
}

/// One machine configuration: its verifier (machine, stacking height, row
/// cap) and FRI parameters.
pub struct Config<
  GC: slop_challenger::IopCtx,
  SC: sp1_hypercube::ShardContext<GC>,
> {
  pub verifier: ShardVerifier<GC, SC>,
  pub fri: FriConfig<GC::F>,
}

// Not derived: the derive would demand `SC: Clone`, which the shard context
// types are not; the verifier itself is.
impl<GC: slop_challenger::IopCtx, SC: sp1_hypercube::ShardContext<GC>> Clone
  for Config<GC, SC>
{
  fn clone(&self) -> Self {
    Self { verifier: self.verifier.clone(), fri: self.fri }
  }
}

/// The four machine configurations of the pipeline.
pub struct Machines {
  pub leaf: Config<SP1GlobalContext, RecursionSC>,
  pub compress: Config<SP1GlobalContext, RecursionSC>,
  pub shrink: Config<SP1GlobalContext, RecursionSC>,
  pub wrap: Config<SP1OuterGlobalContext, WrapSC>,
}

impl Machines {
  fn inner(&self, level: Level) -> &Config<SP1GlobalContext, RecursionSC> {
    match level {
      Level::Leaf => &self.leaf,
      Level::Compress => &self.compress,
      Level::Shrink => &self.shrink,
    }
  }
}

type Reply<T> = std::sync::mpsc::Sender<T>;

enum Job {
  /// Setup (`record: None`, returns the key) or setup-and-prove on a
  /// KoalaBear level.
  Inner {
    level: Level,
    program: Program,
    record: Option<Record>,
    reply: Reply<(InnerVk, Option<InnerProof>)>,
  },
  /// Setup-and-prove on the BN254 wrap machine.
  Outer {
    program: Program,
    record: Record,
    reply: Reply<(OuterVk, OuterProof)>,
  },
}

/// The GPU worker: one thread, one CUDA task scope, lazily built provers.
pub struct GpuRecursion {
  tx: Option<tokio::sync::mpsc::UnboundedSender<Job>>,
  thread: Option<std::thread::JoinHandle<()>>,
}

impl GpuRecursion {
  /// Whether the environment selects GPU proving of the recursion tail:
  /// `IX_HC_GPU` set and `IX_REC_GPU` not `0`.
  pub fn selected() -> bool {
    std::env::var_os("IX_HC_GPU").is_some()
      && !std::env::var("IX_REC_GPU").is_ok_and(|v| v == "0")
  }

  /// Start the worker for these machine configurations.
  pub fn start(machines: Machines) -> Result<Self> {
    let (tx, rx) = tokio::sync::mpsc::unbounded_channel::<Job>();
    let thread = std::thread::Builder::new()
      .name("aiur-recursion-gpu".into())
      .spawn(move || {
        let runtime = tokio::runtime::Runtime::new().expect("tokio runtime");
        runtime.block_on(async move {
          run_in_place(move |scope| async move {
            Worker::new(machines, scope).serve(rx).await;
          })
          .await;
        });
      })?;
    Ok(Self { tx: Some(tx), thread: Some(thread) })
  }

  fn send(&self, job: Job) -> Result<()> {
    self
      .tx
      .as_ref()
      .expect("worker channel")
      .send(job)
      .map_err(|_closed| anyhow!("the GPU recursion worker is gone"))
  }

  /// The verifying key of `program` on the machine of `level`.
  pub fn setup_inner(&self, level: Level, program: Program) -> Result<InnerVk> {
    let (reply, rx) = std::sync::mpsc::channel();
    self.send(Job::Inner { level, program, record: None, reply })?;
    let (vk, _) =
      rx.recv().map_err(|_closed| anyhow!("the GPU recursion worker died"))?;
    Ok(vk)
  }

  /// Setup and prove `record` (an execution of `program`) on the machine of
  /// `level`.
  pub fn prove_inner(
    &self,
    level: Level,
    program: Program,
    record: Record,
  ) -> Result<(InnerVk, InnerProof)> {
    let (reply, rx) = std::sync::mpsc::channel();
    self.send(Job::Inner { level, program, record: Some(record), reply })?;
    let (vk, proof) =
      rx.recv().map_err(|_closed| anyhow!("the GPU recursion worker died"))?;
    Ok((vk, proof.expect("a prove job returns a proof")))
  }

  /// Setup and prove `record` on the BN254 wrap machine.
  pub fn prove_outer(
    &self,
    program: Program,
    record: Record,
  ) -> Result<(OuterVk, OuterProof)> {
    let (reply, rx) = std::sync::mpsc::channel();
    self.send(Job::Outer { program, record, reply })?;
    rx.recv().map_err(|_closed| anyhow!("the GPU recursion worker died"))
  }
}

impl Drop for GpuRecursion {
  fn drop(&mut self) {
    // Closing the channel ends the worker's loop; the scope is left cleanly.
    drop(self.tx.take());
    if let Some(thread) = self.thread.take() {
      let _ = thread.join();
    }
  }
}

type InnerProver = SimpleProver<
  SP1GlobalContext,
  RecursionSC,
  CudaShardProver<SP1GlobalContext, InnerCudaComponents>,
>;
type OuterProver = SimpleProver<
  SP1OuterGlobalContext,
  WrapSC,
  CudaShardProver<SP1OuterGlobalContext, OuterCudaComponents>,
>;

/// Proving keys kept per prover: a proof's setup (preprocessed trace
/// generation and commitment) is skipped when the program was proven
/// before, which is every leaf and compose proof after the first of its
/// kind. Bounded, since a key holds its level's trace buffer on the device.
const MAX_CACHED_KEYS: usize = 4;

/// A prover with the trace-buffer capacity it was built for and the proving
/// keys it set up, by program (the pipeline keeps one `Arc` per program).
struct Built<P, K> {
  capacity: usize,
  prover: P,
  keys: Vec<(Program, Arc<K>)>,
}

type InnerKey = ProvingKey<
  SP1GlobalContext,
  RecursionSC,
  CudaShardProver<SP1GlobalContext, InnerCudaComponents>,
>;
type OuterKey = ProvingKey<
  SP1OuterGlobalContext,
  WrapSC,
  CudaShardProver<SP1OuterGlobalContext, OuterCudaComponents>,
>;

struct Worker {
  machines: Machines,
  scope: TaskScope,
  /// The recursion chips' interactions on the device (the three KoalaBear
  /// levels share one machine's chip set).
  inner_interactions: BTreeMap<String, Arc<Interactions<F, TaskScope>>>,
  inner: BTreeMap<Level, Built<InnerProver, InnerKey>>,
  outer: Option<Built<OuterProver, OuterKey>>,
}

impl Worker {
  fn new(machines: Machines, scope: TaskScope) -> Self {
    let inner_interactions =
      device_interactions(machines.compress.verifier.machine(), &scope);
    Self {
      machines,
      scope,
      inner_interactions,
      inner: BTreeMap::new(),
      outer: None,
    }
  }

  async fn serve(mut self, mut rx: tokio::sync::mpsc::UnboundedReceiver<Job>) {
    while let Some(job) = rx.recv().await {
      match job {
        Job::Inner { level, program, record, reply } => {
          let result = self.inner(level, program, record).await;
          let _ = reply.send(result);
        },
        Job::Outer { program, record, reply } => {
          let result = self.outer(program, record).await;
          let _ = reply.send(result);
        },
      }
    }
  }

  async fn inner(
    &mut self,
    level: Level,
    program: Program,
    record: Option<Record>,
  ) -> (InnerVk, Option<InnerProof>) {
    let config = self.machines.inner(level).clone();
    let needed = trace_capacity(
      config.verifier.machine(),
      config.verifier.log_stacking_height(),
      &program,
      record.as_ref(),
    );
    let rebuild = self.inner.get(&level).is_none_or(|p| p.capacity < needed);
    if rebuild {
      let capacity = needed
        .max(self.inner.get(&level).map(|p| p.capacity).unwrap_or_default());
      debug(&format!(
        "gpu recursion: building the {level:?} prover (trace buffer {capacity} \
         felts, stacking 2^{}, row cap 2^{})",
        config.verifier.log_stacking_height(),
        config.verifier.max_log_row_count()
      ));
      // Drop the old prover (and its pinned buffer) before allocating.
      self.inner.remove(&level);
      let prover =
        build_inner(&self.scope, &config, &self.inner_interactions, capacity);
      self.inner.insert(level, Built { capacity, prover, keys: Vec::new() });
    }
    let built = self.inner.get_mut(&level).expect("prover built above");
    let start = Instant::now();
    let result = match record {
      None => {
        let (_, vk) = built.prover.setup(program).await;
        (vk, None)
      },
      Some(record) => {
        let pk = match built.keys.iter().find(|(p, _)| Arc::ptr_eq(p, &program))
        {
          Some((_, pk)) => pk.clone(),
          None => {
            let (pk, _) = built.prover.setup(program.clone()).await;
            // SAFETY: the preprocessed data was produced by this very prover.
            let pk = unsafe { pk.into_inner() };
            if built.keys.len() >= MAX_CACHED_KEYS {
              built.keys.clear();
            }
            built.keys.push((program, pk.clone()));
            pk
          },
        };
        let vk = pk.vk.clone();
        let proof = built.prover.prove_shard(pk, record).await;
        (vk, Some(proof))
      },
    };
    debug(&format!(
      "gpu recursion: {level:?} {} in {:.2?}",
      if result.1.is_some() { "prove" } else { "setup" },
      start.elapsed()
    ));
    result
  }

  async fn outer(
    &mut self,
    program: Program,
    record: Record,
  ) -> (OuterVk, OuterProof) {
    let config = self.machines.wrap.clone();
    let needed = trace_capacity(
      config.verifier.machine(),
      config.verifier.log_stacking_height(),
      &program,
      Some(&record),
    );
    if self.outer.as_ref().is_none_or(|p| p.capacity < needed) {
      let capacity =
        needed.max(self.outer.as_ref().map(|p| p.capacity).unwrap_or_default());
      debug(&format!(
        "gpu recursion: building the wrap prover (trace buffer {capacity} \
         felts)"
      ));
      self.outer = None;
      let interactions =
        device_interactions(config.verifier.machine(), &self.scope);
      let prover = build_outer(&self.scope, &config, &interactions, capacity);
      self.outer = Some(Built { capacity, prover, keys: Vec::new() });
    }
    let start = Instant::now();
    let result = self
      .outer
      .as_ref()
      .expect("wrap prover")
      .prover
      .setup_and_prove_shard(program, None, record)
      .await;
    debug(&format!("gpu recursion: wrap prove in {:.2?}", start.elapsed()));
    result
  }
}

fn debug(msg: &str) {
  if std::env::var_os("IX_HC_DEBUG").is_some() {
    eprintln!("{msg}");
  }
}

/// The chips' interactions, uploaded to the device.
fn device_interactions<A: MachineAir<F>>(
  machine: &Machine<F, A>,
  scope: &TaskScope,
) -> BTreeMap<String, Arc<Interactions<F, TaskScope>>> {
  let mut all = BTreeMap::new();
  for chip in machine.chips().iter() {
    let host = Interactions::new(chip.sends(), chip.receives());
    let device = host.copy_to_device(scope).expect("interaction upload");
    all.insert(chip.name().to_string(), Arc::new(device));
  }
  all
}

/// The trace-buffer capacity a setup (`record: None`) or a proof of
/// `program` needs: the preprocessed section plus the main section, each
/// zero-padded to a multiple of the stacking height, plus one stacked column
/// of headroom. Recursion chips size their traces from the program's pinned
/// shape when it has one (`num_rows`), exactly as the tracegen does.
fn trace_capacity<A>(
  machine: &Machine<F, A>,
  log_stacking_height: u32,
  program: &RecursionProgram<F>,
  record: Option<&Record>,
) -> usize
where
  A: MachineAir<F, Program = RecursionProgram<F>, Record = Record>,
{
  let stacking = 1usize << log_stacking_height;
  let preprocessed: usize = machine
    .chips()
    .iter()
    .map(|chip| {
      chip.preprocessed_width()
        * chip.preprocessed_num_rows(program).unwrap_or_default()
    })
    .sum();
  let main: usize = record
    .map(|record| {
      machine
        .chips()
        .iter()
        .filter(|chip| chip.included(record))
        .map(|chip| chip.width() * chip.num_rows(record).unwrap_or_default())
        .sum()
    })
    .unwrap_or_default();
  preprocessed.next_multiple_of(stacking)
    + main.next_multiple_of(stacking)
    + stacking
}

fn build_inner(
  scope: &TaskScope,
  config: &Config<SP1GlobalContext, RecursionSC>,
  interactions: &BTreeMap<String, Arc<Interactions<F, TaskScope>>>,
  capacity: usize,
) -> InnerProver {
  let basefold = FriCudaProver::<SP1GlobalContext, _, F>::new(
    Poseidon2SP1Field16CudaProver::new(scope),
    config.fri,
    config.verifier.log_stacking_height(),
  );
  let buffers =
    Arc::new(WorkerQueue::new(vec![PinnedBuffer::<F>::with_capacity(
      capacity,
    )]));
  let cuda = CudaShardProver::<SP1GlobalContext, InnerCudaComponents>::new(
    buffers,
    u32::try_from(config.verifier.max_log_row_count())
      .expect("max_log_row_count"),
    basefold,
    config.verifier.machine().clone(),
    capacity,
    scope.clone(),
    interactions.clone(),
    false,
    false,
  );
  SimpleProver::new(config.verifier.clone(), cuda)
}

fn build_outer(
  scope: &TaskScope,
  config: &Config<SP1OuterGlobalContext, WrapSC>,
  interactions: &BTreeMap<String, Arc<Interactions<F, TaskScope>>>,
  capacity: usize,
) -> OuterProver {
  let basefold = FriCudaProver::<SP1OuterGlobalContext, _, F>::new(
    Poseidon2Bn254CudaProver::new(scope),
    config.fri,
    config.verifier.log_stacking_height(),
  );
  let buffers =
    Arc::new(WorkerQueue::new(vec![PinnedBuffer::<F>::with_capacity(
      capacity,
    )]));
  let cuda = CudaShardProver::<SP1OuterGlobalContext, OuterCudaComponents>::new(
    buffers,
    u32::try_from(config.verifier.max_log_row_count())
      .expect("max_log_row_count"),
    basefold,
    config.verifier.machine().clone(),
    capacity,
    scope.clone(),
    interactions.clone(),
    false,
    false,
  );
  SimpleProver::new(config.verifier.clone(), cuda)
}
