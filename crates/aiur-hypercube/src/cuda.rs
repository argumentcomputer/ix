//! GPU proving via the open-source `sp1-gpu` prover (feature `cuda`).
//!
//! `sp1-gpu`'s `CudaShardProver` is machine-generic: each chip's AIR is
//! compiled once to a flat bytecode which fused CUDA kernels interpret, so
//! Aiur's chips need no per-chip kernels. The integration surface is
//! exactly three pieces:
//!
//! - [`CudaTracegenAir`] for [`AiurAir`], entirely defaulted: Aiur traces
//!   are built on the host (they live in the record), and the trait's
//!   defaults declare no device tracegen, which selects the host-trace
//!   upload path.
//! - [`AiurCudaComponents`], choosing the stock Poseidon2 Merkle prover,
//!   jagged PCS and device challenger — only `Air` differs from SP1's own
//!   configuration.
//! - [`prove`], a drop-in sibling of [`crate::prover::prove`]: the
//!   `CudaShardProver` implements the same `AirProver` interface the CPU
//!   prover does, so it slots into `SimpleProver` and the identical
//!   setup/prove-shard flow. Proofs and verifying keys are byte-identical
//!   in type to the CPU path's; verification is unchanged.
//!
//! This module type-checks without a GPU, but *building* it compiles
//! `sp1-gpu-sys`'s kernels and needs the CUDA toolchain (`nvcc`); set
//! `CUDA_ARCHS` (e.g. `89` for Ada, `90` for Hopper, `120` for Blackwell)
//! to avoid compiling kernels for every architecture. At runtime,
//! `IX_HC_GPU=1` routes [`crate::prover::prove`] through here.
//!
//! Two `sp1-gpu` crates are vendored under `crates/vendor/` (workspace
//! `[patch.crates-io]`) because their upstream releases are sized and
//! shaped for SP1's RISC-V machine: `sp1-gpu-jagged-tracegen` bounds a
//! shard's total column count at 2^14 (Aiur's IxVM kernel machine has ~85k),
//! and `sp1-gpu-zerocheck` assumed a single preprocessed-padding column,
//! which only holds when `max_log_row_count >= log_stacking_height` — with
//! Aiur's defaults (20 < 21) every main chip's columns were shifted and the
//! verifier rejected the proof. See the vendored crates' READMEs.

use std::collections::BTreeMap;
use std::sync::Arc;

use slop_basefold::FriConfig;
use slop_futures::queue::WorkerQueue;
use sp1_gpu_basefold::FriCudaProver;
use sp1_gpu_challenger::DuplexChallenger;
use sp1_gpu_cudart::{PinnedBuffer, TaskScope, run_in_place};
use sp1_gpu_logup_gkr::Interactions;
use sp1_gpu_merkle_tree::{CudaTcsProver, Poseidon2SP1Field16CudaProver};
use sp1_gpu_shard_prover::{CudaShardProver, CudaShardProverComponents};
use sp1_gpu_tracegen::CudaTracegenAir;
use sp1_hypercube::{
  MachineProof, MachineVerifier, SP1InnerPcs,
  air::MachineAir,
  prover::{SimpleProver, shape_from_record},
};
use sp1_primitives::{
  SP1GlobalContext,
  fri_params::{SP1_PROOF_OF_WORK_BITS, unique_decoding_queries},
};

use crate::{
  F,
  air::AiurAir,
  machine::AiurMachine,
  prover::{AiurProof, AiurVerifyingKey, ProverParams, shard_verifier},
  record::{AiurProgram, AiurRecord},
};

// Aiur traces are host-built; the defaults select the host upload path.
impl CudaTracegenAir<F> for AiurAir {}

/// The `sp1-gpu` component selection for the Aiur machine: SP1's stock
/// Poseidon2-Merkle tensor prover, jagged PCS and device challenger, with
/// [`AiurAir`] as the machine's AIR.
pub struct AiurCudaComponents;

impl CudaShardProverComponents<SP1GlobalContext> for AiurCudaComponents {
  type P = Poseidon2SP1Field16CudaProver;
  type Air = AiurAir;
  type C = SP1InnerPcs;
  type DeviceChallenger = DuplexChallenger<F, TaskScope>;
}

/// Proves an execution's shards on the GPU, returning the verifying key and
/// the proof — the same types [`crate::prover::prove`] returns, verified by
/// the same [`crate::prover::verify`].
pub fn prove(
  machine: &AiurMachine,
  records: Vec<AiurRecord>,
  params: ProverParams,
) -> (AiurVerifyingKey, AiurProof) {
  // Trace-buffer capacity. One dense buffer (and one pinned host buffer)
  // holds the preprocessed traces followed by a shard's main traces, each
  // section zero-padded to a multiple of the stacking height, so it must
  // fit the preprocessed area plus the largest shard's main area. Setup
  // generates every chip's preprocessed trace regardless of the record, so
  // that area comes from the machine; the main area comes from
  // `shape_from_record` (already rounded to the stacking height). One extra
  // stacked column of headroom.
  let stacking = 1usize << params.log_stacking_height;
  let preprocessed_area = machine
    .machine()
    .chips()
    .iter()
    .map(|chip| {
      chip.preprocessed_width()
        * chip.preprocessed_num_rows(&AiurProgram).unwrap_or_default()
    })
    .sum::<usize>()
    .next_multiple_of(stacking);
  let mv = MachineVerifier::new(shard_verifier(machine, params));
  let main_area = records
    .iter()
    .filter_map(|record| shape_from_record(&mv, record))
    .map(|shape| shape.main_area)
    .max()
    .unwrap_or(stacking);
  let capacity = preprocessed_area + main_area + stacking;
  let capacity = std::env::var("IX_HC_GPU_TRACE_CAP")
    .ok()
    .and_then(|v| v.parse().ok())
    .unwrap_or(capacity);

  let verifier = shard_verifier(machine, params);
  let chips = machine.machine().clone();
  let runtime = tokio::runtime::Runtime::new().expect("tokio runtime");
  runtime.block_on(async move {
    let (tx, rx) = std::sync::mpsc::channel();
    run_in_place(move |scope| async move {
      let fri_config = FriConfig::new(
        params.log_blowup,
        unique_decoding_queries(params.log_blowup),
        SP1_PROOF_OF_WORK_BITS,
      );
      let basefold = FriCudaProver::<SP1GlobalContext, _, F>::new(
        Poseidon2SP1Field16CudaProver::new(&scope),
        fri_config,
        params.log_stacking_height,
      );
      let mut all_interactions = BTreeMap::new();
      for chip in chips.chips().iter() {
        let host = Interactions::new(chip.sends(), chip.receives());
        let device = host.copy_to_device(&scope).expect("interaction upload");
        all_interactions.insert(chip.name().to_string(), Arc::new(device));
      }
      let buffers =
        Arc::new(WorkerQueue::new(vec![PinnedBuffer::<F>::with_capacity(
          capacity,
        )]));
      let cuda = CudaShardProver::<SP1GlobalContext, AiurCudaComponents>::new(
        buffers,
        u32::try_from(params.max_log_row_count).expect("max_log_row_count"),
        basefold,
        chips,
        capacity,
        scope.clone(),
        all_interactions,
        false,
        false,
      );
      let prover = SimpleProver::new(verifier, cuda);
      let (pk, vk) = prover.setup(Arc::new(AiurProgram)).await;
      // SAFETY: the preprocessed data was produced by this very prover.
      let pk = unsafe { pk.into_inner() };
      let mut shard_proofs = Vec::with_capacity(records.len());
      for record in records {
        shard_proofs.push(prover.prove_shard(pk.clone(), record).await);
      }
      let _ = tx.send((vk, MachineProof { shard_proofs }));
    })
    .await;
    rx.recv().expect("gpu prove result")
  })
}
