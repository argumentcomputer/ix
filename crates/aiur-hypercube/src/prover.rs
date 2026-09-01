//! Proving and verifying an [`AiurMachine`] shard with the Hypercube CPU
//! prover.

use std::sync::Arc;

use slop_basefold::FriConfig;
use sp1_hypercube::{
  MachineProof, MachineVerifier, MachineVerifierConfigError,
  MachineVerifyingKey, SP1InnerPcs, SP1PcsProofInner, ShardVerifier,
  prover::simple_prover,
};
use sp1_primitives::{
  SP1GlobalContext,
  fri_params::{SP1_PROOF_OF_WORK_BITS, unique_decoding_queries},
};

use crate::{
  air::AiurAir,
  machine::AiurMachine,
  record::{AiurProgram, AiurRecord},
};

/// Hypercube PCS parameters.
#[derive(Clone, Copy, Debug)]
pub struct ProverParams {
  pub log_blowup: usize,
  /// Traces are stacked into columns of `2^log_stacking_height` elements.
  pub log_stacking_height: u32,
  /// No chip may have more than `2^max_log_row_count` rows.
  pub max_log_row_count: usize,
}

impl Default for ProverParams {
  fn default() -> Self {
    Self { log_blowup: 1, log_stacking_height: 21, max_log_row_count: 20 }
  }
}

pub type AiurVerifyingKey = MachineVerifyingKey<SP1GlobalContext>;
pub type AiurProof = MachineProof<SP1GlobalContext, SP1PcsProofInner>;
pub type AiurVerifyError =
  MachineVerifierConfigError<SP1GlobalContext, SP1InnerPcs>;

fn shard_verifier(
  machine: &AiurMachine,
  params: ProverParams,
) -> ShardVerifier<SP1GlobalContext, sp1_hypercube::InnerSC<AiurAir>> {
  let fri_config = FriConfig::new(
    params.log_blowup,
    unique_decoding_queries(params.log_blowup),
    SP1_PROOF_OF_WORK_BITS,
  );
  ShardVerifier::from_basefold_parameters(
    fri_config,
    params.log_stacking_height,
    params.max_log_row_count,
    machine.machine().clone(),
  )
}

/// Proves one shard, returning the verifying key and the proof.
pub fn prove(
  machine: &AiurMachine,
  record: AiurRecord,
  params: ProverParams,
) -> (AiurVerifyingKey, AiurProof) {
  let verifier = shard_verifier(machine, params);
  let runtime = tokio::runtime::Runtime::new().expect("tokio runtime");
  runtime.block_on(async move {
    let prover = simple_prover(verifier);
    let (pk, vk) = prover.setup(Arc::new(AiurProgram)).await;
    // SAFETY: the preprocessed data was produced by this very prover.
    let pk = unsafe { pk.into_inner() };
    let shard_proof = prover.prove_shard(pk, record).await;
    (vk, MachineProof { shard_proofs: vec![shard_proof] })
  })
}

/// Verifies a proof against the machine and verifying key.
pub fn verify(
  machine: &AiurMachine,
  params: ProverParams,
  vk: &AiurVerifyingKey,
  proof: &AiurProof,
) -> Result<(), AiurVerifyError> {
  MachineVerifier::new(shard_verifier(machine, params)).verify(vk, proof)
}
