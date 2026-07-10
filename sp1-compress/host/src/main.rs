//! `sp1-compress-host`: wrap an Aiur multi-STARK proof in an SP1 proof to
//! compress it.
//!
//! The Aiur/multi-STARK proofs the Ix pipeline produces are large (MBs); this
//! host runs the multi-stark verifier inside an SP1 guest and asks SP1 for a
//! recursive proof of that verification — constant-size `compressed` by
//! default, or `groth16`/`plonk` for onchain-sized proofs (needs Docker or a
//! native gnark build).
//!
//! Two ways in:
//!   `demo`      — hand-built Aiur program, proved here, then compressed;
//!                 exercises the whole chain with no Lean involvement.
//!   `compress`  — consume artifact files from the real pipeline:
//!                 `--vk` (aiur::vk_codec::aiur_system_to_bytes bytes),
//!                 `--claim` (canonical u64 LE Goldilocks elements),
//!                 `--proof` (multi_stark Proof::to_bytes bytes).
//!
//! The real pipeline is also reachable without artifact files via
//! `ix compress <proof-hex>` (see `Ix/Cli/CompressCmd.lean`), which drives
//! this crate's library through FFI.

mod demo;

use std::path::PathBuf;

use aiur::{
  G,
  execute::IOBuffer,
  synthesis::AiurSystem,
  vk_codec::{AiurVerifyingKey, aiur_system_to_bytes},
};
use anyhow::{Context, Result, bail};
use clap::{Args, Parser, Subcommand};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::{CommitmentParameters, FriParameters},
};
use sp1_compress_host::{Mode, run_sp1};

#[derive(Parser)]
#[command(
  name = "sp1-compress-host",
  about = "Compress Aiur multi-STARK proofs via SP1 recursion"
)]
struct Cli {
  #[command(subcommand)]
  command: Command,
}

#[derive(Subcommand)]
enum Command {
  /// Prove a small built-in Aiur program, then compress that proof in SP1.
  Demo {
    #[command(flatten)]
    fri: FriArgs,
    #[command(flatten)]
    sp1: Sp1Args,
    /// Write the intermediate artifacts (vk.bin, claim.bin, proof.bin) here,
    /// in the exact format the `compress` subcommand consumes.
    #[arg(long)]
    save_artifacts: Option<PathBuf>,
  },
  /// Compress an existing Aiur proof from artifact files.
  Compress {
    /// Verifying key bytes (`aiur::vk_codec::aiur_system_to_bytes`).
    #[arg(long)]
    vk: PathBuf,
    /// Claim: one canonical u64 LE per Goldilocks element.
    #[arg(long)]
    claim: PathBuf,
    /// Proof bytes (`multi_stark::prover::Proof::to_bytes`).
    #[arg(long)]
    proof: PathBuf,
    #[command(flatten)]
    fri: FriArgs,
    #[command(flatten)]
    sp1: Sp1Args,
  },
}

/// FRI parameters. Defaults match `ix prove` / `ix verify`
/// (`Ix/Cli/ProveCmd.lean`); they MUST match the proving side or
/// verification fails.
#[derive(Args)]
struct FriArgs {
  #[arg(long, default_value_t = 0)]
  log_final_poly_len: usize,
  #[arg(long, default_value_t = 1)]
  max_log_arity: usize,
  #[arg(long, default_value_t = 100)]
  num_queries: usize,
  #[arg(long, default_value_t = 20)]
  commit_pow_bits: usize,
  #[arg(long, default_value_t = 0)]
  query_pow_bits: usize,
}

impl FriArgs {
  fn to_parameters(&self) -> FriParameters {
    FriParameters {
      log_final_poly_len: self.log_final_poly_len,
      max_log_arity: self.max_log_arity,
      num_queries: self.num_queries,
      commit_proof_of_work_bits: self.commit_pow_bits,
      query_proof_of_work_bits: self.query_pow_bits,
    }
  }
}

#[derive(Args)]
struct Sp1Args {
  /// SP1 stage: execute | core | compressed | groth16 | plonk.
  /// `execute` only emulates (cycle counts, no proof); `groth16`/`plonk`
  /// additionally need Docker or a native gnark build.
  #[arg(long, default_value = "compressed")]
  mode: String,
  /// Write the SP1 proof here (bincode, the SDK's `.save()` format).
  #[arg(long)]
  output: Option<PathBuf>,
}

#[tokio::main]
async fn main() -> Result<()> {
  sp1_sdk::utils::setup_logger();
  let cli = Cli::parse();
  match cli.command {
    Command::Demo { fri, sp1, save_artifacts } => {
      let (vk_bytes, claim_bytes, proof_bytes) = prove_demo(&fri)?;
      if let Some(dir) = save_artifacts {
        std::fs::create_dir_all(&dir)?;
        std::fs::write(dir.join("vk.bin"), &vk_bytes)?;
        std::fs::write(dir.join("claim.bin"), &claim_bytes)?;
        std::fs::write(dir.join("proof.bin"), &proof_bytes)?;
        println!("artifacts written to {}", dir.display());
      }
      let mode: Mode =
        sp1.mode.parse().map_err(|e: String| anyhow::anyhow!(e))?;
      run_sp1(
        vk_bytes,
        claim_bytes,
        proof_bytes,
        &fri.to_parameters(),
        mode,
        sp1.output.as_deref(),
      )
      .await
    },
    Command::Compress { vk, claim, proof, fri, sp1 } => {
      let vk_bytes =
        std::fs::read(&vk).with_context(|| format!("read {}", vk.display()))?;
      let claim_bytes = std::fs::read(&claim)
        .with_context(|| format!("read {}", claim.display()))?;
      let proof_bytes = std::fs::read(&proof)
        .with_context(|| format!("read {}", proof.display()))?;
      // Fail fast on bad artifacts before paying for SP1 setup: the guest
      // would reject them anyway, but natively the error is immediate.
      let key = AiurVerifyingKey::from_bytes(&vk_bytes)
        .map_err(|e| anyhow::anyhow!("bad verifying key: {e}"))?;
      let claim_elts = decode_claim(&claim_bytes)?;
      let inner_proof = multi_stark::prover::Proof::from_bytes(&proof_bytes)
        .map_err(|e| anyhow::anyhow!("bad proof: {e}"))?;
      let fri_params = fri.to_parameters();
      let vk_fri = key.fri_parameters();
      if (
        fri_params.log_final_poly_len,
        fri_params.max_log_arity,
        fri_params.num_queries,
        fri_params.commit_proof_of_work_bits,
        fri_params.query_proof_of_work_bits,
      ) != (
        vk_fri.log_final_poly_len,
        vk_fri.max_log_arity,
        vk_fri.num_queries,
        vk_fri.commit_proof_of_work_bits,
        vk_fri.query_proof_of_work_bits,
      ) {
        bail!("--fri parameters do not match the verifying key");
      }
      key.verify(&claim_elts, &inner_proof).map_err(|e| {
        anyhow::anyhow!("Aiur proof does not verify natively: {e:?}")
      })?;
      println!("native pre-check: Aiur proof verifies");
      let mode: Mode =
        sp1.mode.parse().map_err(|e: String| anyhow::anyhow!(e))?;
      run_sp1(
        vk_bytes,
        claim_bytes,
        proof_bytes,
        &fri.to_parameters(),
        mode,
        sp1.output.as_deref(),
      )
      .await
    },
  }
}

fn decode_claim(bytes: &[u8]) -> Result<Vec<G>> {
  if !bytes.len().is_multiple_of(8) {
    bail!("claim file length {} is not a multiple of 8", bytes.len());
  }
  Ok(
    bytes
      .chunks_exact(8)
      .map(|c| G::from_u64(u64::from_le_bytes(c.try_into().unwrap())))
      .collect(),
  )
}

/// Build, prove, and natively verify the demo program.
/// Returns `(vk_bytes, claim_bytes, proof_bytes)` in artifact format.
fn prove_demo(fri: &FriArgs) -> Result<(Vec<u8>, Vec<u8>, Vec<u8>)> {
  // Canonical parameters shared with `ix prove` (Ix/Cli/ProveCmd.lean).
  let commitment_parameters =
    CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let system = AiurSystem::build(
    demo::toplevel(),
    commitment_parameters,
    fri.to_parameters(),
  );

  let input = [G::from_u64(3), G::from_u64(5)];
  let mut io_buffer =
    IOBuffer { data: Default::default(), map: Default::default() };
  let (claim, proof) =
    system.prove(demo::ENTRY_FUN_IDX, &input, &mut io_buffer);
  println!(
    "demo claim: {:?}",
    claim.iter().map(G::as_canonical_u64).collect::<Vec<_>>()
  );

  system
    .verify(&claim, &proof)
    .map_err(|e| anyhow::anyhow!("native verification failed: {e:?}"))?;
  println!("native pre-check: demo proof verifies");

  let vk_bytes = aiur_system_to_bytes(&system)
    .map_err(|e| anyhow::anyhow!("vk serialization failed: {e}"))?;
  let claim_bytes = claim
    .iter()
    .flat_map(|g| g.as_canonical_u64().to_le_bytes())
    .collect::<Vec<u8>>();
  let proof_bytes = proof
    .to_bytes()
    .map_err(|e| anyhow::anyhow!("proof serialization failed: {e}"))?;
  Ok((vk_bytes, claim_bytes, proof_bytes))
}
