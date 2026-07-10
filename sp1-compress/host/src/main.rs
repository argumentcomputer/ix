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

mod demo;

use std::path::PathBuf;

use aiur::{
  G,
  execute::IOBuffer,
  synthesis::AiurSystem,
  vk_codec::{AiurVerifyingKey, aiur_system_to_bytes},
};
use anyhow::{Context, Result, bail};
use clap::{Args, Parser, Subcommand, ValueEnum};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::{CommitmentParameters, FriParameters},
};
use sp1_sdk::{
  ProverClient, SP1ProofWithPublicValues, SP1Stdin, include_elf, prelude::*,
};

const GUEST_ELF: Elf = include_elf!("sp1-compress-guest");

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

  fn to_bytes(&self) -> Vec<u8> {
    [
      self.log_final_poly_len,
      self.max_log_arity,
      self.num_queries,
      self.commit_pow_bits,
      self.query_pow_bits,
    ]
    .iter()
    .flat_map(|&x| (x as u64).to_le_bytes())
    .collect()
  }
}

#[derive(Args)]
struct Sp1Args {
  /// SP1 stage: `execute` only emulates (cycle counts, no proof).
  /// `groth16`/`plonk` additionally need Docker or a native gnark build.
  #[arg(long, value_enum, default_value_t = Mode::Compressed)]
  mode: Mode,
  /// Write the SP1 proof here (bincode, the SDK's `.save()` format).
  #[arg(long)]
  output: Option<PathBuf>,
}

#[derive(Clone, Copy, ValueEnum)]
enum Mode {
  Execute,
  Core,
  Compressed,
  Groth16,
  Plonk,
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
      run_sp1(vk_bytes, claim_bytes, proof_bytes, &fri, &sp1).await
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
      run_sp1(vk_bytes, claim_bytes, proof_bytes, &fri, &sp1).await
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

/// Expected guest public values: `blake3(vk) || fri params || claim`.
fn expected_public_values(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  fri: &FriArgs,
) -> Vec<u8> {
  let mut expected = Vec::with_capacity(32 + 40 + claim_bytes.len());
  expected.extend_from_slice(blake3::hash(vk_bytes).as_bytes());
  expected.extend_from_slice(&fri.to_bytes());
  expected.extend_from_slice(claim_bytes);
  expected
}

async fn run_sp1(
  vk_bytes: Vec<u8>,
  claim_bytes: Vec<u8>,
  proof_bytes: Vec<u8>,
  fri: &FriArgs,
  sp1: &Sp1Args,
) -> Result<()> {
  println!(
    "inner proof: {} bytes, vk: {} bytes, claim: {} elements",
    proof_bytes.len(),
    vk_bytes.len(),
    claim_bytes.len() / 8
  );

  let mut stdin = SP1Stdin::new();
  stdin.write_vec(vk_bytes.clone());
  stdin.write_vec(fri.to_bytes());
  stdin.write_vec(claim_bytes.clone());
  stdin.write_vec(proof_bytes);

  let expected = expected_public_values(&vk_bytes, &claim_bytes, fri);
  let client = ProverClient::from_env().await;

  if matches!(sp1.mode, Mode::Execute) {
    let (public_values, report) =
      client.execute(GUEST_ELF, stdin).await.context("execution failed")?;
    if public_values.as_slice() != expected.as_slice() {
      bail!("guest public values mismatch");
    }
    println!("total cycles: {}", report.total_instruction_count());
    println!("{report}");
    return Ok(());
  }

  let pk = client.setup(GUEST_ELF).await.context("setup failed")?;
  let request = client.prove(&pk, stdin);
  let proof: SP1ProofWithPublicValues = match sp1.mode {
    Mode::Execute => unreachable!(),
    Mode::Core => request.core().await,
    Mode::Compressed => request.compressed().await,
    Mode::Groth16 => request.groth16().await,
    Mode::Plonk => request.plonk().await,
  }
  .context("SP1 proving failed")?;

  client
    .verify(&proof, pk.verifying_key(), None)
    .context("SP1 proof verification failed")?;
  if proof.public_values.as_slice() != expected.as_slice() {
    bail!("guest public values mismatch");
  }

  let size = bincode::serialized_size(&proof)?;
  println!("SP1 proof verified; serialized size: {size} bytes");
  println!("vk digest: {}", hex::encode(blake3::hash(&vk_bytes).as_bytes()));

  if let Some(path) = &sp1.output {
    proof.save(path).context("saving SP1 proof failed")?;
    println!("SP1 proof saved to {}", path.display());
  }
  Ok(())
}
