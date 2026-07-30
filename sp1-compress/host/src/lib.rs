//! Compress an Aiur multi-STARK proof by verifying it inside the SP1 zkVM
//! guest and proving that verification.
//!
//! Library surface shared by the `sp1-compress-host` CLI and `ix-ffi`
//! (cargo feature `sp1`), which backs the `ix compress` command.

pub mod wrap;

use std::{path::Path, str::FromStr};

use anyhow::{Context, Result, bail};
use multi_stark::types::FriParameters;
use sp1_sdk::{
  ProverClient, SP1ProofWithPublicValues, SP1Stdin, include_elf, prelude::*,
};

pub const GUEST_ELF: Elf = include_elf!("sp1-compress-guest");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
  /// Emulate only: cycle counts, no proof.
  Execute,
  Core,
  Compressed,
  /// Needs Docker (or a `native-gnark` SDK build) for the gnark wrapper.
  Groth16,
  Plonk,
}

impl FromStr for Mode {
  type Err = String;

  fn from_str(s: &str) -> Result<Self, String> {
    match s.to_ascii_lowercase().as_str() {
      "execute" => Ok(Self::Execute),
      "core" => Ok(Self::Core),
      "compressed" => Ok(Self::Compressed),
      "groth16" => Ok(Self::Groth16),
      "plonk" => Ok(Self::Plonk),
      other => Err(format!(
        "unknown mode `{other}` (execute|core|compressed|groth16|plonk)"
      )),
    }
  }
}

/// The guest's FRI-parameter input encoding: 5 u64 LE values.
pub fn fri_parameters_to_bytes(fri: &FriParameters) -> Vec<u8> {
  [
    fri.log_final_poly_len,
    fri.max_log_arity,
    fri.num_queries,
    fri.commit_proof_of_work_bits,
    fri.query_proof_of_work_bits,
  ]
  .iter()
  .flat_map(|&x| (x as u64).to_le_bytes())
  .collect()
}

/// Expected guest public values:
/// `blake3(vk) || fri params || n || (claim_len_u32 || claim)*`.
pub fn expected_public_values(
  vk_bytes: &[u8],
  claims: &[Vec<u8>],
  fri: &FriParameters,
) -> Vec<u8> {
  let mut expected = Vec::with_capacity(32 + 40 + 4);
  expected.extend_from_slice(blake3::hash(vk_bytes).as_bytes());
  expected.extend_from_slice(&fri_parameters_to_bytes(fri));
  expected.extend_from_slice(&(claims.len() as u32).to_le_bytes());
  for claim_bytes in claims {
    expected
      .extend_from_slice(&((claim_bytes.len() / 8) as u32).to_le_bytes());
    expected.extend_from_slice(claim_bytes);
  }
  expected
}

/// Run the guest over `(vk, fri, [(claim, proof)…])` and produce ONE SP1
/// proof of the in-circuit verification of the whole batch (or just
/// emulate, for `Mode::Execute`). Every proof in the batch is a statement
/// of the same system, verified against the single shared vk. `output`,
/// when set, receives the SP1 proof in the SDK's `.save()` format.
pub async fn run_sp1(
  vk_bytes: Vec<u8>,
  pairs: Vec<(Vec<u8>, Vec<u8>)>,
  fri: &FriParameters,
  mode: Mode,
  output: Option<&Path>,
) -> Result<()> {
  if pairs.is_empty() {
    bail!("empty batch: need at least one (claim, proof) pair");
  }
  let proof_total: usize = pairs.iter().map(|(_, p)| p.len()).sum();
  println!(
    "batch: {} proof(s), {} proof bytes total, vk: {} bytes",
    pairs.len(),
    proof_total,
    vk_bytes.len()
  );

  // Debug escape hatch: dump the exact guest inputs as artifact files (the
  // `compress` subcommand's format) so failures can be reproduced natively.
  if let Ok(dir) = std::env::var("SP1_COMPRESS_DUMP_DIR") {
    let dir = Path::new(&dir);
    std::fs::create_dir_all(dir)?;
    std::fs::write(dir.join("vk.bin"), &vk_bytes)?;
    for (k, (claim_bytes, proof_bytes)) in pairs.iter().enumerate() {
      std::fs::write(dir.join(format!("claim-{k}.bin")), claim_bytes)?;
      std::fs::write(dir.join(format!("proof-{k}.bin")), proof_bytes)?;
    }
    println!("sp1-compress: dumped guest inputs to {}", dir.display());
  }

  let mut stdin = SP1Stdin::new();
  stdin.write_vec(vk_bytes.clone());
  stdin.write_vec(fri_parameters_to_bytes(fri));
  stdin.write_vec((pairs.len() as u32).to_le_bytes().to_vec());
  let claims: Vec<Vec<u8>> =
    pairs.iter().map(|(c, _)| c.clone()).collect();
  for (claim_bytes, proof_bytes) in pairs {
    stdin.write_vec(claim_bytes);
    stdin.write_vec(proof_bytes);
  }

  let expected = expected_public_values(&vk_bytes, &claims, fri);
  let client = ProverClient::from_env().await;

  if matches!(mode, Mode::Execute) {
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
  let proof: SP1ProofWithPublicValues = match mode {
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
  // For the onchain wraps, also surface the raw proof blob — the thing an
  // EVM/`sp1-verifier` consumer actually takes (`bytes()` panics on
  // core/compressed proofs, so gate it).
  if matches!(mode, Mode::Groth16 | Mode::Plonk) {
    let onchain = proof.bytes();
    println!(
      "onchain proof: {} bytes, 0x{}",
      onchain.len(),
      hex::encode(&onchain)
    );
    println!("sp1 vkey (bn254): {}", pk.verifying_key().bytes32());
  }

  if let Some(path) = output {
    proof.save(path).context("saving SP1 proof failed")?;
    println!("SP1 proof saved to {}", path.display());
  }
  Ok(())
}

/// Blocking wrapper for callers without an async runtime (the `ix` FFI).
pub fn run_sp1_blocking(
  vk_bytes: Vec<u8>,
  pairs: Vec<(Vec<u8>, Vec<u8>)>,
  fri: &FriParameters,
  mode: Mode,
  output: Option<&Path>,
) -> Result<()> {
  tokio::runtime::Runtime::new()
    .context("tokio runtime")?
    .block_on(run_sp1(vk_bytes, pairs, fri, mode, output))
}
