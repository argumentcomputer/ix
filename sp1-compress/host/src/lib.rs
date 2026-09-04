//! Verify one persisted `ix_aggr` root inside SP1 and run SP1's recursive
//! compression tail to a final Groth16 or Plonk SNARK.

use std::{path::Path, str::FromStr};

use aiur::{G, synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use anyhow::{Context, Result, bail};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::FriParameters,
};
#[cfg(not(clippy))]
use sp1_sdk::include_elf;
use sp1_sdk::{
  Elf, ProverClient, SP1ProofWithPublicValues, SP1Stdin, prelude::*,
};

#[cfg(not(clippy))]
pub const GUEST_ELF: Elf = include_elf!("sp1-compress-guest");
// `sp1-build` intentionally skips guest compilation under clippy. Keep host
// API linting available on clean checkouts; this value is never executed by
// clippy itself.
#[cfg(clippy)]
pub const GUEST_ELF: Elf = Elf::Static(&[]);
pub const PUBLIC_VALUES_DOMAIN: &[u8; 8] = b"IXROOT01";
pub const OUTER_CLAIM_ELEMENTS: usize = 18;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
  Execute,
  Core,
  Compressed,
  Groth16,
  Plonk,
}

impl FromStr for Mode {
  type Err = String;

  fn from_str(value: &str) -> Result<Self, Self::Err> {
    match value.to_ascii_lowercase().as_str() {
      "execute" => Ok(Self::Execute),
      "core" => Ok(Self::Core),
      "compressed" => Ok(Self::Compressed),
      "groth16" => Ok(Self::Groth16),
      "plonk" => Ok(Self::Plonk),
      other => Err(format!(
        "unknown SP1 mode `{other}` (execute|core|compressed|groth16|plonk)"
      )),
    }
  }
}

pub fn fri_parameters_to_bytes(fri: &FriParameters) -> Vec<u8> {
  [
    fri.log_final_poly_len,
    fri.max_log_arity,
    fri.num_queries,
    fri.commit_proof_of_work_bits,
    fri.query_proof_of_work_bits,
  ]
  .iter()
  .flat_map(|&value| (value as u64).to_le_bytes())
  .collect()
}

fn decode_claim(claim_bytes: &[u8]) -> Result<Vec<G>> {
  if claim_bytes.len() != OUTER_CLAIM_ELEMENTS * 8 {
    bail!(
      "ix_aggr outer claim is {} bytes; expected {} (18 Goldilocks words)",
      claim_bytes.len(),
      OUTER_CLAIM_ELEMENTS * 8
    );
  }
  claim_bytes
    .as_chunks::<8>()
    .0
    .iter()
    .enumerate()
    .map(|(index, chunk)| {
      let word = u64::from_le_bytes(*chunk);
      let value = G::from_u64(word);
      if value.as_canonical_u64() != word {
        bail!("outer claim word {index} is not canonical Goldilocks");
      }
      Ok(value)
    })
    .collect()
}

fn fri_matches(actual: &FriParameters, expected: &FriParameters) -> bool {
  actual.log_final_poly_len == expected.log_final_poly_len
    && actual.max_log_arity == expected.max_log_arity
    && actual.num_queries == expected.num_queries
    && actual.commit_proof_of_work_bits == expected.commit_proof_of_work_bits
    && actual.query_proof_of_work_bits == expected.query_proof_of_work_bits
}

/// Fail fast natively before starting SP1 setup or proving. The guest repeats
/// every one of these checks; this preflight is an ergonomics and cost guard,
/// not part of the soundness argument.
pub fn validate_root_inputs(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  proof_bytes: &[u8],
  fri: &FriParameters,
) -> Result<()> {
  let claim = decode_claim(claim_bytes)?;
  let vk = AiurVerifyingKey::from_bytes(vk_bytes)
    .map_err(|error| anyhow::anyhow!("invalid Aiur verifying key: {error}"))?;
  if !fri_matches(&vk.fri_parameters(), fri) {
    bail!("requested recursion FRI parameters do not match the Aiur vk");
  }
  let proof = AiurProof::from_bytes(proof_bytes)
    .map_err(|error| anyhow::anyhow!("invalid Aiur proof: {error}"))?;
  vk.verify(&claim, &proof).map_err(|error| {
    anyhow::anyhow!("aggregate root does not verify: {error:?}")
  })
}

/// Canonical SP1 public values:
/// `IXROOT01 || blake3(aiur_vk) || fri_parameters || ix_aggr_outer_claim`.
pub fn expected_public_values(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  fri: &FriParameters,
) -> Result<Vec<u8>> {
  let claim = decode_claim(claim_bytes)?;
  let mut expected = Vec::with_capacity(8 + 32 + 40 + OUTER_CLAIM_ELEMENTS * 8);
  expected.extend_from_slice(PUBLIC_VALUES_DOMAIN);
  expected.extend_from_slice(blake3::hash(vk_bytes).as_bytes());
  expected.extend_from_slice(&fri_parameters_to_bytes(fri));
  for value in claim {
    expected.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
  }
  Ok(expected)
}

/// Execute or prove the SP1 terminal. `output` receives the SDK's verified
/// proof container. For Groth16/Plonk, `onchain_output` receives the raw proof
/// bytes consumed by an onchain verifier.
pub async fn run_sp1(
  vk_bytes: Vec<u8>,
  claim_bytes: Vec<u8>,
  proof_bytes: Vec<u8>,
  fri: &FriParameters,
  mode: Mode,
  output: Option<&Path>,
  onchain_output: Option<&Path>,
) -> Result<()> {
  if onchain_output.is_some() && !matches!(mode, Mode::Groth16 | Mode::Plonk) {
    bail!("--onchain-output requires --mode groth16 or --mode plonk");
  }
  validate_root_inputs(&vk_bytes, &claim_bytes, &proof_bytes, fri)?;
  println!(
    "native preflight: aggregate root verifies (proof={} bytes, vk={} bytes)",
    proof_bytes.len(),
    vk_bytes.len()
  );
  println!(
    "SP1 guest ELF: {} bytes, blake3 {}",
    GUEST_ELF.len(),
    blake3::hash(&GUEST_ELF).to_hex()
  );

  let mut stdin = SP1Stdin::new();
  stdin.write_vec(vk_bytes.clone());
  stdin.write_vec(fri_parameters_to_bytes(fri));
  stdin.write_vec(claim_bytes.clone());
  stdin.write_vec(proof_bytes);

  let expected = expected_public_values(&vk_bytes, &claim_bytes, fri)?;
  let client = ProverClient::from_env().await;
  if mode == Mode::Execute {
    let (public_values, report) =
      client.execute(GUEST_ELF, stdin).await.context("SP1 execution failed")?;
    if public_values.as_slice() != expected.as_slice() {
      bail!("SP1 guest public values do not match the host reconstruction");
    }
    println!("SP1 execute accepted the root");
    println!("total cycles: {}", report.total_instruction_count());
    let mut phases = report.cycle_tracker.iter().collect::<Vec<_>>();
    phases.sort_unstable_by_key(|(name, _)| name.as_str());
    for (name, cycles) in phases {
      let invocations =
        report.invocation_tracker.get(name).copied().unwrap_or(0);
      println!("profile {name}: {cycles} cycles ({invocations} invocation(s))");
    }
    println!("{report}");
    return Ok(());
  }

  let pk = client.setup(GUEST_ELF).await.context("SP1 setup failed")?;
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
    bail!("SP1 proof public values do not match the host reconstruction");
  }

  let serialized_size = bincode::serialized_size(&proof)?;
  println!("SP1 proof verified; SDK artifact: {serialized_size} bytes");
  println!("SP1 program vkey: {}", pk.verifying_key().bytes32());
  println!("Aiur recursion vk digest: {}", blake3::hash(&vk_bytes).to_hex());
  println!("public values: 0x{}", hex::encode(&expected));

  if matches!(mode, Mode::Groth16 | Mode::Plonk) {
    let onchain = proof.bytes();
    println!(
      "onchain proof: {} bytes, 0x{}",
      onchain.len(),
      hex::encode(&onchain)
    );
    if let Some(path) = onchain_output {
      std::fs::write(path, &onchain)
        .with_context(|| format!("write onchain proof {}", path.display()))?;
      println!("onchain proof saved to {}", path.display());
    }
  }
  if let Some(path) = output {
    proof.save(path).context("saving SP1 proof failed")?;
    println!("SP1 proof saved to {}", path.display());
  }
  Ok(())
}

pub fn run_sp1_blocking(
  vk_bytes: Vec<u8>,
  claim_bytes: Vec<u8>,
  proof_bytes: Vec<u8>,
  fri: &FriParameters,
  mode: Mode,
  output: Option<&Path>,
  onchain_output: Option<&Path>,
) -> Result<()> {
  tokio::runtime::Runtime::new().context("tokio runtime")?.block_on(run_sp1(
    vk_bytes,
    claim_bytes,
    proof_bytes,
    fri,
    mode,
    output,
    onchain_output,
  ))
}

#[cfg(test)]
mod tests {
  use super::*;

  fn test_fri() -> FriParameters {
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 100,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    }
  }

  fn canonical_claim() -> Vec<u8> {
    (0..OUTER_CLAIM_ELEMENTS as u64).flat_map(u64::to_le_bytes).collect()
  }

  #[test]
  fn public_values_are_fixed_and_domain_separated() {
    let vk = b"vk";
    let claim = canonical_claim();
    let public =
      expected_public_values(vk, &claim, &test_fri()).expect("public");
    assert_eq!(public.len(), 8 + 32 + 40 + 18 * 8);
    assert_eq!(&public[..8], PUBLIC_VALUES_DOMAIN);
    assert_eq!(&public[8..40], blake3::hash(vk).as_bytes());
    assert_eq!(&public[80..], claim);
  }

  #[test]
  fn root_claim_shape_and_canonical_encoding_are_strict() {
    assert!(expected_public_values(b"vk", &[0; 8], &test_fri()).is_err());
    let mut claim = canonical_claim();
    claim[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(expected_public_values(b"vk", &claim, &test_fri()).is_err());
  }

  #[test]
  fn mode_parser_is_closed() {
    assert_eq!("groth16".parse(), Ok(Mode::Groth16));
    assert!("final-ish".parse::<Mode>().is_err());
  }
}
