//! Re-verify a saved terminal proof (Plonk or Groth16) the way a third party
//! would: with SP1's pure-Rust verifier and its published verifying key for
//! that system, no SDK prover, gnark or Docker involved. Then decode the
//! 224-byte statement.
//!
//! `cargo run --release --example verify_terminal -- root.sp1 [GUEST_VKEY_HASH]`
//!
//! Without the second argument the guest's key hash is derived from the ELF
//! compiled into this host, which is the hash a verifier must pin.

use anyhow::{Context, Result, bail};
use sp1_compress_host::{
  CURRENT_GUEST_ELF, OUTER_CLAIM_ELEMENTS, PUBLIC_VALUES_DOMAIN,
};
use sp1_sdk::{ProverClient, SP1Proof, SP1ProofWithPublicValues, prelude::*};
use sp1_verifier::{
  GROTH16_VK_BYTES, Groth16Verifier, PLONK_VK_BYTES, PlonkVerifier,
};

#[tokio::main]
async fn main() -> Result<()> {
  let mut args = std::env::args().skip(1);
  let path =
    args.next().context("usage: verify_plonk ROOT.sp1 [GUEST_VKEY_HASH]")?;
  let vkey_hash = match args.next() {
    Some(hash) => hash,
    None => {
      let client = ProverClient::from_env().await;
      let pk = client.setup(CURRENT_GUEST_ELF).await.context("SP1 setup")?;
      pk.verifying_key().bytes32()
    },
  };

  let proof = SP1ProofWithPublicValues::load(&path)
    .with_context(|| format!("loading {path}"))?;
  let public_values = proof.public_values.to_vec();
  let onchain = proof.bytes();
  let system = match &proof.proof {
    SP1Proof::Plonk(_) => {
      PlonkVerifier::verify(
        &onchain,
        &public_values,
        &vkey_hash,
        &PLONK_VK_BYTES,
      )
      .map_err(|error| {
        anyhow::anyhow!("Plonk verification failed: {error:?}")
      })?;
      "Plonk"
    },
    SP1Proof::Groth16(_) => {
      Groth16Verifier::verify(
        &onchain,
        &public_values,
        &vkey_hash,
        &GROTH16_VK_BYTES,
      )
      .map_err(|error| {
        anyhow::anyhow!("Groth16 verification failed: {error:?}")
      })?;
      "Groth16"
    },
    other => bail!("not a terminal proof: {other:?}"),
  };
  println!(
    "{system} proof verified: {} bytes, guest vkey {vkey_hash}",
    onchain.len()
  );

  if public_values.len() != 8 + 32 + 40 + OUTER_CLAIM_ELEMENTS * 8 {
    bail!("public values are {} bytes, expected 224", public_values.len());
  }
  if &public_values[..8] != PUBLIC_VALUES_DOMAIN {
    bail!("public values do not start with the IXROOT01 domain");
  }
  let word = |at: usize| {
    u64::from_le_bytes(public_values[at..at + 8].try_into().unwrap())
  };
  println!("recursion vk digest: {}", hex::encode(&public_values[8..40]));
  println!(
    "fri parameters: log_final_poly_len={} max_log_arity={} num_queries={} commit_pow_bits={} query_pow_bits={}",
    word(40),
    word(48),
    word(56),
    word(64),
    word(72)
  );
  let claim: Vec<u64> =
    (0..OUTER_CLAIM_ELEMENTS).map(|i| word(80 + 8 * i)).collect();
  println!("outer claim: {claim:?}");
  Ok(())
}
