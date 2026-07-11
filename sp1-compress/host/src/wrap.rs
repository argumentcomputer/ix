//! Upgrade a saved *compressed* SP1 proof to groth16/plonk without redoing
//! the core/compress STARK stages (hours) — only shrink → BN254 wrap →
//! gnark run (minutes + the gnark proof).
//!
//! Mirrors the tail of SP1's internal pipeline: `FullNode::shrink_wrap` is
//! public API, but the final gnark stage is only reachable through the
//! internal task queue, so it is replicated here verbatim from
//! `RecursionProver::{run_plonk, run_groth16}` (sp1-prover
//! `worker/prover/recursion.rs`, tag v6.3.1). Keep in sync when bumping SP1.
//!
//! Version-bound: the saved proof only upgrades under the same SP1 circuit
//! version that produced it; the shrink stage's verification rejects
//! mismatches.

use std::{borrow::Borrow, path::Path};

use anyhow::{Context, Result, anyhow, bail};
use slop_algebra::{AbstractField, PrimeField, PrimeField32};
use slop_bn254::Bn254Fr;
use sp1_hypercube::{SP1PcsProofOuter, SP1WrapProof, koalabears_to_bn254};
use sp1_primitives::{SP1Field, SP1OuterGlobalContext};
use sp1_prover::{
  build::{try_build_groth16_artifacts_dir, try_build_plonk_artifacts_dir},
  worker::{SP1LocalNodeBuilder, cpu_worker_builder},
};
use sp1_recursion_circuit::{
  machine::SP1ShapedWitnessValues,
  utils::{
    koalabear_bytes_to_bn254, koalabears_proof_nonce_to_bn254, words_to_bytes,
  },
  witness::{OuterWitness, Witnessable},
};
use sp1_recursion_executor::RecursionPublicValues;
use sp1_recursion_gnark_ffi::{
  Groth16Bn254Proof, Groth16Bn254Prover, PlonkBn254Proof, PlonkBn254Prover,
};
use sp1_sdk::{SP1Proof, SP1ProofWithPublicValues};

use crate::Mode;

type WrapProof = SP1WrapProof<SP1OuterGlobalContext, SP1PcsProofOuter>;

/// Load a saved compressed `SP1ProofWithPublicValues`, run the remaining
/// pipeline stages for `mode` (`Groth16` or `Plonk`), and save/print the
/// upgraded proof. The public values and version metadata carry over.
pub async fn wrap_saved(
  input: &Path,
  mode: Mode,
  output: Option<&Path>,
) -> Result<()> {
  let mut saved = SP1ProofWithPublicValues::load(input)
    .with_context(|| format!("loading SP1 proof from {}", input.display()))?;
  if !matches!(saved.proof, SP1Proof::Compressed(_)) {
    bail!(
      "{} does not contain a compressed proof; only compressed proofs can \
       be wrapped (core proofs must re-prove, wrapped ones already are)",
      input.display()
    );
  }
  println!(
    "loaded compressed proof from {} (sp1 {}), {} public value bytes",
    input.display(),
    saved.sp1_version,
    saved.public_values.as_slice().len()
  );

  let node =
    SP1LocalNodeBuilder::from_worker_client_builder(cpu_worker_builder())
      .build()
      .await
      .map_err(|e| anyhow!("building local prover node: {e:#}"))?;
  println!("running shrink + wrap (recursive STARK stages)...");
  let wrap_proof = node
    .shrink_wrap(&saved.proof)
    .await
    .map_err(|e| anyhow!("shrink/wrap failed: {e:#}"))?;

  println!("running gnark {mode:?} wrap...");
  saved.proof = match mode {
    Mode::Plonk => SP1Proof::Plonk(prove_plonk(wrap_proof).await?),
    Mode::Groth16 => SP1Proof::Groth16(prove_groth16(wrap_proof).await?),
    _ => bail!("wrap target must be plonk or groth16"),
  };

  let onchain = saved.bytes();
  println!(
    "onchain proof: {} bytes, 0x{}",
    onchain.len(),
    hex::encode(&onchain)
  );
  if let Some(path) = output {
    saved.save(path).context("saving upgraded SP1 proof failed")?;
    println!("SP1 proof saved to {}", path.display());
  }
  Ok(())
}

/// Blocking wrapper for callers without an async runtime (the `ix` FFI).
pub fn wrap_saved_blocking(
  input: &Path,
  mode: Mode,
  output: Option<&Path>,
) -> Result<()> {
  tokio::runtime::Runtime::new()
    .context("tokio runtime")?
    .block_on(wrap_saved(input, mode, output))
}

// The two functions below are line-for-line ports of the gnark stages in
// sp1-prover's `RecursionProver::{run_plonk, run_groth16}`, minus the
// artifact-client plumbing (we hold the wrap proof in memory).

async fn prove_plonk(wrap_proof: WrapProof) -> Result<PlonkBn254Proof> {
  let build_dir =
    try_build_plonk_artifacts_dir(&wrap_proof.vk, &wrap_proof.proof).await?;

  tokio::task::spawn_blocking(move || -> Result<_> {
    let SP1WrapProof { vk: wrap_vk, proof: wrap_proof } = wrap_proof;
    let input = SP1ShapedWitnessValues {
      vks_and_proofs: vec![(wrap_vk.clone(), wrap_proof.clone())],
      is_complete: true,
    };
    let pv: &RecursionPublicValues<SP1Field> =
      wrap_proof.public_values.as_slice().borrow();
    let vkey_hash = koalabears_to_bn254(&pv.sp1_vk_digest);
    let committed_values_digest_bytes: [SP1Field; 32] =
      words_to_bytes(&pv.committed_value_digest)
        .try_into()
        .map_err(|_| anyhow!("committed_value_digest has invalid length"))?;
    let committed_values_digest =
      koalabear_bytes_to_bn254(&committed_values_digest_bytes);
    let exit_code =
      Bn254Fr::from_canonical_u32(pv.exit_code.as_canonical_u32());
    let vk_root = koalabears_to_bn254(&pv.vk_root);
    let proof_nonce = koalabears_proof_nonce_to_bn254(&pv.proof_nonce);
    let witness = {
      let mut witness = OuterWitness::default();
      input.write(&mut witness);
      witness.write_committed_values_digest(committed_values_digest);
      witness.write_vkey_hash(vkey_hash);
      witness.write_exit_code(exit_code);
      witness.write_vk_root(vk_root);
      witness.write_proof_nonce(proof_nonce);
      witness
    };
    let prover = PlonkBn254Prover::new();
    let proof = prover.prove(witness, &build_dir);
    prover
      .verify(
        &proof,
        &vkey_hash.as_canonical_biguint(),
        &committed_values_digest.as_canonical_biguint(),
        &exit_code.as_canonical_biguint(),
        &vk_root.as_canonical_biguint(),
        &proof_nonce.as_canonical_biguint(),
        &build_dir,
      )
      .map_err(|e| anyhow!("failed to verify plonk wrap proof: {e}"))?;
    Ok(proof)
  })
  .await
  .map_err(|e| anyhow!("plonk proof task panicked: {e}"))?
}

async fn prove_groth16(wrap_proof: WrapProof) -> Result<Groth16Bn254Proof> {
  let build_dir =
    try_build_groth16_artifacts_dir(&wrap_proof.vk, &wrap_proof.proof).await?;

  tokio::task::spawn_blocking(move || -> Result<_> {
    let SP1WrapProof { vk, proof } = wrap_proof;
    let input = SP1ShapedWitnessValues {
      vks_and_proofs: vec![(vk, proof.clone())],
      is_complete: true,
    };
    let pv: &RecursionPublicValues<SP1Field> =
      proof.public_values.as_slice().borrow();
    let vkey_hash = koalabears_to_bn254(&pv.sp1_vk_digest);
    let committed_values_digest_bytes: [SP1Field; 32] =
      words_to_bytes(&pv.committed_value_digest)
        .try_into()
        .map_err(|_| anyhow!("committed_value_digest has invalid length"))?;
    let committed_values_digest =
      koalabear_bytes_to_bn254(&committed_values_digest_bytes);
    let exit_code =
      Bn254Fr::from_canonical_u32(pv.exit_code.as_canonical_u32());
    let proof_nonce = koalabears_proof_nonce_to_bn254(&pv.proof_nonce);
    let vk_root = koalabears_to_bn254(&pv.vk_root);
    let witness = {
      let mut witness = OuterWitness::default();
      input.write(&mut witness);
      witness.write_committed_values_digest(committed_values_digest);
      witness.write_vkey_hash(vkey_hash);
      witness.write_exit_code(exit_code);
      witness.write_vk_root(vk_root);
      witness.write_proof_nonce(proof_nonce);
      witness
    };
    let prover = Groth16Bn254Prover::new();
    let proof = prover.prove(witness, &build_dir);
    prover
      .verify(
        &proof,
        &vkey_hash.as_canonical_biguint(),
        &committed_values_digest.as_canonical_biguint(),
        &exit_code.as_canonical_biguint(),
        &vk_root.as_canonical_biguint(),
        &proof_nonce.as_canonical_biguint(),
        &build_dir,
      )
      .map_err(|e| anyhow!("failed to verify groth16 wrap proof: {e}"))?;
    Ok(proof)
  })
  .await
  .map_err(|e| anyhow!("groth16 proof task panicked: {e}"))?
}
