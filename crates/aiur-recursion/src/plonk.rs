//! The gnark PLONK stage over a wrap proof: SP1's circuit-artifact build
//! (`sp1_prover::build`) keyed by the wrap verifying key, then the PLONK
//! prover/verifier of `sp1-recursion-gnark-ffi`. The gnark toolchain runs in
//! SP1's Docker image unless the FFI crate's `native` feature is on.

use std::{
  borrow::Borrow,
  path::{Path, PathBuf},
};

use anyhow::{Context, Result, anyhow};
use sha2::{Digest, Sha256};
use slop_algebra::{AbstractField, PrimeField, PrimeField32};
use slop_bn254::Bn254Fr;
use sp1_hypercube::{SP1WrapProof, koalabears_to_bn254};
use sp1_primitives::SP1Field;
use sp1_prover::build::build_plonk_bn254_artifacts;
use sp1_recursion_circuit::{
  machine::SP1ShapedWitnessValues,
  utils::{
    koalabear_bytes_to_bn254, koalabears_proof_nonce_to_bn254, words_to_bytes,
  },
  witness::{OuterWitness, Witnessable},
};
use sp1_recursion_executor::RecursionPublicValues;
use sp1_recursion_gnark_ffi::{PlonkBn254Proof, PlonkBn254Prover};

use crate::pipeline::WrapProof;

/// The public inputs of the PLONK proof, as the on-chain verifier receives
/// them: BN254 field elements packed from the wrap proof's public values.
#[derive(Clone, Debug)]
pub struct PlonkPublicInputs {
  /// Poseidon2 digest of the Aiur machine's verifying key.
  pub vkey_hash: Bn254Fr,
  /// The 32-byte claim digest (`claim_digest_bytes`), packed.
  pub committed_values_digest: Bn254Fr,
  pub exit_code: Bn254Fr,
  pub vk_root: Bn254Fr,
  pub proof_nonce: Bn254Fr,
}

impl PlonkPublicInputs {
  pub fn of_wrap_proof(proof: &WrapProof) -> Result<Self> {
    let pv: &RecursionPublicValues<SP1Field> =
      proof.proof.public_values.as_slice().borrow();
    let bytes: [SP1Field; 32] = words_to_bytes(&pv.committed_value_digest)
      .try_into()
      .map_err(|bytes: Vec<SP1Field>| {
        anyhow!("committed_value_digest is {} bytes, not 32", bytes.len())
      })?;
    Ok(Self {
      vkey_hash: koalabears_to_bn254(&pv.sp1_vk_digest),
      committed_values_digest: koalabear_bytes_to_bn254(&bytes),
      exit_code: Bn254Fr::from_canonical_u32(pv.exit_code.as_canonical_u32()),
      vk_root: koalabears_to_bn254(&pv.vk_root),
      proof_nonce: koalabears_proof_nonce_to_bn254(&pv.proof_nonce),
    })
  }
}

/// Where the PLONK circuit artifacts for `wrap_vk` live: keyed by the
/// serialized verifying key, under `~/.ix/cache/plonk-bn254/`.
pub fn artifacts_dir(
  wrap_vk: &sp1_hypercube::MachineVerifyingKey<
    sp1_primitives::SP1OuterGlobalContext,
  >,
) -> Result<PathBuf> {
  let bytes = bincode::serialize(wrap_vk).context("serializing the wrap vk")?;
  let key = hex::encode(Sha256::digest(bytes));
  let home = std::env::var_os("HOME")
    .map(PathBuf::from)
    .ok_or_else(|| anyhow!("HOME is not set"))?;
  Ok(home.join(".ix").join("cache").join("plonk-bn254").join(key))
}

/// Build the PLONK circuit artifacts for the wrap proof's verifying key if
/// they are not cached yet, and return their directory.
pub fn ensure_artifacts(wrap: &WrapProof) -> Result<PathBuf> {
  let dir = artifacts_dir(&wrap.vk)?;
  if dir.join("plonk_vk.bin").exists() && dir.join("plonk_pk.bin").exists() {
    return Ok(dir);
  }
  tracing::info!("building PLONK circuit artifacts in {}", dir.display());
  build_plonk_bn254_artifacts(&wrap.vk, &wrap.proof, &dir)
    .context("building the PLONK circuit artifacts")?;
  Ok(dir)
}

/// Prove the wrap proof in the gnark PLONK circuit at `build_dir` and verify
/// the result.
pub fn prove(
  wrap: WrapProof,
  build_dir: &Path,
) -> Result<(PlonkBn254Proof, PlonkPublicInputs)> {
  let inputs = PlonkPublicInputs::of_wrap_proof(&wrap)?;
  let SP1WrapProof { vk, proof } = wrap;
  let shaped = SP1ShapedWitnessValues {
    vks_and_proofs: vec![(vk, proof)],
    is_complete: true,
  };
  let mut witness = OuterWitness::default();
  shaped.write(&mut witness);
  witness.write_committed_values_digest(inputs.committed_values_digest);
  witness.write_vkey_hash(inputs.vkey_hash);
  witness.write_exit_code(inputs.exit_code);
  witness.write_vk_root(inputs.vk_root);
  witness.write_proof_nonce(inputs.proof_nonce);
  let prover = PlonkBn254Prover::new();
  let proof = prover.prove(witness, build_dir);
  if std::env::var_os("IX_HC_DEBUG").is_some() {
    eprintln!("plonk proof public inputs: {:?}", proof.public_inputs);
    eprintln!(
      "expected: vkey_hash {} committed {} exit_code {} vk_root {} nonce {}",
      inputs.vkey_hash.as_canonical_biguint(),
      inputs.committed_values_digest.as_canonical_biguint(),
      inputs.exit_code.as_canonical_biguint(),
      inputs.vk_root.as_canonical_biguint(),
      inputs.proof_nonce.as_canonical_biguint()
    );
  }
  prover
    .verify(
      &proof,
      &inputs.vkey_hash.as_canonical_biguint(),
      &inputs.committed_values_digest.as_canonical_biguint(),
      &inputs.exit_code.as_canonical_biguint(),
      &inputs.vk_root.as_canonical_biguint(),
      &inputs.proof_nonce.as_canonical_biguint(),
      build_dir,
    )
    .map_err(|e| anyhow!("PLONK proof does not verify: {e}"))?;
  Ok((proof, inputs))
}
