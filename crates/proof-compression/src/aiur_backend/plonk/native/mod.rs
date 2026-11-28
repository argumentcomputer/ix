//! Pure-Rust (+ optional Ix-CUDA) PLONK + BSB22 setup, witness solver, prover,
//! verifier, and Solidity verifier generator directly over Lean's formally
//! certified `ix-aiur-scs-v1` (`ixscs001`) format for both BN254 and BLS12-381.
//!
//! Compiles and runs under default features with zero Go, CGo, or `bindgen`
//! dependencies.

pub mod cuda_accel;
pub mod preprocess;
pub mod prover;
pub mod scs_file;
pub mod solidity;
pub mod solver;
pub mod transcript;
pub mod verifier;

#[cfg(test)]
mod tests;

use crate::kzg::{Srs, curve::KzgCurve};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{fs, path::Path};

pub use cuda_accel::PlonkAccelerator;
pub use preprocess::{ProvingKey, VerifyingKey, domain_size_for_scs, setup};
pub use prover::{
  NativeProof, ProofBundle, ProverTimings, prove, prove_binary_witness,
  prove_with_seed,
};
pub use scs_file::{
  GateCoeffs, PackedGate, ScsBuilder, ScsFile, WireHint, hex_digest,
  parse_hex_digest,
};
pub use solidity::{
  export_bls12_381_solidity, export_bn254_solidity, export_solidity,
  solidity_filename_for_vk,
};
pub use solver::{
  PreCommitmentState, parse_binary_witness, solve_post_commitment,
  solve_pre_commitment,
};
pub use verifier::{verify, verify_native_bytes, verify_solidity_bytes};

/// Format identifier for persisted native PLONK prepared directories.
pub const NATIVE_MANIFEST_FORMAT: &str = "ix-aiur-native-plonk-v1";

/// Authenticated disk manifest for a prepared native PLONK circuit directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreparedManifest {
  pub format: String,
  pub curve: String,
  pub domain: usize,
  pub public_inputs: usize,
  pub outputs: usize,
  pub gates: usize,
  pub commits: usize,
  pub scs_sha256: String,
  pub srs_blake3: String,
  pub vk_sha256: String,
  pub pk_sha256: String,
  pub inputs_sha256: String,
  pub solidity_file: String,
  pub solidity_sha256: String,
}

fn sha256_hex(bytes: &[u8]) -> String {
  let digest: [u8; 32] = Sha256::digest(bytes).into();
  hex_digest(&digest)
}

/// Preprocess an `ix-aiur-scs-v1` file and write `verifying-key.bin`,
/// `proving-key.bin`, `inputs.json`, the Solidity verifier, and
/// `manifest.json` (`ix-aiur-native-plonk-v1`) into `out_dir`.
pub fn prepare_to_dir<C: KzgCurve>(
  scs_path: &Path,
  srs: &Srs<C>,
  srs_blake3: &str,
  out_dir: &Path,
  accel: &PlonkAccelerator<C>,
) -> Result<PreparedManifest, String> {
  let scs_bytes =
    fs::read(scs_path).map_err(|e| format!("{}: {e}", scs_path.display()))?;
  let scs = ScsFile::<C>::parse(&scs_bytes)?;
  if !scs.outputs.is_empty() {
    return Err(format!(
      "native PLONK-SCS does not synthesize in-circuit pairing constraints \
       for deferred scs.outputs (got {} output wires); self-contained \
       outputs == 0 circuits are required",
      scs.outputs.len()
    ));
  }
  let (pk, vk) = setup(&scs, srs, accel)?;
  let vk_bytes = vk.to_bytes()?;
  let pk_bytes = pk.to_bytes()?;
  let inputs_bytes =
    serde_json::to_vec_pretty(&scs.to_inputs()).map_err(|e| e.to_string())?;
  let solidity_src = export_solidity(&vk)?;
  let solidity_file = solidity_filename_for_vk(&vk);

  fs::create_dir_all(out_dir)
    .map_err(|e| format!("{}: {e}", out_dir.display()))?;
  fs::write(out_dir.join("verifying-key.bin"), &vk_bytes)
    .map_err(|e| e.to_string())?;
  fs::write(out_dir.join("proving-key.bin"), &pk_bytes)
    .map_err(|e| e.to_string())?;
  fs::write(out_dir.join("inputs.json"), &inputs_bytes)
    .map_err(|e| e.to_string())?;
  fs::write(out_dir.join(solidity_file), solidity_src.as_bytes())
    .map_err(|e| e.to_string())?;

  let manifest = PreparedManifest {
    format: NATIVE_MANIFEST_FORMAT.into(),
    curve: C::NAME.into(),
    domain: vk.domain_size,
    public_inputs: scs.publics,
    outputs: scs.outputs.len(),
    gates: scs.gates_count,
    commits: scs.commits.len(),
    scs_sha256: scs.sha256_hex(),
    srs_blake3: srs_blake3.to_owned(),
    vk_sha256: sha256_hex(&vk_bytes),
    pk_sha256: sha256_hex(&pk_bytes),
    inputs_sha256: sha256_hex(&inputs_bytes),
    solidity_file: solidity_file.into(),
    solidity_sha256: sha256_hex(solidity_src.as_bytes()),
  };
  let manifest_bytes =
    serde_json::to_vec_pretty(&manifest).map_err(|e| e.to_string())?;
  fs::write(out_dir.join("manifest.json"), &manifest_bytes)
    .map_err(|e| e.to_string())?;
  Ok(manifest)
}

/// Ready-to-prove native PLONK + BSB22 handle holding an authenticated
/// [`ScsFile`], [`ProvingKey`], and [`PlonkAccelerator`].
pub struct NativeProver<C: KzgCurve> {
  scs: ScsFile<C>,
  pk: ProvingKey<C>,
  vk_sha256: [u8; 32],
  accel: PlonkAccelerator<C>,
}

impl<C: KzgCurve> NativeProver<C> {
  /// Construct directly in memory from a parsed [`ScsFile`] and [`ProvingKey`].
  pub fn from_parts(
    scs: ScsFile<C>,
    pk: ProvingKey<C>,
    accel: PlonkAccelerator<C>,
  ) -> Self {
    let vk_sha256 = pk.vk.sha256();
    Self { scs, pk, vk_sha256, accel }
  }

  /// Open a prepared directory created by [`prepare_to_dir`], verifying every
  /// SHA-256 pin (`scs`, `verifying-key.bin`, `proving-key.bin`) against
  /// `manifest`.
  pub fn open(
    prepared_dir: &Path,
    scs_path: &Path,
    manifest: &PreparedManifest,
    accel: PlonkAccelerator<C>,
  ) -> Result<Self, String> {
    if manifest.format != NATIVE_MANIFEST_FORMAT {
      return Err(format!(
        "unexpected native PLONK manifest format {:?}",
        manifest.format
      ));
    }
    if manifest.curve != C::NAME {
      return Err(format!(
        "manifest curve {:?} differs from requested {:?}",
        manifest.curve,
        C::NAME
      ));
    }
    let scs = ScsFile::<C>::read_pinned(scs_path, &manifest.scs_sha256)?;
    if !scs.outputs.is_empty() || manifest.outputs != 0 {
      return Err(format!(
        "native PLONK-SCS does not synthesize in-circuit pairing constraints \
         for deferred scs.outputs (scs has {} output wires, manifest has {}); \
         self-contained outputs == 0 circuits are required",
        scs.outputs.len(),
        manifest.outputs
      ));
    }

    let vk_bytes = fs::read(prepared_dir.join("verifying-key.bin"))
      .map_err(|e| format!("verifying-key.bin: {e}"))?;
    if sha256_hex(&vk_bytes) != manifest.vk_sha256 {
      return Err("verifying-key.bin differs from manifest SHA-256".into());
    }
    let vk = VerifyingKey::<C>::from_bytes(&vk_bytes)?;

    let pk_bytes = fs::read(prepared_dir.join("proving-key.bin"))
      .map_err(|e| format!("proving-key.bin: {e}"))?;
    if sha256_hex(&pk_bytes) != manifest.pk_sha256 {
      return Err("proving-key.bin differs from manifest SHA-256".into());
    }
    let pk = ProvingKey::<C>::from_bytes(&pk_bytes)?;
    if pk.vk != vk {
      return Err(
        "proving-key embedded VK differs from verifying-key.bin".into(),
      );
    }
    let vk_sha256 = parse_hex_digest(&manifest.vk_sha256)?;
    Ok(Self { scs, pk, vk_sha256, accel })
  }

  pub fn scs(&self) -> &ScsFile<C> {
    &self.scs
  }

  pub fn vk(&self) -> &VerifyingKey<C> {
    &self.pk.vk
  }

  pub fn vk_sha256(&self) -> [u8; 32] {
    self.vk_sha256
  }

  /// Prove from slice input wires (`0..scs.cells`).
  pub fn prove(
    &self,
    input_wires: &[C::Fr],
    expected_publics: &[C::Fr],
  ) -> Result<ProofBundle, String> {
    let (proof, timings) =
      prove(&self.scs, &self.pk, input_wires, expected_publics, &self.accel)?;
    Ok(ProofBundle {
      native: proof.to_native_bytes()?,
      solidity: proof.marshal_solidity(),
      timings,
    })
  }

  /// Prove from gnark-format binary witness bytes (`scs::Witness::binary` or
  /// `scs::Bls12381Witness::binary`).
  pub fn prove_binary(
    &self,
    witness_bytes: &[u8],
    expected_publics: &[C::Fr],
  ) -> Result<ProofBundle, String> {
    let (proof, timings) = prove_binary_witness(
      &self.scs,
      &self.pk,
      witness_bytes,
      expected_publics,
      &self.accel,
    )?;
    Ok(ProofBundle {
      native: proof.to_native_bytes()?,
      solidity: proof.marshal_solidity(),
      timings,
    })
  }
}
