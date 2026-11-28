//! Pure-Rust deterministic BN254 Groth16 Solidity verifier generator.
//!
//! Emits a standalone `Groth16Verifier` contract using Ethereum EIP-196
//! (`ecAdd` `0x06`, `ecMul` `0x07`) and EIP-197 (`ecPairing` `0x08`)
//! precompiles. For `2` public inputs, the generated `verifyProof` ABI matches
//! `contracts/groth16/src/IxGroth16Verifier.sol`'s `IGroth16Verifier`
//! interface verbatim.

use super::setup::VerifyingKey;
use ark_bn254::{Fq, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use num_bigint::BigUint;
use std::fmt::Write;

const BN254_P_DEC: &str = "21888242871839275222246405745257275088696311157297823662689037894645226208583";
const BN254_R_DEC: &str = "21888242871839275222246405745257275088548364400416034343698204186575808495617";

fn fq_dec(val: Fq) -> String {
  BigUint::from_bytes_le(&val.into_bigint().to_bytes_le()).to_string()
}

fn g1_dec(pt: &G1Affine) -> (String, String) {
  if pt.is_zero() {
    ("0".into(), "0".into())
  } else {
    (fq_dec(pt.x), fq_dec(pt.y))
  }
}

/// Format a G2 point in EIP-197 order `(x_c1, x_c0, y_c1, y_c0)`.
fn g2_eip197_dec(pt: &G2Affine) -> (String, String, String, String) {
  if pt.is_zero() {
    ("0".into(), "0".into(), "0".into(), "0".into())
  } else {
    (fq_dec(pt.x.c1), fq_dec(pt.x.c0), fq_dec(pt.y.c1), fq_dec(pt.y.c0))
  }
}

pub const DEV_SOLIDITY_CONTRACT: &str =
  "Groth16Verifier_DEV_INSECURE_DO_NOT_DEPLOY";
pub const DEV_SOLIDITY_HEADER: &str = "\
// WARNING: GENERATED FROM A DEVELOPMENT TRAPDOOR SETUP — DO NOT DEPLOY\n\
// No multi-party ceremony setup exists for this backend yet; anyone holding\n\
// the setup trapdoors can forge arbitrary proofs accepted by this contract.\n\n";

/// Output filename for an exported Groth16 Solidity verifier. Development
/// setups never emit an unmarked `Groth16Verifier.sol`.
pub const fn solidity_filename(is_development: bool) -> &'static str {
  if is_development {
    "Groth16Verifier.DEV_INSECURE.sol"
  } else {
    "Groth16Verifier.sol"
  }
}

/// Deterministically emit a complete Solidity verifier contract for `vk`.
///
/// Because [`super::setup`] currently only provides a development trapdoor
/// setup (`setup_dev`), this marks the exported contract as
/// `Groth16Verifier_DEV_INSECURE_DO_NOT_DEPLOY` with an unmistakable header.
/// Call [`export_solidity_with_setup`] with `is_development = false` only for
/// keys produced by an audited multi-party setup ceremony.
pub fn export_solidity(vk: &VerifyingKey) -> Result<String, String> {
  export_solidity_with_setup(vk, true)
}

/// Deterministically emit a complete Solidity verifier contract for `vk`,
/// selecting either the marked development contract (`is_development = true`)
/// or the deployable `Groth16Verifier` contract (`is_development = false`).
///
/// The emitted contract exposes:
/// `function verifyProof(bytes calldata proof, uint256[L] calldata publicInputs) external view`
/// where `L = vk.num_public_inputs()`. When `L == 2`, it is drop-in compatible
/// with `contracts/groth16/src/IxGroth16Verifier.sol`.
pub fn export_solidity_with_setup(
  vk: &VerifyingKey,
  is_development: bool,
) -> Result<String, String> {
  vk.validate()?;
  let num_public = vk.num_public_inputs();
  if num_public == 0 {
    return Err(
      "Solidity verifier export requires at least 1 public input".into(),
    );
  }

  let (alpha_x, alpha_y) = g1_dec(&vk.alpha_g1);
  let beta_neg = -vk.beta_g2;
  let gamma_neg = -vk.gamma_g2;
  let delta_neg = -vk.delta_g2;
  let (bx1, bx0, by1, by0) = g2_eip197_dec(&beta_neg);
  let (gx1, gx0, gy1, gy0) = g2_eip197_dec(&gamma_neg);
  let (dx1, dx0, dy1, dy0) = g2_eip197_dec(&delta_neg);

  let contract_name =
    if is_development { DEV_SOLIDITY_CONTRACT } else { "Groth16Verifier" };
  let mut out = String::with_capacity(4352 + num_public * 256);
  if is_development {
    out.push_str(DEV_SOLIDITY_HEADER);
  }

  let _ = writeln!(out, "// SPDX-License-Identifier: MIT OR Apache-2.0");
  let _ = writeln!(out, "pragma solidity ^0.8.28;");
  let _ = writeln!(out);
  let _ = writeln!(out, "/// @title BN254 Groth16 Verifier");
  let _ = writeln!(
    out,
    "/// @notice Generated deterministically by ix-proof-compression pure-Rust Groth16."
  );
  let _ = writeln!(
    out,
    "/// @dev Compatible with IxGroth16Verifier (IGroth16Verifier.verifyProof)."
  );
  let _ = writeln!(out, "contract {contract_name} {{");
  let _ = writeln!(out, "    error InvalidProofLength();");
  let _ = writeln!(out, "    error PublicInputNotInField();");
  let _ = writeln!(out, "    error ProofInvalid();");
  let _ = writeln!(out);
  let _ = writeln!(out, "    uint256 private constant PRECOMPILE_ADD = 0x06;");
  let _ = writeln!(out, "    uint256 private constant PRECOMPILE_MUL = 0x07;");
  let _ =
    writeln!(out, "    uint256 private constant PRECOMPILE_PAIRING = 0x08;");
  let _ = writeln!(out);
  let _ = writeln!(out, "    // BN254 base field P and scalar field R.");
  let _ = writeln!(out, "    uint256 private constant P = {BN254_P_DEC};");
  let _ = writeln!(out, "    uint256 private constant R = {BN254_R_DEC};");
  let _ = writeln!(out);
  let _ = writeln!(out, "    // Verifying key: [alpha]_1");
  let _ = writeln!(out, "    uint256 private constant ALPHA_X = {alpha_x};");
  let _ = writeln!(out, "    uint256 private constant ALPHA_Y = {alpha_y};");
  let _ = writeln!(out);
  let _ = writeln!(
    out,
    "    // Verifying key: -[beta]_2 (EIP-197 Fp2 order: c1 imaginary, c0 real)"
  );
  let _ = writeln!(out, "    uint256 private constant BETA_NEG_X_C1 = {bx1};");
  let _ = writeln!(out, "    uint256 private constant BETA_NEG_X_C0 = {bx0};");
  let _ = writeln!(out, "    uint256 private constant BETA_NEG_Y_C1 = {by1};");
  let _ = writeln!(out, "    uint256 private constant BETA_NEG_Y_C0 = {by0};");
  let _ = writeln!(out);
  let _ = writeln!(out, "    // Verifying key: -[gamma]_2");
  let _ = writeln!(out, "    uint256 private constant GAMMA_NEG_X_C1 = {gx1};");
  let _ = writeln!(out, "    uint256 private constant GAMMA_NEG_X_C0 = {gx0};");
  let _ = writeln!(out, "    uint256 private constant GAMMA_NEG_Y_C1 = {gy1};");
  let _ = writeln!(out, "    uint256 private constant GAMMA_NEG_Y_C0 = {gy0};");
  let _ = writeln!(out);
  let _ = writeln!(out, "    // Verifying key: -[delta]_2");
  let _ = writeln!(out, "    uint256 private constant DELTA_NEG_X_C1 = {dx1};");
  let _ = writeln!(out, "    uint256 private constant DELTA_NEG_X_C0 = {dx0};");
  let _ = writeln!(out, "    uint256 private constant DELTA_NEG_Y_C1 = {dy1};");
  let _ = writeln!(out, "    uint256 private constant DELTA_NEG_Y_C0 = {dy0};");
  let _ = writeln!(out);
  let _ =
    writeln!(out, "    // Public input query points IC[0..={num_public}]");
  for (idx, pt) in vk.ic.iter().enumerate() {
    let (x, y) = g1_dec(pt);
    let _ = writeln!(out, "    uint256 private constant IC_{idx}_X = {x};");
    let _ = writeln!(out, "    uint256 private constant IC_{idx}_Y = {y};");
  }
  let _ = writeln!(out);
  let _ = writeln!(
    out,
    "    function publicInputMSM(uint256[{num_public}] calldata publicInputs)"
  );
  let _ = writeln!(out, "        private");
  let _ = writeln!(out, "        view");
  let _ = writeln!(out, "        returns (uint256 x, uint256 y)");
  let _ = writeln!(out, "    {{");
  let _ = writeln!(out, "        bool success = true;");
  let _ = writeln!(out, "        assembly (\"memory-safe\") {{");
  let _ = writeln!(out, "            let f := mload(0x40)");
  let _ = writeln!(out, "            let g := add(f, 0x40)");
  let _ = writeln!(out, "            let tmp := add(f, 0xa0)");
  let _ = writeln!(out, "            let s");
  let _ = writeln!(out, "            let callOk");
  let _ = writeln!(out, "            mstore(f, IC_0_X)");
  let _ = writeln!(out, "            mstore(add(f, 0x20), IC_0_Y)");
  for i in 0..num_public {
    let ic_idx = i + 1;
    let byte_off = i * 32;
    let _ = writeln!(out);
    let _ = writeln!(out, "            mstore(g, IC_{ic_idx}_X)");
    let _ = writeln!(out, "            mstore(add(g, 0x20), IC_{ic_idx}_Y)");
    if byte_off == 0 {
      let _ = writeln!(out, "            s := calldataload(publicInputs)");
    } else {
      let _ = writeln!(
        out,
        "            s := calldataload(add(publicInputs, {byte_off}))"
      );
    }
    let _ = writeln!(out, "            mstore(add(g, 0x40), s)");
    let _ = writeln!(out, "            success := and(success, lt(s, R))");
    let _ = writeln!(out, "            mstore(tmp, 0)");
    let _ = writeln!(out, "            mstore(add(tmp, 0x20), 0)");
    let _ = writeln!(
      out,
      "            callOk := staticcall(gas(), PRECOMPILE_MUL, g, 0x60, tmp, 0x40)"
    );
    let _ = writeln!(
      out,
      "            success := and(success, and(callOk, eq(returndatasize(), 0x40)))"
    );
    let _ = writeln!(out, "            mstore(g, mload(tmp))");
    let _ =
      writeln!(out, "            mstore(add(g, 0x20), mload(add(tmp, 0x20)))");
    let _ = writeln!(out, "            mstore(tmp, 0)");
    let _ = writeln!(out, "            mstore(add(tmp, 0x20), 0)");
    let _ = writeln!(
      out,
      "            callOk := staticcall(gas(), PRECOMPILE_ADD, f, 0x80, tmp, 0x40)"
    );
    let _ = writeln!(
      out,
      "            success := and(success, and(callOk, eq(returndatasize(), 0x40)))"
    );
    let _ = writeln!(out, "            mstore(f, mload(tmp))");
    let _ =
      writeln!(out, "            mstore(add(f, 0x20), mload(add(tmp, 0x20)))");
  }
  let _ = writeln!(out);
  let _ = writeln!(out, "            x := mload(f)");
  let _ = writeln!(out, "            y := mload(add(f, 0x20))");
  let _ = writeln!(out, "        }}");
  let _ = writeln!(out, "        if (!success) {{");
  let _ = writeln!(out, "            revert PublicInputNotInField();");
  let _ = writeln!(out, "        }}");
  let _ = writeln!(out, "    }}");
  let _ = writeln!(out);
  let _ = writeln!(
    out,
    "    /// @notice Verify a 256-byte uncompressed BN254 Groth16 proof."
  );
  let _ = writeln!(
    out,
    "    /// @dev Reverts on invalid length, non-canonical public inputs, invalid points, or pairing failure."
  );
  let _ = writeln!(out, "    function verifyProof(");
  let _ = writeln!(out, "        bytes calldata proof,");
  let _ = writeln!(out, "        uint256[{num_public}] calldata publicInputs");
  let _ = writeln!(out, "    ) external view {{");
  let _ = writeln!(out, "        if (proof.length != 256) {{");
  let _ = writeln!(out, "            revert InvalidProofLength();");
  let _ = writeln!(out, "        }}");
  let _ = writeln!(
    out,
    "        (uint256 lx, uint256 ly) = publicInputMSM(publicInputs);"
  );
  let _ = writeln!(out);
  let _ = writeln!(out, "        bool success;");
  let _ = writeln!(out, "        assembly (\"memory-safe\") {{");
  let _ = writeln!(out, "            let f := mload(0x40)");
  let _ = writeln!(
    out,
    "            // Copy A (64 B) || B (128 B) || C (64 B) = 256 bytes (0x100)."
  );
  let _ = writeln!(out, "            calldatacopy(f, proof.offset, 0x100)");
  let _ = writeln!(out);
  let _ = writeln!(
    out,
    "            // Reject non-canonical base-field coordinates (>= P) before ecPairing."
  );
  let _ = writeln!(out, "            let inField := 1");
  let _ = writeln!(
    out,
    "            for {{ let off := 0 }} lt(off, 0x100) {{ off := add(off, 0x20) }} {{"
  );
  let _ = writeln!(
    out,
    "                inField := and(inField, lt(mload(add(f, off)), P))"
  );
  let _ = writeln!(out, "            }}");
  let _ = writeln!(out);
  let _ = writeln!(out, "            // Complete e(C, -delta)");
  let _ = writeln!(out, "            mstore(add(f, 0x100), DELTA_NEG_X_C1)");
  let _ = writeln!(out, "            mstore(add(f, 0x120), DELTA_NEG_X_C0)");
  let _ = writeln!(out, "            mstore(add(f, 0x140), DELTA_NEG_Y_C1)");
  let _ = writeln!(out, "            mstore(add(f, 0x160), DELTA_NEG_Y_C0)");
  let _ = writeln!(out);
  let _ = writeln!(out, "            // e(alpha, -beta)");
  let _ = writeln!(out, "            mstore(add(f, 0x180), ALPHA_X)");
  let _ = writeln!(out, "            mstore(add(f, 0x1a0), ALPHA_Y)");
  let _ = writeln!(out, "            mstore(add(f, 0x1c0), BETA_NEG_X_C1)");
  let _ = writeln!(out, "            mstore(add(f, 0x1e0), BETA_NEG_X_C0)");
  let _ = writeln!(out, "            mstore(add(f, 0x200), BETA_NEG_Y_C1)");
  let _ = writeln!(out, "            mstore(add(f, 0x220), BETA_NEG_Y_C0)");
  let _ = writeln!(out);
  let _ = writeln!(out, "            // e(L_pub, -gamma)");
  let _ = writeln!(out, "            mstore(add(f, 0x240), lx)");
  let _ = writeln!(out, "            mstore(add(f, 0x260), ly)");
  let _ = writeln!(out, "            mstore(add(f, 0x280), GAMMA_NEG_X_C1)");
  let _ = writeln!(out, "            mstore(add(f, 0x2a0), GAMMA_NEG_X_C0)");
  let _ = writeln!(out, "            mstore(add(f, 0x2c0), GAMMA_NEG_Y_C1)");
  let _ = writeln!(out, "            mstore(add(f, 0x2e0), GAMMA_NEG_Y_C0)");
  let _ = writeln!(out);
  let _ = writeln!(out, "            if inField {{");
  let _ = writeln!(out, "                let out := add(f, 0x300)");
  let _ = writeln!(out, "                mstore(out, 0)");
  let _ = writeln!(
    out,
    "                let pairOk := staticcall(gas(), PRECOMPILE_PAIRING, f, 0x300, out, 0x20)"
  );
  let _ = writeln!(
    out,
    "                success := and(pairOk, and(eq(returndatasize(), 0x20), eq(mload(out), 1)))"
  );
  let _ = writeln!(out, "            }}");
  let _ = writeln!(out, "        }}");
  let _ = writeln!(out, "        if (!success) {{");
  let _ = writeln!(out, "            revert ProofInvalid();");
  let _ = writeln!(out, "        }}");
  let _ = writeln!(out, "    }}");
  let _ = writeln!(out, "}}");

  Ok(out)
}
