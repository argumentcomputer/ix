//! Pure-Rust Solidity PLONK (+ BSB22) verifier generator for both BN254
//! (EIP-196/197) and BLS12-381 (EIP-2537).
//!
//! Substitutes all `G2_SRS_*`, `G1_SRS_*`, `VK_*`, `VK_QCP_0_*`, and
//! `VK_INDEX_COMMIT_API_0` constants directly from [`VerifyingKey`] into the
//! verified Solidity templates in `contracts/plonk/`, including BLS12-381
//! infinity-flag fixups (`0x40`) for transcript hashing whenever a VK G1 point
//! is the point at infinity. Zero Go required.

use super::preprocess::VerifyingKey;
use crate::kzg::curve::{Bls12381, Bn254, Curve, KzgCurve};
use crate::pipeline::SetupClass;
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, PrimeField};
use num_bigint::BigUint;
use std::fmt::Write;

const BN254_TEMPLATE: &str =
  include_str!("../../../../../../contracts/plonk/src/PlonkVerifier.sol");
const BLS12_381_TEMPLATE: &str = include_str!(
  "../../../../../../contracts/plonk/testdata/bls12-381/Bls12381PlonkVerifier.sol"
);

const HEADER_END_MARKER: &str =
  "  // ------------------------------------------------";

pub const DEV_SOLIDITY_CONTRACT: &str =
  "PlonkVerifier_DEV_INSECURE_DO_NOT_DEPLOY";
pub const DEV_SOLIDITY_HEADER: &str = "\
// WARNING: GENERATED FROM A DEVELOPMENT TRAPDOOR SRS — DO NOT DEPLOY\n\
// This verifying key's SRS anchors do not match the released ceremony\n\
// parameters; anyone holding the trapdoor can forge arbitrary proofs.\n\n";

/// Output filename for `vk`'s exported Solidity verifier. Development setups
/// never emit an unmarked `PlonkVerifier.sol` / `Bls12381PlonkVerifier.sol`.
pub fn solidity_filename_for_vk<C: KzgCurve>(
  vk: &VerifyingKey<C>,
) -> &'static str {
  let is_dev = vk.setup_class() == SetupClass::Development;
  match (C::CURVE, is_dev) {
    (Curve::Bn254, false) => "PlonkVerifier.sol",
    (Curve::Bn254, true) => "PlonkVerifier.DEV_INSECURE.sol",
    (Curve::Bls12381, false) => "Bls12381PlonkVerifier.sol",
    (Curve::Bls12381, true) => "Bls12381PlonkVerifier.DEV_INSECURE.sol",
  }
}

fn bn_fq_dec(val: ark_bn254::Fq) -> String {
  BigUint::from_bytes_le(&val.into_bigint().to_bytes_le()).to_string()
}

fn bn_fr_dec(val: ark_bn254::Fr) -> String {
  BigUint::from_bytes_le(&val.into_bigint().to_bytes_le()).to_string()
}

fn bls_fr_dec(val: ark_bls12_381::Fr) -> String {
  BigUint::from_bytes_le(&val.into_bigint().to_bytes_le()).to_string()
}

/// Split a 381-bit BLS12-381 `Fq` element into `(lo_decimal, hi_decimal)` where
/// `val = hi * 2^256 + lo` and `0 <= lo < 2^256`.
fn bls_fq_lo_hi_dec(val: ark_bls12_381::Fq) -> (String, String) {
  let limbs = val.into_bigint().0;
  let mut lo_bytes = [0u8; 32];
  for i in 0..4 {
    lo_bytes[8 * i..8 * i + 8].copy_from_slice(&limbs[i].to_le_bytes());
  }
  let mut hi_bytes = [0u8; 16];
  hi_bytes[0..8].copy_from_slice(&limbs[4].to_le_bytes());
  hi_bytes[8..16].copy_from_slice(&limbs[5].to_le_bytes());
  let lo = BigUint::from_bytes_le(&lo_bytes).to_string();
  let hi = BigUint::from_bytes_le(&hi_bytes).to_string();
  (lo, hi)
}

fn bn_g1_xy(p: ark_bn254::G1Affine) -> (String, String) {
  if p.is_zero() {
    ("0".into(), "0".into())
  } else {
    (bn_fq_dec(p.x), bn_fq_dec(p.y))
  }
}

fn bls_g1_xy(
  p: ark_bls12_381::G1Affine,
) -> ((String, String), (String, String)) {
  if p.is_zero() {
    (("0".into(), "0".into()), ("0".into(), "0".into()))
  } else {
    (bls_fq_lo_hi_dec(p.x), bls_fq_lo_hi_dec(p.y))
  }
}

/// Export a standalone deterministic Solidity verifier contract for `vk`
/// (`PlonkVerifier` for BN254 or BLS12-381).
pub fn export_solidity<C: KzgCurve>(
  vk: &VerifyingKey<C>,
) -> Result<String, String> {
  vk.validate_structure()?;
  if vk.qcp.len() != 1 || vk.commitment_constraint_indexes.len() != 1 {
    return Err(
      "Solidity verifier export requires exactly one BSB22 commitment".into(),
    );
  }
  match C::CURVE {
    Curve::Bn254 => {
      // Safe curve-monomorphized conversion via canonical bytes round-trip.
      let bytes = vk.to_bytes()?;
      let bn_vk = VerifyingKey::<Bn254>::from_bytes(&bytes)?;
      export_bn254_solidity(&bn_vk)
    },
    Curve::Bls12381 => {
      let bytes = vk.to_bytes()?;
      let bls_vk = VerifyingKey::<Bls12381>::from_bytes(&bytes)?;
      export_bls12_381_solidity(&bls_vk)
    },
  }
}

/// Export BN254 EIP-196/197 `PlonkVerifier.sol`.
pub fn export_bn254_solidity(
  vk: &VerifyingKey<Bn254>,
) -> Result<String, String> {
  let tail_pos = BN254_TEMPLATE
    .find(HEADER_END_MARKER)
    .ok_or("BN254 Solidity template missing header delimiter")?;
  let body = &BN254_TEMPLATE[tail_pos..];

  let is_dev = vk.setup_class() == SetupClass::Development;
  let contract_name =
    if is_dev { DEV_SOLIDITY_CONTRACT } else { "PlonkVerifier" };
  let mut out = String::with_capacity(BN254_TEMPLATE.len() + 512);
  if is_dev {
    out.push_str(DEV_SOLIDITY_HEADER);
  }
  out.push_str(
    "// SPDX-License-Identifier: Apache-2.0\n\n\
     // Copyright 2023 Consensys Software Inc.\n\
     //\n\
     // Licensed under the Apache License, Version 2.0 (the \"License\");\n\
     // you may not use this file except in compliance with the License.\n\
     // You may obtain a copy of the License at\n\
     //\n\
     //     http://www.apache.org/licenses/LICENSE-2.0\n\
     //\n\
     // Unless required by applicable law or agreed to in writing, software\n\
     // distributed under the License is distributed on an \"AS IS\" BASIS,\n\
     // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n\
     // See the License for the specific language governing permissions and\n\
     // limitations under the License.\n\n\
     // Code generated by ix-proof-compression native PLONK exporter\n\n\
     pragma solidity ^0.8.0;\n\n",
  );
  let _ = writeln!(out, "contract {contract_name} {{");
  out.push_str(
    "\n\
       uint256 private constant R_MOD = 21888242871839275222246405745257275088548364400416034343698204186575808495617;\n\
       uint256 private constant R_MOD_MINUS_ONE = 21888242871839275222246405745257275088548364400416034343698204186575808495616;\n\
       uint256 private constant P_MOD = 21888242871839275222246405745257275088696311157297823662689037894645226208583;\n",
  );

  // BN254 EIP-197 G2 order is (c1, c0) = (A1, A0).
  for (idx, g2) in [vk.g2, vk.tau_g2].iter().enumerate() {
    let _ = writeln!(out, "  ");
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_X_0 = {};",
      bn_fq_dec(g2.x.c1)
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_X_1 = {};",
      bn_fq_dec(g2.x.c0)
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_Y_0 = {};",
      bn_fq_dec(g2.y.c1)
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_Y_1 = {};",
      bn_fq_dec(g2.y.c0)
    );
  }
  let (g1_x, g1_y) = bn_g1_xy(vk.g1);
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  uint256 private constant G1_SRS_X = {g1_x};");
  let _ = writeln!(out, "  uint256 private constant G1_SRS_Y = {g1_y};");
  let _ = writeln!(out);
  let _ =
    writeln!(out, "  // ----------------------- vk ---------------------");
  let _ = writeln!(
    out,
    "  uint256 private constant VK_NB_PUBLIC_INPUTS = {};",
    vk.num_public_inputs
  );
  let _ = writeln!(
    out,
    "  uint256 private constant VK_DOMAIN_SIZE = {};",
    vk.domain_size
  );
  let _ = writeln!(
    out,
    "  uint256 private constant VK_INV_DOMAIN_SIZE = {};",
    bn_fr_dec(vk.domain_size_inv)
  );
  let _ = writeln!(
    out,
    "  uint256 private constant VK_OMEGA = {};",
    bn_fr_dec(vk.omega)
  );

  for (name, point) in
    [("QL", vk.ql), ("QR", vk.qr), ("QM", vk.qm), ("QO", vk.qo), ("QK", vk.qk)]
  {
    let (x, y) = bn_g1_xy(point);
    let _ = writeln!(out, "  uint256 private constant VK_{name}_COM_X = {x};");
    let _ = writeln!(out, "  uint256 private constant VK_{name}_COM_Y = {y};");
  }
  for (i, &point) in vk.s.iter().enumerate() {
    let (x, y) = bn_g1_xy(point);
    let idx = i + 1;
    let _ = writeln!(out, "  ");
    let _ = writeln!(out, "  uint256 private constant VK_S{idx}_COM_X = {x};");
    let _ = writeln!(out, "  uint256 private constant VK_S{idx}_COM_Y = {y};");
  }
  let _ = writeln!(out, "  ");
  let _ = writeln!(
    out,
    "  uint256 private constant VK_COSET_SHIFT = {};",
    bn_fr_dec(vk.coset_shift)
  );
  let (qcp_x, qcp_y) = bn_g1_xy(vk.qcp[0]);
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  uint256 private constant VK_QCP_0_X = {qcp_x};");
  let _ = writeln!(out, "  uint256 private constant VK_QCP_0_Y = {qcp_y};");
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  ");
  let _ = writeln!(
    out,
    "  uint256 private constant VK_INDEX_COMMIT_API_0 = {};",
    vk.commitment_constraint_indexes[0]
  );
  let _ = writeln!(out, "  uint256 private constant VK_NB_CUSTOM_GATES = 1;");
  let _ = writeln!(out);
  out.push_str(body);
  Ok(out)
}

/// Export BLS12-381 EIP-2537 `Bls12381PlonkVerifier.sol`.
pub fn export_bls12_381_solidity(
  vk: &VerifyingKey<Bls12381>,
) -> Result<String, String> {
  let tail_pos = BLS12_381_TEMPLATE
    .find(HEADER_END_MARKER)
    .ok_or("BLS12-381 Solidity template missing header delimiter")?;
  let mut body = BLS12_381_TEMPLATE[tail_pos..].to_owned();

  // Inject gnark BLS12-381 infinity-flag fixups (`0x40`) for any zero VK G1
  // commitments in `derive_gamma` and `compute_gamma_kzg`.
  let gamma_points =
    [vk.s[0], vk.s[1], vk.s[2], vk.ql, vk.qr, vk.qm, vk.qo, vk.qk, vk.qcp[0]];
  let mut gamma_fixups = String::new();
  for (i, pt) in gamma_points.iter().enumerate() {
    if pt.is_zero() {
      let off = 0x20 + i * 0x60;
      let _ =
        writeln!(gamma_fixups, "        mstore8(add(mPtr, 0x{off:x}), 0x40)");
    }
  }
  if !gamma_fixups.is_empty() {
    let marker = "        // public inputs\n";
    let pos = body
      .find(marker)
      .ok_or("BLS12-381 template missing derive_gamma public inputs marker")?;
    let patch = format!(
      "        // --- Infinity flag fixups (Marshal sets 0x40 for identity) ---\n\
       {gamma_fixups}\n"
    );
    body.insert_str(pos, &patch);
  }

  // In `compute_gamma_kzg`: S1 is at mPtr + 0x1c0, S2 at 0x220, Qcp_0 at 0x280.
  let mut kzg_fixups = String::new();
  for (pt, off) in
    [(vk.s[0], 0x1c0usize), (vk.s[1], 0x220usize), (vk.qcp[0], 0x280usize)]
  {
    if pt.is_zero() {
      let _ =
        writeln!(kzg_fixups, "        mstore8(add(mPtr, 0x{off:x}), 0x40)");
    }
  }
  if !kzg_fixups.is_empty() {
    let marker = "        mstore(add(mPtr, 0x2e0), mload(add(state, STATE_OPENING_LINEARISED_POLYNOMIAL_ZETA)))";
    let pos = body
      .find(marker)
      .ok_or("BLS12-381 template missing compute_gamma_kzg marker")?;
    body.insert_str(pos, &kzg_fixups);
  }

  let is_dev = vk.setup_class() == SetupClass::Development;
  let contract_name =
    if is_dev { DEV_SOLIDITY_CONTRACT } else { "PlonkVerifier" };
  let mut out = String::with_capacity(BLS12_381_TEMPLATE.len() + 768);
  if is_dev {
    out.push_str(DEV_SOLIDITY_HEADER);
  }
  out.push_str(
    "// SPDX-License-Identifier: Apache-2.0\n\n\
     // Copyright 2023 Consensys Software Inc.\n\
     //\n\
     // Licensed under the Apache License, Version 2.0 (the \"License\");\n\
     // you may not use this file except in compliance with the License.\n\
     // You may obtain a copy of the License at\n\
     //\n\
     //     http://www.apache.org/licenses/LICENSE-2.0\n\
     //\n\
     // Unless required by applicable law or agreed to in writing, software\n\
     // distributed under the License is distributed on an \"AS IS\" BASIS,\n\
     // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\n\
     // See the License for the specific language governing permissions and\n\
     // limitations under the License.\n\n\
     // Code generated by ix-proof-compression native PLONK exporter\n\n\
     pragma solidity ^0.8.0;\n\n",
  );
  let _ = writeln!(out, "contract {contract_name} {{");
  out.push_str(
    "\n\
       uint256 private constant R_MOD = 52435875175126190479447740508185965837690552500527637822603658699938581184513;\n\
       uint256 private constant R_MOD_MINUS_ONE = 52435875175126190479447740508185965837690552500527637822603658699938581184512;\n",
  );

  // BLS12-381 EIP-2537 G2 order is (c0, c1) = (A0, A1).
  for (idx, g2) in [vk.g2, vk.tau_g2].iter().enumerate() {
    let (x0_lo, x0_hi) = bls_fq_lo_hi_dec(g2.x.c0);
    let (x1_lo, x1_hi) = bls_fq_lo_hi_dec(g2.x.c1);
    let (y0_lo, y0_hi) = bls_fq_lo_hi_dec(g2.y.c0);
    let (y1_lo, y1_hi) = bls_fq_lo_hi_dec(g2.y.c1);
    let _ = writeln!(out, "  ");
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_X_0_lo = {x0_lo};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_X_0_hi = {x0_hi};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_X_1_lo = {x1_lo};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_X_1_hi = {x1_hi};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_Y_0_lo = {y0_lo};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_Y_0_hi = {y0_hi};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_Y_1_lo = {y1_lo};"
    );
    let _ = writeln!(
      out,
      "  uint256 private constant G2_SRS_{idx}_Y_1_hi = {y1_hi};"
    );
  }
  let ((g1_x_lo, g1_x_hi), (g1_y_lo, g1_y_hi)) = bls_g1_xy(vk.g1);
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  uint256 private constant G1_SRS_X_lo = {g1_x_lo};");
  let _ = writeln!(out, "  uint256 private constant G1_SRS_X_hi = {g1_x_hi};");
  let _ = writeln!(out, "  uint256 private constant G1_SRS_Y_lo = {g1_y_lo};");
  let _ = writeln!(out, "  uint256 private constant G1_SRS_Y_hi = {g1_y_hi};");
  let _ = writeln!(out);
  let _ =
    writeln!(out, "  // ----------------------- vk ---------------------");
  let _ = writeln!(
    out,
    "  uint256 private constant VK_NB_PUBLIC_INPUTS = {};",
    vk.num_public_inputs
  );
  let _ = writeln!(
    out,
    "  uint256 private constant VK_DOMAIN_SIZE = {};",
    vk.domain_size
  );
  let _ = writeln!(
    out,
    "  uint256 private constant VK_INV_DOMAIN_SIZE = {};",
    bls_fr_dec(vk.domain_size_inv)
  );
  let _ = writeln!(
    out,
    "  uint256 private constant VK_OMEGA = {};",
    bls_fr_dec(vk.omega)
  );

  for (name, point) in
    [("QL", vk.ql), ("QR", vk.qr), ("QM", vk.qm), ("QO", vk.qo), ("QK", vk.qk)]
  {
    let ((x_lo, x_hi), (y_lo, y_hi)) = bls_g1_xy(point);
    let _ =
      writeln!(out, "  uint256 private constant VK_{name}_COM_X_lo = {x_lo};");
    let _ =
      writeln!(out, "  uint256 private constant VK_{name}_COM_X_hi = {x_hi};");
    let _ =
      writeln!(out, "  uint256 private constant VK_{name}_COM_Y_lo = {y_lo};");
    let _ =
      writeln!(out, "  uint256 private constant VK_{name}_COM_Y_hi = {y_hi};");
  }
  for (i, &point) in vk.s.iter().enumerate() {
    let ((x_lo, x_hi), (y_lo, y_hi)) = bls_g1_xy(point);
    let idx = i + 1;
    let _ = writeln!(out, "  ");
    let _ =
      writeln!(out, "  uint256 private constant VK_S{idx}_COM_X_lo = {x_lo};");
    let _ =
      writeln!(out, "  uint256 private constant VK_S{idx}_COM_X_hi = {x_hi};");
    let _ =
      writeln!(out, "  uint256 private constant VK_S{idx}_COM_Y_lo = {y_lo};");
    let _ =
      writeln!(out, "  uint256 private constant VK_S{idx}_COM_Y_hi = {y_hi};");
  }
  let _ = writeln!(out, "  ");
  let _ = writeln!(
    out,
    "  uint256 private constant VK_COSET_SHIFT = {};",
    bls_fr_dec(vk.coset_shift)
  );
  let ((qcp_x_lo, qcp_x_hi), (qcp_y_lo, qcp_y_hi)) = bls_g1_xy(vk.qcp[0]);
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  ");
  let _ =
    writeln!(out, "  uint256 private constant VK_QCP_0_X_lo = {qcp_x_lo};");
  let _ =
    writeln!(out, "  uint256 private constant VK_QCP_0_X_hi = {qcp_x_hi};");
  let _ =
    writeln!(out, "  uint256 private constant VK_QCP_0_Y_lo = {qcp_y_lo};");
  let _ =
    writeln!(out, "  uint256 private constant VK_QCP_0_Y_hi = {qcp_y_hi};");
  let _ = writeln!(out, "  ");
  let _ = writeln!(out, "  ");
  let _ = writeln!(
    out,
    "  uint256 private constant VK_INDEX_COMMIT_API_0 = {};",
    vk.commitment_constraint_indexes[0]
  );
  let _ = writeln!(out, "  uint256 private constant VK_NB_CUSTOM_GATES = 1;");
  let _ = writeln!(out);
  out.push_str(&body);
  Ok(out)
}
