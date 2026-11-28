//! Fermat's Last Theorem 256-byte Margin Note Groth16 demonstration circuit.
//!
//! Pierre de Fermat's 1670 Diophantus margin note is 262 bytes of Latin text.
//! An uncompressed BN254 Groth16 proof is 256 bytes (256 < 262), and a
//! compressed proof is 128 bytes.
//!
//! Public inputs use the exact 2-limb `_reverse128` convention of
//! `contracts/groth16/src/IxGroth16Verifier.sol`:
//! - `pub_hi = Fr::from(u128::from_le_bytes(expected_claim_digest[0..16]))`
//! - `pub_lo = Fr::from(u128::from_le_bytes(expected_claim_digest[16..32]))`
//!
//! Private witness constraints prove knowledge of a non-zero cubic witness
//! `(x, y, z)` with `d = x^3 + y^3 - z^3` and `d · d_inv = 1` (proving
//! `x^3 + y^3 != z^3` in `Fr`), bound algebraically to `(pub_hi, pub_lo)`.

use super::prover::Proof;
use super::r1cs::{LinearCombination, R1cs};
use super::setup::VerifyingKey;
use ark_bn254::{Fq, Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{BigInteger, Field, PrimeField};
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

/// Samuel de Fermat's 1670 Diophantus Latin margin note (exact 262 bytes).
pub const FERMAT_MARGIN_NOTE: &str = "Cubum autem in duos cubos, aut quadratoquadratum in duos quadratoquadratos & generaliter nullam in infinitum ultra quadratum potestatem in duos eiusdem nominis fas est dividere cuius rei demonstrationem mirabilem sane detexi. Hanc marginis exiguitas non caperet.";

const _: () = assert!(FERMAT_MARGIN_NOTE.len() == 262);

/// Format tag for exported JSON verification vectors.
pub const FERMAT_VECTOR_FORMAT: &str = "ix-groth16-bn254-fermat-demo-v1";

/// Deterministic dev setup seed for the Fermat Margin Note demo.
pub const FERMAT_DEMO_DEV_SEED: &[u8] =
  b"ix/groth16/bn254/fermat-margin-note-demo/dev-unsafe/v1";

/// Decimal encoding of an affine BN254 G1 point.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct G1Decimal {
  pub x: String,
  pub y: String,
}

/// Decimal encoding of an affine BN254 G2 point (`x = x_c0 + x_c1·u`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct G2Decimal {
  pub x_c0: String,
  pub x_c1: String,
  pub y_c0: String,
  pub y_c1: String,
}

/// Self-contained decimal verifying key (including pre-negated G2 elements for
/// direct multi-pairing verification).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifyingKeyDecimal {
  pub alpha_g1: G1Decimal,
  pub beta_g2: G2Decimal,
  pub gamma_g2: G2Decimal,
  pub delta_g2: G2Decimal,
  pub beta_neg_g2: G2Decimal,
  pub gamma_neg_g2: G2Decimal,
  pub delta_neg_g2: G2Decimal,
  pub ic: Vec<G1Decimal>,
}

/// Self-contained decimal encoding of a Groth16 proof `(A, B, C)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofDecimal {
  pub a: G1Decimal,
  pub b: G2Decimal,
  pub c: G1Decimal,
}

/// Self-contained JSON cross-verification vector for Rust, Foundry EVM
/// (`IxGroth16Verifier`), and standalone `IxCC` x86 ELF verifiers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FermatDemoVector {
  pub format: String,
  pub security_note: String,
  pub margin_note_bytes: usize,
  pub proof_evm_bytes: usize,
  pub proof_compressed_bytes: usize,
  pub expected_claim_digest: String,
  pub public_inputs: [String; 2],
  pub proof_256_bytes: String,
  pub proof_128_compressed_bytes: String,
  pub proof: ProofDecimal,
  pub vk: VerifyingKeyDecimal,
}

/// Derive the default 32-byte claim digest from Fermat's 262-byte margin note.
pub fn default_fermat_claim_digest() -> [u8; 32] {
  *blake3::hash(FERMAT_MARGIN_NOTE.as_bytes()).as_bytes()
}

/// Convert a 32-byte `expectedClaimDigest` into `[pub_hi, pub_lo]` matching
/// `IxGroth16Verifier._reverse128`:
/// - `pub_hi = u128::from_le_bytes(digest[0..16])`
/// - `pub_lo = u128::from_le_bytes(digest[16..32])`
pub fn claim_digest_to_public_inputs(digest: &[u8; 32]) -> [Fr; 2] {
  let hi = u128::from_le_bytes(digest[0..16].try_into().expect("16 bytes"));
  let lo = u128::from_le_bytes(digest[16..32].try_into().expect("16 bytes"));
  [Fr::from(hi), Fr::from(lo)]
}

/// Reconstruct a 32-byte `expectedClaimDigest` from `[pub_hi, pub_lo]` 128-bit
/// limbs (inverse of [`claim_digest_to_public_inputs`]).
pub fn public_inputs_to_claim_digest(pub_hi: u128, pub_lo: u128) -> [u8; 32] {
  let mut out = [0u8; 32];
  out[0..16].copy_from_slice(&pub_hi.to_le_bytes());
  out[16..32].copy_from_slice(&pub_lo.to_le_bytes());
  out
}

/// Build the Fermat's Last Theorem Margin Note R1CS circuit.
///
/// Public inputs (`num_public = 2`):
/// - wire 1: `pub_hi` (first 16 bytes of `expectedClaimDigest`, LE u128)
/// - wire 2: `pub_lo` (second 16 bytes of `expectedClaimDigest`, LE u128)
///
/// Private witness wires (`19` private wires, `16` constraints, QAP domain
/// `N = 32`):
/// - `(x, y, z)` non-zero cubic witness (`x·y·z != 0`)
/// - `x^3 + y^3 - z^3 = d` with `d · d_inv = 1` (proves `x^3 + y^3 != z^3`)
/// - Algebraic cubic-sponge binding of `(pub_hi, pub_lo)` to `(d, x^3)`.
pub fn fermat_demo_r1cs() -> R1cs {
  let mut r1cs = R1cs::new(2);
  let pub_hi = r1cs.public_wire(0);
  let pub_lo = r1cs.public_wire(1);

  let x = r1cs.alloc_private();
  let y = r1cs.alloc_private();
  let z = r1cs.alloc_private();
  let x_sq = r1cs.alloc_private();
  let x_cu = r1cs.alloc_private();
  let y_sq = r1cs.alloc_private();
  let y_cu = r1cs.alloc_private();
  let z_sq = r1cs.alloc_private();
  let z_cu = r1cs.alloc_private();
  let d_inv = r1cs.alloc_private();
  let xy = r1cs.alloc_private();
  let xyz = r1cs.alloc_private();
  let xyz_inv = r1cs.alloc_private();
  let claim_mix = r1cs.alloc_private();
  let bind = r1cs.alloc_private();
  let s1_sq = r1cs.alloc_private();
  let s1_cu = r1cs.alloc_private();
  let s2_sq = r1cs.alloc_private();
  let s2_cu = r1cs.alloc_private();

  let w = LinearCombination::from_wire;
  let one = LinearCombination::from_constant(Fr::ONE);

  // Cubic powers: x^3, y^3, z^3.
  r1cs.add_constraint(w(x), w(x), w(x_sq));
  r1cs.add_constraint(w(x_sq), w(x), w(x_cu));
  r1cs.add_constraint(w(y), w(y), w(y_sq));
  r1cs.add_constraint(w(y_sq), w(y), w(y_cu));
  r1cs.add_constraint(w(z), w(z), w(z_sq));
  r1cs.add_constraint(w(z_sq), w(z), w(z_cu));

  // Non-equality: d = x^3 + y^3 - z^3 != 0 via d · d_inv = 1.
  let d_lc = w(x_cu).add(&w(y_cu)).sub(&w(z_cu));
  r1cs.add_constraint(d_lc.clone(), w(d_inv), one.clone());

  // Non-triviality: x != 0, y != 0, z != 0 via (x · y · z) · xyz_inv = 1.
  r1cs.add_constraint(w(x), w(y), w(xy));
  r1cs.add_constraint(w(xy), w(z), w(xyz));
  r1cs.add_constraint(w(xyz), w(xyz_inv), one);

  // Claim binding constraints tying pub_hi and pub_lo to the cubic witness.
  r1cs.add_constraint(w(pub_hi), w(pub_lo), w(claim_mix));

  let bind_a = w(pub_hi).add(&w(pub_lo).scale(Fr::from(2u64))).add(&d_lc);
  let bind_b = w(pub_hi).add(&w(pub_lo).scale(Fr::from(3u64))).add(&w(x_cu));
  r1cs.add_constraint(bind_a, bind_b, w(bind));

  // Two-step cubic S-box binding s1 = pub_hi + d, s2 = pub_lo + s1^3.
  let s1_lc = w(pub_hi).add(&d_lc);
  r1cs.add_constraint(s1_lc.clone(), s1_lc.clone(), w(s1_sq));
  r1cs.add_constraint(w(s1_sq), s1_lc, w(s1_cu));

  let s2_lc = w(pub_lo).add(&w(s1_cu));
  r1cs.add_constraint(s2_lc.clone(), s2_lc.clone(), w(s2_sq));
  r1cs.add_constraint(w(s2_sq), s2_lc, w(s2_cu));

  r1cs
}

/// Compute a satisfying full R1CS wire assignment for [`fermat_demo_r1cs`]
/// given `expected_claim_digest` and non-zero cubic witness `(x, y, z)` with
/// `x^3 + y^3 != z^3`.
pub fn fermat_demo_assignment(
  expected_claim_digest: &[u8; 32],
  x: Fr,
  y: Fr,
  z: Fr,
) -> Result<(Vec<Fr>, [Fr; 2]), String> {
  let public_inputs = claim_digest_to_public_inputs(expected_claim_digest);
  let [pub_hi, pub_lo] = public_inputs;

  let x_sq = x * x;
  let x_cu = x_sq * x;
  let y_sq = y * y;
  let y_cu = y_sq * y;
  let z_sq = z * z;
  let z_cu = z_sq * z;

  let d = x_cu + y_cu - z_cu;
  let d_inv = d
    .inverse()
    .ok_or("witness violates x^3 + y^3 != z^3 (difference is zero)")?;

  let xy = x * y;
  let xyz = xy * z;
  let xyz_inv = xyz
    .inverse()
    .ok_or("witness triple (x, y, z) must be non-zero in every coordinate")?;

  let claim_mix = pub_hi * pub_lo;
  let bind = (pub_hi + Fr::from(2u64) * pub_lo + d)
    * (pub_hi + Fr::from(3u64) * pub_lo + x_cu);

  let s1 = pub_hi + d;
  let s1_sq = s1 * s1;
  let s1_cu = s1_sq * s1;

  let s2 = pub_lo + s1_cu;
  let s2_sq = s2 * s2;
  let s2_cu = s2_sq * s2;

  let private_witness = [
    x, y, z, x_sq, x_cu, y_sq, y_cu, z_sq, z_cu, d_inv, xy, xyz, xyz_inv,
    claim_mix, bind, s1_sq, s1_cu, s2_sq, s2_cu,
  ];

  let r1cs = fermat_demo_r1cs();
  let assignment = r1cs.make_assignment(&public_inputs, &private_witness)?;
  r1cs.is_satisfied(&assignment)?;
  Ok((assignment, public_inputs))
}

fn fq_to_dec(v: Fq) -> String {
  BigUint::from_bytes_le(&v.into_bigint().to_bytes_le()).to_string()
}

fn fr_to_dec(v: Fr) -> String {
  BigUint::from_bytes_le(&v.into_bigint().to_bytes_le()).to_string()
}

fn g1_to_dec(pt: &G1Affine) -> G1Decimal {
  if pt.is_zero() {
    G1Decimal { x: "0".into(), y: "0".into() }
  } else {
    G1Decimal { x: fq_to_dec(pt.x), y: fq_to_dec(pt.y) }
  }
}

fn g2_to_dec(pt: &G2Affine) -> G2Decimal {
  if pt.is_zero() {
    G2Decimal {
      x_c0: "0".into(),
      x_c1: "0".into(),
      y_c0: "0".into(),
      y_c1: "0".into(),
    }
  } else {
    G2Decimal {
      x_c0: fq_to_dec(pt.x.c0),
      x_c1: fq_to_dec(pt.x.c1),
      y_c0: fq_to_dec(pt.y.c0),
      y_c1: fq_to_dec(pt.y.c1),
    }
  }
}

fn hex_0x(bytes: &[u8]) -> String {
  const HEX: &[u8; 16] = b"0123456789abcdef";
  let mut s = String::with_capacity(2 + bytes.len() * 2);
  s.push_str("0x");
  for &b in bytes {
    s.push(HEX[usize::from(b >> 4)] as char);
    s.push(HEX[usize::from(b & 0x0f)] as char);
  }
  s
}

/// Export a self-contained JSON verification vector for Rust, Foundry EVM, and
/// `IxCC` x86 ELF cross-verification.
pub fn export_fermat_vector(
  vk: &VerifyingKey,
  expected_claim_digest: &[u8; 32],
  proof: &Proof,
) -> Result<FermatDemoVector, String> {
  vk.validate()?;
  if vk.num_public_inputs() != 2 {
    return Err(format!(
      "Fermat demo vector requires 2 public inputs, got {}",
      vk.num_public_inputs()
    ));
  }
  let public_inputs = claim_digest_to_public_inputs(expected_claim_digest);
  let evm_bytes = proof.to_evm_bytes();
  let compressed_bytes = proof.to_compressed_bytes();
  let beta_neg = -vk.beta_g2;
  let gamma_neg = -vk.gamma_g2;
  let delta_neg = -vk.delta_g2;

  Ok(FermatDemoVector {
    format: FERMAT_VECTOR_FORMAT.into(),
    security_note: "DEV/UNSAFE deterministic setup — no trusted setup ceremony"
      .into(),
    margin_note_bytes: FERMAT_MARGIN_NOTE.len(),
    proof_evm_bytes: Proof::EVM_BYTES,
    proof_compressed_bytes: Proof::COMPRESSED_BYTES,
    expected_claim_digest: hex_0x(expected_claim_digest),
    public_inputs: [fr_to_dec(public_inputs[0]), fr_to_dec(public_inputs[1])],
    proof_256_bytes: hex_0x(&evm_bytes),
    proof_128_compressed_bytes: hex_0x(&compressed_bytes),
    proof: ProofDecimal {
      a: g1_to_dec(&proof.a),
      b: g2_to_dec(&proof.b),
      c: g1_to_dec(&proof.c),
    },
    vk: VerifyingKeyDecimal {
      alpha_g1: g1_to_dec(&vk.alpha_g1),
      beta_g2: g2_to_dec(&vk.beta_g2),
      gamma_g2: g2_to_dec(&vk.gamma_g2),
      delta_g2: g2_to_dec(&vk.delta_g2),
      beta_neg_g2: g2_to_dec(&beta_neg),
      gamma_neg_g2: g2_to_dec(&gamma_neg),
      delta_neg_g2: g2_to_dec(&delta_neg),
      ic: vk.ic.iter().map(g1_to_dec).collect(),
    },
  })
}
