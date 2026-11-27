//! Unit tests and 8/8 negative controls for pure-Rust BN254 Groth16.

use super::fermat_demo::{
  FERMAT_DEMO_DEV_SEED, FERMAT_MARGIN_NOTE, claim_digest_to_public_inputs,
  default_fermat_claim_digest, export_fermat_vector, fermat_demo_assignment,
  fermat_demo_r1cs, public_inputs_to_claim_digest,
};
use super::prover::{Proof, prove, prove_with_blinding};
use super::r1cs::{LinearCombination, R1cs};
use super::setup::setup_dev;
use super::solidity::export_solidity;
use super::verifier::{
  verify, verify_compressed_bytes, verify_evm_bytes,
  verify_evm_bytes_raw_publics,
};
use ark_bn254::{Fq, Fq2, Fr, G1Projective, G2Affine, G2Projective};
use ark_ec::{CurveGroup, PrimeGroup, short_weierstrass::SWCurveConfig};
use ark_ff::{BigInteger, Field, PrimeField};

/// Build a small R1CS proving `x^3 + x + 5 == out` (public input `out`).
fn cubic_r1cs() -> R1cs {
  let mut r1cs = R1cs::new(1);
  let out = r1cs.public_wire(0);
  let x = r1cs.alloc_private();
  let x_sq = r1cs.alloc_private();
  let x_cu = r1cs.alloc_private();

  let w = LinearCombination::from_wire;
  let five = LinearCombination::from_constant(Fr::from(5u64));

  // x * x = x_sq
  r1cs.add_constraint(w(x), w(x), w(x_sq));
  // x_sq * x = x_cu
  r1cs.add_constraint(w(x_sq), w(x), w(x_cu));
  // (x_cu + x + 5) * 1 = out
  r1cs.add_constraint(
    w(x_cu).add(&w(x)).add(&five),
    LinearCombination::from_constant(Fr::ONE),
    w(out),
  );
  r1cs
}

fn fr_to_be_bytes(v: Fr) -> [u8; 32] {
  let raw = v.into_bigint().to_bytes_be();
  let mut out = [0u8; 32];
  let start = 32 - raw.len();
  out[start..32].copy_from_slice(&raw);
  out
}

#[test]
fn r1cs_satisfaction_and_rejection() {
  let r1cs = cubic_r1cs();
  // x = 3 => 27 + 3 + 5 = 35
  let good = r1cs
    .make_assignment(
      &[Fr::from(35u64)],
      &[Fr::from(3u64), Fr::from(9u64), Fr::from(27u64)],
    )
    .expect("assignment shape");
  r1cs.is_satisfied(&good).expect("valid assignment");

  // Wrong output.
  let mut bad_out = good.clone();
  bad_out[1] = Fr::from(36u64);
  assert!(r1cs.is_satisfied(&bad_out).is_err());

  // Wrong wire 0 constant.
  let mut bad_one = good;
  bad_one[0] = Fr::from(2u64);
  assert!(r1cs.is_satisfied(&bad_one).is_err());
}

#[test]
fn small_r1cs_groth16_roundtrip_and_zk_blinding() {
  let r1cs = cubic_r1cs();
  let (pk, vk) = setup_dev(&r1cs, b"small-cubic-seed").expect("setup_dev");
  let assignment = r1cs
    .make_assignment(
      &[Fr::from(35u64)],
      &[Fr::from(3u64), Fr::from(9u64), Fr::from(27u64)],
    )
    .expect("assignment");
  let public_inputs = [Fr::from(35u64)];

  let proof_det =
    prove_with_blinding(&pk, &assignment, Fr::from(17u64), Fr::from(29u64))
      .expect("deterministic prove");
  verify(&vk, &public_inputs, &proof_det).expect("verify det");

  // Uncompressed 256-byte EVM roundtrip & 128-byte compressed roundtrip.
  let evm = proof_det.to_evm_bytes();
  assert_eq!(evm.len(), 256);
  verify_evm_bytes(&vk, &public_inputs, &evm).expect("verify evm bytes");

  let comp = proof_det.to_compressed_bytes();
  assert_eq!(comp.len(), 128);
  verify_compressed_bytes(&vk, &public_inputs, &comp)
    .expect("verify compressed bytes");

  // Fresh random ZK proofs differ in A, B, C yet both verify.
  let proof_r1 = prove(&pk, &assignment).expect("zk prove 1");
  let proof_r2 = prove(&pk, &assignment).expect("zk prove 2");
  assert_ne!(proof_r1.to_evm_bytes(), proof_r2.to_evm_bytes());
  verify(&vk, &public_inputs, &proof_r1).expect("verify r1");
  verify(&vk, &public_inputs, &proof_r2).expect("verify r2");
}

#[test]
fn fermat_demo_roundtrip_and_digest_limb_convention() {
  assert_eq!(FERMAT_MARGIN_NOTE.len(), 262);
  let digest = default_fermat_claim_digest();
  let limbs = claim_digest_to_public_inputs(&digest);
  let hi = u128::from_le_bytes(digest[0..16].try_into().expect("16B"));
  let lo = u128::from_le_bytes(digest[16..32].try_into().expect("16B"));
  assert_eq!(public_inputs_to_claim_digest(hi, lo), digest);
  assert_eq!(limbs, [Fr::from(hi), Fr::from(lo)]);

  let r1cs = fermat_demo_r1cs();
  let (pk, vk) = setup_dev(&r1cs, FERMAT_DEMO_DEV_SEED).expect("setup_dev");
  let (assignment, public_inputs) = fermat_demo_assignment(
    &digest,
    Fr::from(3u64),
    Fr::from(4u64),
    Fr::from(5u64),
  )
  .expect("fermat assignment");

  let proof = prove(&pk, &assignment).expect("fermat prove");
  let evm = proof.to_evm_bytes();
  let compressed = proof.to_compressed_bytes();
  assert_eq!(evm.len(), 256);
  assert_eq!(compressed.len(), 128);
  assert!(evm.len() < FERMAT_MARGIN_NOTE.len());

  verify(&vk, &public_inputs, &proof).expect("verify fermat proof");
  verify_evm_bytes(&vk, &public_inputs, &evm).expect("verify fermat evm");
  verify_compressed_bytes(&vk, &public_inputs, &compressed)
    .expect("verify fermat compressed");

  let vec = export_fermat_vector(&vk, &digest, &proof).expect("export vector");
  assert_eq!(vec.margin_note_bytes, 262);
  assert_eq!(vec.proof_evm_bytes, 256);
  assert_eq!(vec.proof_compressed_bytes, 128);
  assert_eq!(vec.vk.ic.len(), 3);
  let json = serde_json::to_string_pretty(&vec).expect("serialize vector");
  let decoded: super::fermat_demo::FermatDemoVector =
    serde_json::from_str(&json).expect("deserialize vector");
  assert_eq!(decoded, vec);
}

#[test]
fn fermat_demo_rejects_invalid_witnesses() {
  let digest = default_fermat_claim_digest();
  // Zero coordinate violates x·y·z != 0.
  assert!(
    fermat_demo_assignment(
      &digest,
      Fr::from(0u64),
      Fr::from(4u64),
      Fr::from(5u64)
    )
    .is_err()
  );
  // x^3 + y^3 == z^3 in Fr violates d != 0 (e.g., x = 1, y = -1, z = 0; or
  // x = 2, y = -2, z = 0). Also test non-zero triple with x^3 + y^3 == z^3
  // modulo r (impossible for small positives, trivial with y = -x and z = 0).
  assert!(
    fermat_demo_assignment(
      &digest,
      Fr::from(2u64),
      -Fr::from(2u64),
      Fr::from(0u64)
    )
    .is_err()
  );
}

#[test]
fn negative_controls_eight_of_eight_rejected() {
  let digest = default_fermat_claim_digest();
  let r1cs = fermat_demo_r1cs();
  let (pk, vk) = setup_dev(&r1cs, FERMAT_DEMO_DEV_SEED).expect("setup_dev");
  let (assignment, public_inputs) = fermat_demo_assignment(
    &digest,
    Fr::from(3u64),
    Fr::from(4u64),
    Fr::from(5u64),
  )
  .expect("fermat assignment");
  let proof =
    prove_with_blinding(&pk, &assignment, Fr::from(101u64), Fr::from(202u64))
      .expect("prove");
  verify(&vk, &public_inputs, &proof).expect("baseline valid proof");
  let evm = proof.to_evm_bytes();

  // 1. Wrong public input (flip LSB of pub_hi and pub_lo).
  let bad_pub_0 = [public_inputs[0] + Fr::ONE, public_inputs[1]];
  let bad_pub_1 = [public_inputs[0], public_inputs[1] + Fr::ONE];
  assert!(verify(&vk, &bad_pub_0, &proof).is_err());
  assert!(verify(&vk, &bad_pub_1, &proof).is_err());

  // 2. Tampered A (valid curve point, wrong proof element).
  let mut tampered_a = proof;
  tampered_a.a =
    (G1Projective::from(proof.a) + G1Projective::generator()).into_affine();
  assert!(verify(&vk, &public_inputs, &tampered_a).is_err());

  // 3. Tampered B (valid G2 subgroup point, wrong proof element).
  let mut tampered_b = proof;
  tampered_b.b =
    (G2Projective::from(proof.b) + G2Projective::generator()).into_affine();
  assert!(verify(&vk, &public_inputs, &tampered_b).is_err());

  // 4. Tampered C (valid curve point, wrong proof element).
  let mut tampered_c = proof;
  tampered_c.c =
    (G1Projective::from(proof.c) + G1Projective::generator()).into_affine();
  assert!(verify(&vk, &public_inputs, &tampered_c).is_err());

  // 5. Off-curve G1 and off-curve / non-subgroup G2 points.
  let mut off_curve_g1_bytes = evm;
  // Increment A.y by 1 => (x, y + 1) is off y^2 = x^3 + 3.
  off_curve_g1_bytes[63] ^= 0x01;
  assert!(verify_evm_bytes(&vk, &public_inputs, &off_curve_g1_bytes).is_err());

  let mut off_curve_g2_bytes = evm;
  off_curve_g2_bytes[191] ^= 0x01;
  assert!(verify_evm_bytes(&vk, &public_inputs, &off_curve_g2_bytes).is_err());

  // Also test an on-curve G2 point that is NOT in the prime-order subgroup!
  // On BN254 twist y^2 = x^3 + 3/(9+u), pick small x until y^2 is a square in
  // Fq2 and check that it fails subgroup check (cofactor h2 = 2p - r != 1).
  let non_subgroup_g2 = find_on_curve_non_subgroup_g2();
  assert!(non_subgroup_g2.is_on_curve());
  assert!(!non_subgroup_g2.is_in_correct_subgroup_assuming_on_curve());
  let mut bad_subgrp_proof = proof;
  bad_subgrp_proof.b = non_subgroup_g2;
  assert!(verify(&vk, &public_inputs, &bad_subgrp_proof).is_err());
  assert!(
    Proof::from_evm_bytes(&bad_subgrp_proof.to_evm_bytes()).is_err(),
    "from_evm_bytes must reject G2 point outside prime-order subgroup"
  );

  // Also test non-canonical Fq coordinate (>= p) in EVM bytes.
  let mut non_canon_fq = evm;
  non_canon_fq[0..32].fill(0xff);
  assert!(Proof::from_evm_bytes(&non_canon_fq).is_err());

  // 6. Wrong verifying key (different setup seed).
  let (_pk_other, vk_other) =
    setup_dev(&r1cs, b"different-seed-for-wrong-vk").expect("other setup");
  assert!(verify(&vk_other, &public_inputs, &proof).is_err());

  // 7. Swapped A and C.
  let swapped_ac = Proof { a: proof.c, b: proof.b, c: proof.a };
  assert_ne!(proof.a, proof.c);
  assert!(verify(&vk, &public_inputs, &swapped_ac).is_err());

  // 8. Non-canonical public input scalar (>= Fr::MODULUS).
  let r_bytes = Fr::MODULUS.to_bytes_be();
  let mut r_be = [0u8; 32];
  r_be[32 - r_bytes.len()..32].copy_from_slice(&r_bytes);
  let pub0_be = fr_to_be_bytes(public_inputs[0]);
  let pub1_be = fr_to_be_bytes(public_inputs[1]);
  // Sanity: canonical raw publics pass.
  verify_evm_bytes_raw_publics(&vk, &[pub0_be, pub1_be], &evm)
    .expect("canonical raw publics");
  // Exact modulus r fails.
  assert!(verify_evm_bytes_raw_publics(&vk, &[r_be, pub1_be], &evm).is_err());
  // 0xff..ff fails.
  assert!(
    verify_evm_bytes_raw_publics(&vk, &[pub0_be, [0xff; 32]], &evm).is_err()
  );
  // Also reject trailing or truncated proof bytes.
  let mut long_proof = evm.to_vec();
  long_proof.push(0);
  assert!(verify_evm_bytes(&vk, &public_inputs, &long_proof).is_err());
  assert!(verify_evm_bytes(&vk, &public_inputs, &evm[..255]).is_err());
}

fn find_on_curve_non_subgroup_g2() -> G2Affine {
  let twist_b = ark_bn254::g2::Config::COEFF_B;
  for k in 1u64..1000 {
    let x = Fq2::new(Fq::from(k), Fq::from(1u64));
    let rhs = x * x * x + twist_b;
    if let Some(y) = rhs.sqrt() {
      let pt = G2Affine::new_unchecked(x, y);
      if pt.is_on_curve() && !pt.is_in_correct_subgroup_assuming_on_curve() {
        return pt;
      }
    }
  }
  panic!("expected to find an on-curve non-subgroup G2 point");
}

#[test]
fn solidity_codegen_is_deterministic_and_matches_interface() {
  let r1cs = fermat_demo_r1cs();
  let (_pk, vk) = setup_dev(&r1cs, FERMAT_DEMO_DEV_SEED).expect("setup_dev");
  let sol_a = export_solidity(&vk).expect("export solidity 1");
  let sol_b = export_solidity(&vk).expect("export solidity 2");
  assert_eq!(sol_a, sol_b, "Solidity codegen must be deterministic");
  assert!(sol_a.contains("contract Groth16Verifier"));
  assert!(sol_a.contains("uint256[2] calldata publicInputs"));
  assert!(sol_a.contains("function verifyProof("));
  assert!(sol_a.contains("PRECOMPILE_ADD = 0x06"));
  assert!(sol_a.contains("PRECOMPILE_MUL = 0x07"));
  assert!(sol_a.contains("PRECOMPILE_PAIRING = 0x08"));
  assert!(sol_a.contains("IC_2_Y"));
}

#[test]
fn medium_r1cs_domain_256_roundtrip() {
  // 200-step squaring chain: w_{i+1} = w_i^2 + 1 => domain N = 256.
  let steps = 200usize;
  let mut r1cs = R1cs::new(2);
  let start_pub = r1cs.public_wire(0);
  let end_pub = r1cs.public_wire(1);

  let w = LinearCombination::from_wire;
  let one = LinearCombination::from_constant(Fr::ONE);

  let mut cur_wire = start_pub;
  let mut cur_val = Fr::from(7u64);
  let start_val = cur_val;
  let mut privates = Vec::with_capacity(steps);

  for step in 0..steps {
    let next_val = cur_val * cur_val + Fr::ONE;
    let next_wire = if step + 1 == steps {
      end_pub
    } else {
      let wire = r1cs.alloc_private();
      privates.push(next_val);
      wire
    };
    // cur * cur = next - 1
    r1cs.add_constraint(w(cur_wire), w(cur_wire), w(next_wire).sub(&one));
    cur_wire = next_wire;
    cur_val = next_val;
  }

  assert_eq!(r1cs.domain_size(), 256);
  let public_inputs = [start_val, cur_val];
  let assignment =
    r1cs.make_assignment(&public_inputs, &privates).expect("chain assignment");
  r1cs.is_satisfied(&assignment).expect("chain satisfied");

  let (pk, vk) = setup_dev(&r1cs, b"chain-256-seed").expect("setup_dev");
  let proof = prove(&pk, &assignment).expect("prove chain");
  let evm = proof.to_evm_bytes();
  assert_eq!(evm.len(), 256);
  verify_evm_bytes(&vk, &public_inputs, &evm).expect("verify chain");

  let wrong_end = [start_val, cur_val + Fr::ONE];
  assert!(verify_evm_bytes(&vk, &wrong_end, &evm).is_err());
}

#[test]
fn fq_modulus_exact_boundary_rejected_in_evm_proof() {
  let p_bytes = Fq::MODULUS.to_bytes_be();
  let mut p_be = [0u8; 32];
  p_be[32 - p_bytes.len()..32].copy_from_slice(&p_bytes);

  let mut buf = [0u8; 256];
  // Put exact Fq::MODULUS into A.x (bytes 0..32).
  buf[0..32].copy_from_slice(&p_be);
  assert!(Proof::from_evm_bytes(&buf).is_err());

  // Put exact Fq::MODULUS into B.y.c0 (bytes 160..192).
  buf[0..32].fill(0);
  buf[160..192].copy_from_slice(&p_be);
  assert!(Proof::from_evm_bytes(&buf).is_err());
}
