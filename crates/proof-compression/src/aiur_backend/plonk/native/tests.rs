use super::*;
use crate::aiur_backend::plonk::scs::{Table, serialize_binary_witness};
use crate::kzg::{
  Srs, VerifierParams,
  curve::{Bls12381, Bn254, G1AffineOf, G1ProjectiveOf, KzgCurve},
  field::CurveScalar,
};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{BigInteger, PrimeField};
use num_bigint::BigUint;
use sha2::{Digest, Sha256};

use super::scs_file::{SEL_L, SEL_M, SEL_O, SEL_R};
use super::transcript::{
  BSB22_DST, decode_fr_be_canonical, decode_g1_raw, fr_be_bytes, g1_raw_bytes,
  g1_raw_len, hash_fr_bsb22,
};

/// Build a synthetic `ix-aiur-scs-v1` circuit that exercises every feature of
/// Lean's format and the two-phase solver:
/// - 2 public inputs (`w0`, `w1`),
/// - `num_outputs` private output wires (`0` for self-contained in-circuit
///   pairing or `18`/`22` for deferred pairing),
/// - private witness wires (`x`, `y`, `m`),
/// - pre-commitment quadratic + linear gates tying `(x, y)` to `(pub0, pub1)`,
/// - BSB22 commitment on input wires,
/// - post-commitment `gamma` challenge (`WireHint::Challenge`),
/// - `beta` 4-bit decomposition gadget (`WireHint::Bit` + boolean + linear
///   reconstruction gates),
/// - 4 post-commitment LogUp quotient gates (`q * d = num`, Montgomery batch
///   inversion path),
/// - 5-link running-sum chain (`u_k = u_{k-1} + c * t_k`, segmented chain
///   path) summing to `0` identically for any `gamma`,
/// - `WireHint::Free` wire in the final check gate.
fn build_rich_scs<C: KzgCurve>(
  num_outputs: usize,
) -> (Vec<u8>, Vec<C::Fr>, Vec<C::Fr>) {
  let one = C::FR_ONE;
  let neg_one = C::FR_NEG_ONE;
  let two = C::Fr::from(2u64);
  let four = C::Fr::from(4u64);
  let eight = C::Fr::from(8u64);
  let coeffs = vec![one, neg_one, two, four, eight];
  const C_POS1: u32 = 0;
  const C_NEG1: u32 = 1;
  const C_POS2: u32 = 2;
  const C_POS4: u32 = 3;
  const C_POS8: u32 = 4;

  // Input wires: [pub0, pub1, out_0..out_{num_outputs-1}, x, y, m].
  let publics = 2usize;
  let outputs: Vec<u32> = (0..num_outputs)
    .map(|k| u32::try_from(publics + k).expect("fits u32"))
    .collect();
  let w_x = u32::try_from(publics + num_outputs).expect("fits u32");
  let w_y = w_x + 1;
  let w_m = w_x + 2;
  let cells = (w_m as usize) + 1;

  let mut hints = vec![WireHint::Input; cells];
  let mut add_wire = |hint: WireHint| -> u32 {
    let id = u32::try_from(hints.len()).expect("wire fits u32");
    hints.push(hint);
    id
  };

  let mut gates: Vec<PackedGate> = Vec::new();
  let push_gate = |gates: &mut Vec<PackedGate>, gate: PackedGate| -> u32 {
    let idx = u32::try_from(gates.len()).expect("gate fits u32");
    gates.push(gate);
    idx
  };

  // Pre-commitment gate 0: w_prod = x * y  =>  1*x*y + (-1)*w_prod = 0.
  let g_prod = u32::try_from(gates.len()).expect("gate fits u32");
  let w_prod = add_wire(WireHint::Solve { gate: g_prod });
  push_gate(
    &mut gates,
    PackedGate {
      a: w_x,
      b: w_y,
      c: w_prod,
      sel: SEL_M | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS1,
      omega_id: C_NEG1,
      qc: 0,
    },
  );

  // Pre-commitment gate 1: w_p_plus_5 = w_prod + 5 - pub0  =>  w_prod - pub0 - w_diff + 5 = 0.
  let g_diff = u32::try_from(gates.len()).expect("gate fits u32");
  let w_diff = add_wire(WireHint::Solve { gate: g_diff });
  push_gate(
    &mut gates,
    PackedGate {
      a: w_prod,
      b: 0,
      c: w_diff,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_NEG1,
      omega_id: C_NEG1,
      qc: 5,
    },
  );

  // Pre-commitment gate 2 (check gate): w_diff - pub1 = 0
  // (enforces pub0 + pub1 = x * y + 5).
  push_gate(
    &mut gates,
    PackedGate {
      a: w_diff,
      b: 1,
      c: 0,
      sel: SEL_L | SEL_R,
      alpha_id: C_POS1,
      beta_id: C_NEG1,
      omega_id: C_POS1,
      qc: 0,
    },
  );

  let pre = gates.len();

  // Post-commitment challenge gamma.
  let w_gamma = add_wire(WireHint::Challenge);

  // 4-bit decomposition of gamma -> beta = b0 + 2*b1 + 4*b2 + 8*b3.
  let mut bits = [0u32; 4];
  for (bit, slot) in bits.iter_mut().enumerate() {
    let wb = add_wire(WireHint::Bit {
      wire: w_gamma,
      bit: u32::try_from(bit).expect("fits u32"),
    });
    *slot = wb;
    // Booleanity check: wb * wb - wb = 0.
    push_gate(
      &mut gates,
      PackedGate {
        a: wb,
        b: wb,
        c: wb,
        sel: SEL_M | SEL_O,
        alpha_id: C_POS1,
        beta_id: C_POS1,
        omega_id: C_NEG1,
        qc: 0,
      },
    );
  }
  let g_b01 = u32::try_from(gates.len()).expect("gate fits u32");
  let w_b01 = add_wire(WireHint::Solve { gate: g_b01 });
  push_gate(
    &mut gates,
    PackedGate {
      a: bits[0],
      b: bits[1],
      c: w_b01,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS2,
      omega_id: C_NEG1,
      qc: 0,
    },
  );
  let g_b012 = u32::try_from(gates.len()).expect("gate fits u32");
  let w_b012 = add_wire(WireHint::Solve { gate: g_b012 });
  push_gate(
    &mut gates,
    PackedGate {
      a: w_b01,
      b: bits[2],
      c: w_b012,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS4,
      omega_id: C_NEG1,
      qc: 0,
    },
  );
  let g_beta = u32::try_from(gates.len()).expect("gate fits u32");
  let w_beta = add_wire(WireHint::Solve { gate: g_beta });
  push_gate(
    &mut gates,
    PackedGate {
      a: w_b012,
      b: bits[3],
      c: w_beta,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS8,
      omega_id: C_NEG1,
      qc: 0,
    },
  );

  // Denominators: d0 = gamma + x + 1, d1 = gamma + y + 1.
  let g_d0 = u32::try_from(gates.len()).expect("gate fits u32");
  let w_d0 = add_wire(WireHint::Solve { gate: g_d0 });
  push_gate(
    &mut gates,
    PackedGate {
      a: w_gamma,
      b: w_x,
      c: w_d0,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS1,
      omega_id: C_NEG1,
      qc: 1,
    },
  );
  let g_d1 = u32::try_from(gates.len()).expect("gate fits u32");
  let w_d1 = add_wire(WireHint::Solve { gate: g_d1 });
  push_gate(
    &mut gates,
    PackedGate {
      a: w_gamma,
      b: w_y,
      c: w_d1,
      sel: SEL_L | SEL_R | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS1,
      omega_id: C_NEG1,
      qc: 1,
    },
  );

  // 4 consecutive quotient gates: q0*d0 = m, q1*d0 = m, q2*d1 = x, q3*d1 = x.
  let mut qs = [0u32; 4];
  for (slot, (den, num)) in
    qs.iter_mut().zip([(w_d0, w_m), (w_d0, w_m), (w_d1, w_x), (w_d1, w_x)])
  {
    let g_idx = u32::try_from(gates.len()).expect("gate fits u32");
    let w_q = add_wire(WireHint::Solve { gate: g_idx });
    *slot = w_q;
    push_gate(
      &mut gates,
      PackedGate {
        a: w_q,
        b: den,
        c: num,
        sel: SEL_M | SEL_O,
        alpha_id: C_POS1,
        beta_id: C_POS1,
        omega_id: C_NEG1,
        qc: 0,
      },
    );
  }

  // 5-step running sum chain:
  // s1 = q0 - q1 (= 0), s2 = s1 + q2, s3 = s2 - q3 (= 0),
  // s4 = s3 + beta, s5 = s4 - beta (= 0).
  let mut prev = qs[0];
  for (other, coeff) in [
    (qs[1], C_NEG1),
    (qs[2], C_POS1),
    (qs[3], C_NEG1),
    (w_beta, C_POS1),
    (w_beta, C_NEG1),
  ] {
    let g_idx = u32::try_from(gates.len()).expect("gate fits u32");
    let next = add_wire(WireHint::Solve { gate: g_idx });
    push_gate(
      &mut gates,
      PackedGate {
        a: prev,
        b: other,
        c: next,
        sel: SEL_L | SEL_R | SEL_O,
        alpha_id: C_POS1,
        beta_id: coeff,
        omega_id: C_NEG1,
        qc: 0,
      },
    );
    prev = next;
  }
  let w_final_sum = prev;

  // Free wire (0) in final check gate: w_free * gamma + w_final_sum = 0.
  let w_free = add_wire(WireHint::Free);
  push_gate(
    &mut gates,
    PackedGate {
      a: w_free,
      b: w_gamma,
      c: w_final_sum,
      sel: SEL_M | SEL_O,
      alpha_id: C_POS1,
      beta_id: C_POS1,
      omega_id: C_POS1,
      qc: 0,
    },
  );

  let commits = vec![0, 1, w_x, w_y, w_m];
  let tables = vec![
    Table {
      name: "root".into(),
      cell_base: 0,
      rows: 1,
      width: u32::try_from(publics + num_outputs).expect("fits u32"),
    },
    Table {
      name: "witness".into(),
      cell_base: u64::try_from(publics + num_outputs).expect("fits u64"),
      rows: 1,
      width: 3,
    },
  ];

  let builder = ScsBuilder::<C> {
    publics,
    wires: hints.len(),
    pre,
    gamma: w_gamma,
    beta: w_beta,
    outputs,
    coeffs,
    gates,
    commits,
    hints,
    tables,
  };
  let scs_bytes = builder.encode();

  // Valid witness: x = 17, y = 23 => x * y + 5 = 396 = 100 + 296.
  let x = C::Fr::from(17u64);
  let y = C::Fr::from(23u64);
  let m = C::Fr::from(9u64);
  let pub0 = C::Fr::from(100u64);
  let pub1 = C::Fr::from(296u64);
  let mut input_wires = Vec::with_capacity(cells);
  input_wires.push(pub0);
  input_wires.push(pub1);
  for k in 0..num_outputs {
    input_wires.push(C::Fr::from(u64::try_from(1000 + k).expect("fits u64")));
  }
  input_wires.push(x);
  input_wires.push(y);
  input_wires.push(m);
  let public_inputs = vec![pub0, pub1];

  (scs_bytes, input_wires, public_inputs)
}

fn check_scs_parser_validation<C: KzgCurve>(num_outputs: usize) {
  let (bytes, _, _) = build_rich_scs::<C>(num_outputs);
  let scs = ScsFile::<C>::parse(&bytes).expect("valid SCS parses");
  assert_eq!(scs.publics, 2);
  assert_eq!(scs.outputs.len(), num_outputs);
  assert_eq!(scs.commits.len(), 5);
  assert_eq!(scs.to_inputs().cells, scs.cells);

  // Bad magic.
  let mut bad = bytes.clone();
  bad[0] ^= 0xff;
  assert!(ScsFile::<C>::parse(&bad).is_err());

  // Truncated.
  assert!(ScsFile::<C>::parse(&bytes[..bytes.len() - 1]).is_err());
  assert!(ScsFile::<C>::parse(&bytes[..40]).is_err());

  // Trailing byte.
  let mut extra = bytes.clone();
  extra.push(0);
  assert!(ScsFile::<C>::parse(&extra).is_err());

  // Zero coefficient rejected (first coeff sits at offset 88 + 4*outputs).
  let coeff_off = 88 + 4 * num_outputs;
  let mut zero_coeff = bytes.clone();
  zero_coeff[coeff_off..coeff_off + 32].fill(0);
  assert!(ScsFile::<C>::parse(&zero_coeff).is_err());

  // Non-canonical coefficient (>= r) rejected.
  let mut big_coeff = bytes.clone();
  big_coeff[coeff_off..coeff_off + 32].fill(0xff);
  assert!(ScsFile::<C>::parse(&big_coeff).is_err());

  // Invalid gate selector (> 15) rejected.
  let gate_off = coeff_off + scs.coeffs.len() * 32;
  let mut bad_sel = bytes.clone();
  bad_sel[gate_off + 12] = 16;
  assert!(ScsFile::<C>::parse(&bad_sel).is_err());

  // SHA-256 pinning test.
  let tmp = std::env::temp_dir()
    .join(format!("ix-native-scs-pin-{}-{num_outputs}.ixscs", C::NAME));
  fs::write(&tmp, &bytes).unwrap();
  let pinned = ScsFile::<C>::read_pinned(&tmp, &scs.sha256_hex()).unwrap();
  assert_eq!(pinned.sha256, scs.sha256);
  let wrong_hex = "0".repeat(64);
  assert!(ScsFile::<C>::read_pinned(&tmp, &wrong_hex).is_err());
  let _ = fs::remove_file(&tmp);
}

#[test]
fn scs_parser_validates_bn254_and_bls12_381() {
  check_scs_parser_validation::<Bn254>(0);
  check_scs_parser_validation::<Bn254>(18);
  check_scs_parser_validation::<Bls12381>(0);
  check_scs_parser_validation::<Bls12381>(22);
}

fn check_hash_fr_matches_solidity_formula<C: KzgCurve>(point: G1AffineOf<C>) {
  let msg = g1_raw_bytes::<C>(point);
  // Independent re-implementation of `hash_fr` in PlonkVerifier.sol /
  // Bls12381PlonkVerifier.sol:
  //   b0 = sha256(0^64 || msg || 0x00 || 48 || 0x00 || "BSB22-Plonk" || 11)
  //   b1 = sha256(b0 || 1 || "BSB22-Plonk" || 11)
  //   b2 = sha256((b0 ^ b1) || 2 || "BSB22-Plonk" || 11)
  //   res = (2^128 * uint256(b1) + uint128(b2[..16])) mod r
  let mut h0 = Sha256::new();
  h0.update([0u8; 64]);
  h0.update(&msg);
  h0.update([0u8, 48u8, 0u8]);
  h0.update(BSB22_DST);
  h0.update([11u8]);
  let b0: [u8; 32] = h0.finalize().into();

  let mut h1 = Sha256::new();
  h1.update(b0);
  h1.update([1u8]);
  h1.update(BSB22_DST);
  h1.update([11u8]);
  let b1: [u8; 32] = h1.finalize().into();

  let mut xored = [0u8; 32];
  for i in 0..32 {
    xored[i] = b0[i] ^ b1[i];
  }
  let mut h2 = Sha256::new();
  h2.update(xored);
  h2.update([2u8]);
  h2.update(BSB22_DST);
  h2.update([11u8]);
  let b2: [u8; 32] = h2.finalize().into();

  let r_mod = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le());
  let b1_int = BigUint::from_bytes_be(&b1);
  let b2_hi = BigUint::from_bytes_be(&b2[..16]);
  let expected_int = ((b1_int << 128) + b2_hi) % r_mod;
  let actual = hash_fr_bsb22::<C>(point);
  let actual_int = BigUint::from_bytes_be(&fr_be_bytes::<C>(actual));
  assert_eq!(actual_int, expected_int);
}

#[test]
fn transcript_hash_fr_and_raw_codecs_match_solidity() {
  // BN254 generator, scaled point, and infinity.
  let bn_gen = ark_bn254::G1Affine::generator();
  let bn_pt = (ark_bn254::G1Projective::from(bn_gen)
    * ark_bn254::Fr::from(42u64))
  .into_affine();
  for pt in [bn_gen, bn_pt, ark_bn254::G1Affine::identity()] {
    check_hash_fr_matches_solidity_formula::<Bn254>(pt);
    let raw = g1_raw_bytes::<Bn254>(pt);
    assert_eq!(raw.len(), 64);
    assert_eq!(decode_g1_raw::<Bn254>(&raw).unwrap(), pt);
  }
  assert!(
    g1_raw_bytes::<Bn254>(ark_bn254::G1Affine::identity())
      .iter()
      .all(|&b| b == 0)
  );

  // BLS12-381 generator, scaled point, and infinity (0x40 MSB flag!).
  let bls_gen = ark_bls12_381::G1Affine::generator();
  let bls_pt = (ark_bls12_381::G1Projective::from(bls_gen)
    * ark_bls12_381::Fr::from(42u64))
  .into_affine();
  for pt in [bls_gen, bls_pt, ark_bls12_381::G1Affine::identity()] {
    check_hash_fr_matches_solidity_formula::<Bls12381>(pt);
    let raw = g1_raw_bytes::<Bls12381>(pt);
    assert_eq!(raw.len(), 96);
    assert_eq!(decode_g1_raw::<Bls12381>(&raw).unwrap(), pt);
  }
  let bls_inf = g1_raw_bytes::<Bls12381>(ark_bls12_381::G1Affine::identity());
  assert_eq!(bls_inf[0], 0x40);
  assert!(bls_inf[1..].iter().all(|&b| b == 0));

  // BLS12-381 non-subgroup torsion point (0, 2) lies on y^2 = x^3 + 4 but NOT
  // in the prime-order subgroup r — decode_g1_raw MUST reject it!
  let mut torsion_raw = vec![0u8; 96];
  torsion_raw[95] = 2;
  assert!(
    decode_g1_raw::<Bls12381>(&torsion_raw).is_err(),
    "BLS12-381 torsion point (0, 2) must be rejected"
  );

  // Canonical scalar rejection at r and r + 1.
  let bn_r = ark_bn254::Fr::MODULUS.to_bytes_be();
  assert!(
    decode_fr_be_canonical::<Bn254>(bn_r.as_slice().try_into().unwrap())
      .is_err()
  );
  let bls_r = ark_bls12_381::Fr::MODULUS.to_bytes_be();
  assert!(
    decode_fr_be_canonical::<Bls12381>(bls_r.as_slice().try_into().unwrap())
      .is_err()
  );
}

fn check_full_prove_verify_and_controls<C: KzgCurve>(num_outputs: usize) {
  let (scs_bytes, input_wires, public_inputs) =
    build_rich_scs::<C>(num_outputs);
  let scs = ScsFile::<C>::parse(&scs_bytes).unwrap();
  let domain = domain_size_for_scs(&scs).unwrap();
  let srs_len = (domain + 3).next_power_of_two();
  let srs = Srs::<C>::unsafe_dev_setup(srs_len, b"ix-native-plonk-unit-test");
  let accel = PlonkAccelerator::<C>::cpu();

  let (pk, vk) = setup(&scs, &srs, &accel).unwrap();
  let vk_sha = vk.sha256();
  let params = VerifierParams::<C>::from_srs(&srs);
  vk.check_anchors(&params).unwrap();

  // Round-trip VK & PK serialization.
  let vk_bytes = vk.to_bytes().unwrap();
  assert_eq!(VerifyingKey::<C>::from_bytes(&vk_bytes).unwrap(), vk);
  let pk_bytes = pk.to_bytes().unwrap();
  let pk_round = ProvingKey::<C>::from_bytes(&pk_bytes).unwrap();
  assert_eq!(pk_round.vk, vk);

  // Prove with two different seeds (verifies randomized ZK blinding).
  let (proof_a, timings_a) = prove_with_seed(
    &scs,
    &pk,
    &input_wires,
    &public_inputs,
    &accel,
    [0x11u8; 32],
  )
  .unwrap();
  let (proof_b, _) = prove_with_seed(
    &scs,
    &pk,
    &input_wires,
    &public_inputs,
    &accel,
    [0x22u8; 32],
  )
  .unwrap();
  assert_ne!(proof_a.lro, proof_b.lro, "blinding should randomize commitments");
  assert_ne!(proof_a.bsb22_commitments, proof_b.bsb22_commitments);
  assert!(timings_a.total_ms >= 0.0);

  // Also test binary witness path + OS RNG path.
  let wrapped_inputs: Vec<CurveScalar<C>> =
    input_wires.iter().copied().map(CurveScalar::new).collect();
  let bin_witness =
    serialize_binary_witness::<C>(scs.publics, &wrapped_inputs).unwrap();
  let (proof_os, _) =
    prove_binary_witness(&scs, &pk, &bin_witness, &public_inputs, &accel)
      .unwrap();

  // Verify native proof, serialized native bytes, and MarshalSolidity bytes.
  verify(&vk, &vk_sha, &proof_a, &public_inputs).unwrap();
  verify(&vk, &vk_sha, &proof_b, &public_inputs).unwrap();
  verify(&vk, &vk_sha, &proof_os, &public_inputs).unwrap();

  let native_bytes = proof_a.to_native_bytes().unwrap();
  verify_native_bytes(&vk, &vk_sha, &native_bytes, &public_inputs).unwrap();

  let sol_bytes = proof_a.marshal_solidity();
  let expected_sol_len =
    9 * g1_raw_len::<C>() + 6 * 32 + (g1_raw_len::<C>() + 32);
  assert_eq!(sol_bytes.len(), expected_sol_len);
  verify_solidity_bytes(&vk, &vk_sha, &sol_bytes, &public_inputs).unwrap();

  // Pure-Rust Solidity verifier export checks.
  let sol_contract = export_solidity(&vk).unwrap();
  assert_eq!(sol_contract, export_solidity(&vk).unwrap());
  assert!(sol_contract.contains("contract PlonkVerifier"));
  assert!(
    sol_contract.contains(&format!("VK_DOMAIN_SIZE = {};", vk.domain_size))
  );
  assert!(sol_contract.contains(&format!(
    "VK_INDEX_COMMIT_API_0 = {};",
    vk.commitment_constraint_indexes[0]
  )));
  assert!(sol_contract.contains("VK_NB_CUSTOM_GATES = 1;"));
  let expected_shift = match C::CURVE {
    crate::kzg::curve::Curve::Bn254 => "VK_COSET_SHIFT = 5;",
    crate::kzg::curve::Curve::Bls12381 => "VK_COSET_SHIFT = 7;",
  };
  assert!(sol_contract.contains(expected_shift));

  // Disk persistence round-trip (`prepare_to_dir` + `NativeProver::open`).
  let dir = std::env::temp_dir()
    .join(format!("ix-native-plonk-prep-{}-{num_outputs}", C::NAME));
  let _ = fs::remove_dir_all(&dir);
  fs::create_dir_all(&dir).unwrap();
  let scs_path = dir.join("circuit.ixscs");
  fs::write(&scs_path, &scs_bytes).unwrap();
  let prep_dir = dir.join("prepared");
  let manifest =
    prepare_to_dir(&scs_path, &srs, "dev-srs-blake3", &prep_dir, &accel)
      .unwrap();
  assert_eq!(manifest.format, NATIVE_MANIFEST_FORMAT);
  assert_eq!(manifest.outputs, num_outputs);
  let prover =
    NativeProver::<C>::open(&prep_dir, &scs_path, &manifest, accel).unwrap();
  let bundle = prover.prove(&input_wires, &public_inputs).unwrap();
  verify_native_bytes(&vk, &vk_sha, &bundle.native, &public_inputs).unwrap();
  verify_solidity_bytes(&vk, &vk_sha, &bundle.solidity, &public_inputs)
    .unwrap();
  // Tampered prepared VK fails SHA-256 pin in `NativeProver::open`.
  let mut tampered_manifest = manifest.clone();
  tampered_manifest.vk_sha256 = "f".repeat(64);
  assert!(
    NativeProver::<C>::open(&prep_dir, &scs_path, &tampered_manifest, accel)
      .is_err()
  );
  let _ = fs::remove_dir_all(&dir);

  // =========================================================================
  // 8/8+ NEGATIVE CONTROLS (all MUST be strictly rejected!)
  // =========================================================================
  let shift_g1 = |p: G1AffineOf<C>| -> G1AffineOf<C> {
    (G1ProjectiveOf::<C>::from(p) + G1ProjectiveOf::<C>::generator())
      .into_affine()
  };

  // Control 1: Wrong public input (both verifier AND prover reject).
  let mut bad_pub = public_inputs.clone();
  bad_pub[0] += C::FR_ONE;
  assert!(verify(&vk, &vk_sha, &proof_a, &bad_pub).is_err());
  assert!(verify_solidity_bytes(&vk, &vk_sha, &sol_bytes, &bad_pub).is_err());
  assert!(prove(&scs, &pk, &input_wires, &bad_pub, &accel).is_err());
  let mut bad_witness_pub = input_wires.clone();
  bad_witness_pub[0] += C::FR_ONE;
  assert!(prove(&scs, &pk, &bad_witness_pub, &bad_pub, &accel).is_err());

  // Control 2: Tampered wire commitment (L / R / O).
  for idx in 0..3 {
    let mut bad = proof_a.clone();
    bad.lro[idx] = shift_g1(bad.lro[idx]);
    assert!(verify(&vk, &vk_sha, &bad, &public_inputs).is_err());
    assert!(
      verify_solidity_bytes(
        &vk,
        &vk_sha,
        &bad.marshal_solidity(),
        &public_inputs
      )
      .is_err()
    );
  }

  // Control 3: Tampered grand-product commitment Z.
  let mut bad_z = proof_a.clone();
  bad_z.z = shift_g1(bad_z.z);
  assert!(verify(&vk, &vk_sha, &bad_z, &public_inputs).is_err());
  assert!(
    verify_solidity_bytes(
      &vk,
      &vk_sha,
      &bad_z.marshal_solidity(),
      &public_inputs
    )
    .is_err()
  );

  // Control 4: Tampered quotient commitment H0 / H1 / H2.
  for idx in 0..3 {
    let mut bad_h = proof_a.clone();
    bad_h.h[idx] = shift_g1(bad_h.h[idx]);
    assert!(verify(&vk, &vk_sha, &bad_h, &public_inputs).is_err());
    assert!(
      verify_solidity_bytes(
        &vk,
        &vk_sha,
        &bad_h.marshal_solidity(),
        &public_inputs
      )
      .is_err()
    );
  }

  // Control 5: Tampered BSB22 commitment (also invalidates gamma = hash_fr(C_bsb22)!).
  let mut bad_bsb = proof_a.clone();
  bad_bsb.bsb22_commitments[0] = shift_g1(bad_bsb.bsb22_commitments[0]);
  assert!(verify(&vk, &vk_sha, &bad_bsb, &public_inputs).is_err());
  assert!(
    verify_solidity_bytes(
      &vk,
      &vk_sha,
      &bad_bsb.marshal_solidity(),
      &public_inputs
    )
    .is_err()
  );

  // Control 6: Tampered claimed opening (r(ζ), L(ζ), S1(ζ), Qcp(ζ), Z(ωζ)).
  for idx in [0usize, 1, 4, 6] {
    let mut bad_eval = proof_a.clone();
    bad_eval.claimed_values[idx] += C::FR_ONE;
    assert!(verify(&vk, &vk_sha, &bad_eval, &public_inputs).is_err());
    if idx > 0 {
      assert!(
        verify_solidity_bytes(
          &vk,
          &vk_sha,
          &bad_eval.marshal_solidity(),
          &public_inputs
        )
        .is_err()
      );
    }
  }
  let mut bad_zwz = proof_a.clone();
  bad_zwz.z_shifted_eval += C::FR_ONE;
  assert!(verify(&vk, &vk_sha, &bad_zwz, &public_inputs).is_err());
  assert!(
    verify_solidity_bytes(
      &vk,
      &vk_sha,
      &bad_zwz.marshal_solidity(),
      &public_inputs
    )
    .is_err()
  );

  // Control 7: Wrong gamma challenge / tampered KZG opening witness.
  let mut bad_w = proof_a.clone();
  bad_w.w_zeta = shift_g1(bad_w.w_zeta);
  assert!(verify(&vk, &vk_sha, &bad_w, &public_inputs).is_err());
  let mut bad_wo = proof_a.clone();
  bad_wo.w_zeta_omega = shift_g1(bad_wo.w_zeta_omega);
  assert!(verify(&vk, &vk_sha, &bad_wo, &public_inputs).is_err());
  // Also directly test that forging a wrong gamma into the post-commitment
  // wire while keeping C_bsb22 fixed breaks the commitment-injection constraint.
  let pre_state = solve_pre_commitment(&scs, &input_wires).unwrap();
  let wrong_gamma =
    hash_fr_bsb22::<C>(proof_a.bsb22_commitments[0]) + C::FR_ONE;
  let solved_wrong_gamma =
    solve_post_commitment(&scs, pre_state, wrong_gamma).unwrap();
  assert_ne!(
    solved_wrong_gamma[scs.gamma as usize],
    hash_fr_bsb22::<C>(proof_a.bsb22_commitments[0])
  );
  // Replacing C_bsb22 with a different commitment changes hash_fr(C_bsb22),
  // which fails the PI_commit algebraic identity in verification.
  let mut wrong_gamma_proof = proof_a.clone();
  wrong_gamma_proof.bsb22_commitments[0] = proof_b.bsb22_commitments[0];
  assert!(verify(&vk, &vk_sha, &wrong_gamma_proof, &public_inputs).is_err());

  // Control 8: Wrong trusted VK SHA-256 digest.
  let mut bad_vk_sha = vk_sha;
  bad_vk_sha[0] ^= 0x01;
  assert!(verify(&vk, &bad_vk_sha, &proof_a, &public_inputs).is_err());
  assert!(
    verify_native_bytes(&vk, &bad_vk_sha, &native_bytes, &public_inputs)
      .is_err()
  );
  assert!(
    verify_solidity_bytes(&vk, &bad_vk_sha, &sol_bytes, &public_inputs)
      .is_err()
  );

  // Control 9: Bad proof length (truncated & extended, native & Solidity).
  assert!(
    verify_native_bytes(
      &vk,
      &vk_sha,
      &native_bytes[..native_bytes.len() - 1],
      &public_inputs
    )
    .is_err()
  );
  let mut ext_native = native_bytes.clone();
  ext_native.push(0);
  assert!(
    verify_native_bytes(&vk, &vk_sha, &ext_native, &public_inputs).is_err()
  );
  assert!(
    verify_solidity_bytes(
      &vk,
      &vk_sha,
      &sol_bytes[..sol_bytes.len() - 1],
      &public_inputs
    )
    .is_err()
  );
  let mut ext_sol = sol_bytes.clone();
  ext_sol.push(0);
  assert!(
    verify_solidity_bytes(&vk, &vk_sha, &ext_sol, &public_inputs).is_err()
  );
}

#[test]
fn bn254_full_prove_verify_solidity_and_negative_controls_outputs_0() {
  check_full_prove_verify_and_controls::<Bn254>(0);
}

#[test]
fn bn254_full_prove_verify_solidity_and_negative_controls_outputs_18() {
  check_full_prove_verify_and_controls::<Bn254>(18);
}

#[test]
fn bls12_381_full_prove_verify_solidity_and_negative_controls_outputs_0() {
  check_full_prove_verify_and_controls::<Bls12381>(0);
}

#[test]
fn bls12_381_full_prove_verify_solidity_and_negative_controls_outputs_22() {
  check_full_prove_verify_and_controls::<Bls12381>(22);
}

#[test]
fn bls12_381_verifier_rejects_non_subgroup_torsion_point_in_proof() {
  let (scs_bytes, input_wires, public_inputs) = build_rich_scs::<Bls12381>(0);
  let scs = ScsFile::<Bls12381>::parse(&scs_bytes).unwrap();
  let domain = domain_size_for_scs(&scs).unwrap();
  let srs = Srs::<Bls12381>::unsafe_dev_setup(
    (domain + 3).next_power_of_two(),
    b"ix-native-plonk-torsion-test",
  );
  let accel = PlonkAccelerator::<Bls12381>::cpu();
  let (pk, vk) = setup(&scs, &srs, &accel).unwrap();
  let vk_sha = vk.sha256();
  let (mut proof, _) = prove_with_seed(
    &scs,
    &pk,
    &input_wires,
    &public_inputs,
    &accel,
    [0x33u8; 32],
  )
  .unwrap();

  // Point (0, 2) on BLS12-381 E(Fq): y^2 = 4 = x^3 + 4, NOT in prime-order G1!
  let torsion = ark_bls12_381::G1Affine::new_unchecked(
    ark_bls12_381::Fq::from(0u64),
    ark_bls12_381::Fq::from(2u64),
  );
  assert!(torsion.is_on_curve());
  assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());

  // Direct API rejects torsion point.
  proof.lro[0] = torsion;
  assert!(verify(&vk, &vk_sha, &proof, &public_inputs).is_err());

  // Solidity wire format rejects torsion point.
  let bad_sol = proof.marshal_solidity();
  assert!(
    verify_solidity_bytes(&vk, &vk_sha, &bad_sol, &public_inputs).is_err()
  );
}

#[test]
fn solver_detects_unsatisfied_pre_and_post_gates() {
  let (scs_bytes, mut bad_inputs, _) = build_rich_scs::<Bn254>(0);
  let scs = ScsFile::<Bn254>::parse(&scs_bytes).unwrap();
  // Break pub0 + pub1 == x * y + 5.
  bad_inputs[0] += ark_bn254::Fr::from(1u64);
  assert!(solve_pre_commitment(&scs, &bad_inputs).is_err());

  // Verify `batch_invert_in_place` rejects a zero denominator cleanly.
  let mut vals = vec![
    ark_bn254::Fr::from(3u64),
    ark_bn254::Fr::from(0u64),
    ark_bn254::Fr::from(5u64),
  ];
  assert!(solver::batch_invert_in_place::<Bn254>(&mut vals).is_err());
}

#[test]
fn dev_srs_never_emits_unmarked_plonk_solidity_and_ceremony_emits_clean() {
  use crate::kzg::srs::filecoin::{
    FILECOIN_PREFIX_2P8_FIXTURE, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
    load_filecoin_cache,
  };
  use crate::pipeline::SetupClass;

  // Development BN254 SRS: marked header, renamed contract, `.DEV_INSECURE.sol`.
  let (bn_scs_bytes, _, _) = build_rich_scs::<Bn254>(0);
  let bn_scs = ScsFile::<Bn254>::parse(&bn_scs_bytes).unwrap();
  let bn_domain = domain_size_for_scs(&bn_scs).unwrap();
  let dev_srs = Srs::<Bn254>::unsafe_dev_setup(
    (bn_domain + 3).next_power_of_two(),
    b"dev-sol-guard-bn254",
  );
  let (_, dev_vk) =
    setup(&bn_scs, &dev_srs, &PlonkAccelerator::<Bn254>::cpu()).unwrap();
  assert_eq!(dev_vk.setup_class(), SetupClass::Development);
  let dev_sol = export_solidity(&dev_vk).unwrap();
  assert!(dev_sol.starts_with(solidity::DEV_SOLIDITY_HEADER));
  assert!(
    dev_sol.contains("contract PlonkVerifier_DEV_INSECURE_DO_NOT_DEPLOY {")
  );
  assert!(!dev_sol.contains("contract PlonkVerifier {"));
  assert_eq!(
    solidity::solidity_filename_for_vk(&dev_vk),
    "PlonkVerifier.DEV_INSECURE.sol"
  );

  // Ceremony BLS12-381 SRS (Filecoin): unmarked `PlonkVerifier` & filename.
  let (bls_scs_bytes, _, _) = build_rich_scs::<Bls12381>(0);
  let bls_scs = ScsFile::<Bls12381>::parse(&bls_scs_bytes).unwrap();
  let bls_domain = domain_size_for_scs(&bls_scs).unwrap();
  let fixture_dir =
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FILECOIN_PREFIX_2P8_FIXTURE);
  let fc_srs = load_filecoin_cache(
    &fixture_dir,
    FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
    (bls_domain + 3).next_power_of_two(),
  )
  .unwrap();
  let (_, fc_vk) =
    setup(&bls_scs, &fc_srs, &PlonkAccelerator::<Bls12381>::cpu()).unwrap();
  assert_eq!(fc_vk.setup_class(), SetupClass::Filecoin);
  let fc_sol = export_solidity(&fc_vk).unwrap();
  assert!(!fc_sol.contains("DEV_INSECURE"));
  assert!(fc_sol.contains("contract PlonkVerifier {"));
  assert_eq!(
    solidity::solidity_filename_for_vk(&fc_vk),
    "Bls12381PlonkVerifier.sol"
  );
}
