// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Compare the complete native proof object with the total Lean codec.
//! The semantic view deliberately differs from bincode's field order and
//! represents every scalar/digest byte as a u64 to expose framing mistakes.

use super::*;
use multi_stark::{
  p3_field::{BasedVectorSpace, PrimeField64},
  types::ExtVal,
};

fn vector<T>(
  out: &mut Vec<u64>,
  values: &[T],
  item: impl Fn(&mut Vec<u64>, &T),
) {
  out.push(u64::try_from(values.len()).unwrap());
  for value in values {
    item(out, value);
  }
}

fn field(out: &mut Vec<u64>, value: &G) {
  out.push(value.as_canonical_u64());
}

fn extension(out: &mut Vec<u64>, value: &ExtVal) {
  let coordinates: &[G] = value.as_basis_coefficients_slice();
  out.push(coordinates[0].as_canonical_u64());
  out.push(coordinates[1].as_canonical_u64());
}

fn hashes(out: &mut Vec<u64>, values: &[[u8; 32]]) {
  vector(out, values, |out, digest| {
    out.extend(digest.iter().map(|byte| u64::from(*byte)));
  });
}

fn openings<T>(
  out: &mut Vec<u64>,
  values: &[Vec<Vec<T>>],
  item: impl Fn(&mut Vec<u64>, &T),
) {
  vector(out, values, |out, matrix| {
    vector(out, matrix, |out, row| vector(out, row, &item));
  });
}

fn view(proof: &AiurProof) -> Vec<u64> {
  let mut out = Vec::new();
  vector(&mut out, &proof.log_degrees, |out, degree| {
    out.push(u64::from(*degree));
  });
  vector(&mut out, &proof.active, |out, enabled| {
    out.push(u64::from(*enabled));
  });
  openings(&mut out, &proof.stage_2_opened_values, extension);
  openings(&mut out, &proof.stage_1_opened_values, extension);
  out.push(u64::from(proof.preprocessed_opened_values.is_some()));
  if let Some(values) = &proof.preprocessed_opened_values {
    openings(&mut out, values, extension);
  }
  openings(&mut out, &proof.quotient_opened_values, extension);
  vector(&mut out, &proof.intermediate_accumulators, extension);
  hashes(&mut out, proof.commitments.quotient_chunks.roots());
  hashes(&mut out, proof.commitments.stage_2_trace.roots());
  hashes(&mut out, proof.commitments.stage_1_trace.roots());
  let fri = &proof.opening_proof;
  field(&mut out, &fri.query_pow_witness);
  vector(&mut out, &fri.final_poly, extension);
  vector(&mut out, &fri.commit_phase_openings, |out, step| {
    hashes(out, &step.opening_proof.sibling_hashes);
    vector(out, &step.sibling_values, |out, row| vector(out, row, extension));
    out.push(u64::from(step.log_arity));
  });
  vector(&mut out, &fri.input_openings, |out, batch| {
    hashes(out, &batch.opening_proof.sibling_hashes);
    openings(out, &batch.opened_values, field);
  });
  vector(&mut out, &fri.commit_pow_witnesses, field);
  vector(&mut out, &fri.commit_phase_commits, |out, cap| {
    hashes(out, cap.roots());
  });
  out
}

fn bytes(out: &mut Vec<u8>, value: &[u8]) {
  out.extend(u64::try_from(value.len()).unwrap().to_le_bytes());
  out.extend(value);
}

fn write_case(out: &mut Vec<u8>, value: &[u8]) -> bool {
  bytes(out, value);
  let parsed = AiurProof::from_bytes(value);
  out.push(u8::from(parsed.is_ok()));
  if let Ok(proof) = parsed {
    bytes(out, &proof.to_bytes().unwrap());
    let words = view(&proof);
    out.extend(u64::try_from(words.len()).unwrap().to_le_bytes());
    out.extend(words.iter().flat_map(|word| word.to_le_bytes()));
    true
  } else {
    false
  }
}

fn sparse(proof: &AiurProof) -> AiurProof {
  let mut result = proof.clone();
  result.active = vec![true, false, true];
  result.log_degrees = vec![0, 8, 16, 255];
  result.intermediate_accumulators = vec![
    ExtVal::from_basis_coefficients_slice(&[G::ZERO, -G::ONE]).unwrap(),
    ExtVal::from_basis_coefficients_slice(&[G::ONE, G::from_u64(1 << 32)])
      .unwrap(),
  ];
  result.quotient_opened_values = vec![vec![], vec![vec![]]];
  result.preprocessed_opened_values = None;
  result.stage_1_opened_values = vec![];
  result.stage_2_opened_values =
    vec![vec![result.intermediate_accumulators.clone()]];
  let fri = &mut result.opening_proof;
  fri.commit_phase_commits.truncate(1);
  fri.commit_pow_witnesses = vec![G::ZERO, G::ONE, -G::ONE];
  fri.input_openings.truncate(1);
  for batch in &mut fri.input_openings {
    batch.opened_values = vec![vec![], vec![vec![G::ONE, -G::ONE]]];
    batch.opening_proof.sibling_hashes.truncate(3);
  }
  fri.commit_phase_openings.truncate(1);
  for step in &mut fri.commit_phase_openings {
    step.log_arity = 255;
    step.sibling_values =
      vec![vec![], result.intermediate_accumulators.clone()];
    step.opening_proof.sibling_hashes.truncate(2);
  }
  fri.final_poly = result.intermediate_accumulators.clone();
  fri.query_pow_witness = -G::ONE;
  result
}

#[test]
fn proof_codec_snapshot() -> std::io::Result<()> {
  let mut cases = Vec::new();
  let mut keys = Vec::new();
  for seed in 0..4 {
    let (mut cp, mut fp) = test_parameters();
    cp.cap_height = seed % 2 * 2;
    fp.max_log_arity = seed % 2 + 1;
    fp.num_queries = 8;
    let top = match seed {
      0 => mul_toplevel(),
      1 => call_and_memory_toplevel(),
      2 => xor_splits_toplevel(),
      _ => unconstrained_call_promotion_toplevel(),
    };
    let input = if seed == 3 {
      vec![G::from_u8(7)]
    } else {
      vec![G::from_u8(3), G::from_u8(5)]
    };
    let system = AiurSystem::build(top, cp, fp);
    let (claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
    system.system.verify(&claim, &proof).unwrap();
    // Preserve the original wire corpus, including native-accepted caps
    // whose shortest trace is now excluded by the Aiur coverage guard.
    assert_eq!(
      system.verify(&claim, &proof).is_ok(),
      trace_cap_coverage(cp.log_blowup, cp.cap_height, &proof.log_degrees)
    );
    keys.push(crate::vk_codec::to_bytes(&system.system, cp, fp));
    cases.push(proof.to_bytes().unwrap());
    let fixture = sparse(&proof);
    let encoded = fixture.to_bytes().unwrap();
    cases.push(encoded.clone());
    let mut some_empty = fixture.clone();
    some_empty.preprocessed_opened_values = Some(vec![]);
    cases.push(some_empty.to_bytes().unwrap());
    for suffix in [&[0][..], &[1, 2, 3][..]] {
      let mut changed = encoded.clone();
      changed.extend(suffix);
      assert!(AiurProof::from_bytes(&changed).is_ok());
      cases.push(changed);
    }
    // Truncate at every byte of the small, fully populated fixture. Native
    // serde must fail even inside extension coordinates and digest arrays.
    for length in 0..encoded.len() {
      let changed = encoded[..length].to_vec();
      assert!(AiurProof::from_bytes(&changed).is_err());
      cases.push(changed);
    }
    // The first active boolean and the first extension coordinate have
    // independently known offsets from the native object's lengths.
    for tag in [2, 127, 255] {
      let mut changed = encoded.clone();
      changed[8] = tag;
      assert!(AiurProof::from_bytes(&changed).is_err());
      cases.push(changed);
    }
    let first_accumulator = 8
      + fixture.active.len()
      + 3 * 8
      + 32
        * (fixture.commitments.stage_1_trace.num_roots()
          + fixture.commitments.stage_2_trace.num_roots()
          + fixture.commitments.quotient_chunks.num_roots())
      + 8;
    for offset in [first_accumulator, first_accumulator + 8] {
      for noncanonical in [G::ORDER_U64, u64::MAX] {
        let mut changed = encoded.clone();
        changed[offset..offset + 8]
          .copy_from_slice(&noncanonical.to_le_bytes());
        assert!(AiurProof::from_bytes(&changed).is_err());
        cases.push(changed);
      }
    }
  }
  let mut out = b"Aiur proof codec v1\n".to_vec();
  out.extend(u64::try_from(keys.len()).unwrap().to_le_bytes());
  for key in &keys {
    bytes(&mut out, key);
  }
  out.extend(u64::try_from(cases.len()).unwrap().to_le_bytes());
  let mut accepted = 0;
  for case in &cases {
    accepted += usize::from(write_case(&mut out, case));
  }
  assert_eq!(accepted, 20);
  assert_eq!(cases.len(), 3636);
  if let Some(path) = std::env::var_os("IX_PROOF_CODEC_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  eprintln!(
    "proof codec: 4 verified native proofs, {} byte cases, {accepted} decodable",
    cases.len()
  );
  Ok(())
}

#[test]
fn malformed_proof_caps_reject_without_panicking() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let (claim, proof) =
    system.prove(0, &[G::ONE, G::ONE], &mut empty_io_buffer());
  let mut bytes = proof.to_bytes().unwrap();
  let offset = 8 + proof.active.len();
  let roots = proof.commitments.stage_1_trace.num_roots();
  bytes[offset..offset + 8].copy_from_slice(&0_u64.to_le_bytes());
  bytes.drain(offset + 8..offset + 8 + roots * 32);
  let malformed = AiurProof::from_bytes(&bytes).unwrap();
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    system.verify(&claim, &malformed)
  }));
  assert!(result.is_ok(), "deserialized proof cap caused verifier panic");
  assert!(result.unwrap().is_err());
}
