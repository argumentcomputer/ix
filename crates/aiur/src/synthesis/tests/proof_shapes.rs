// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Complete native shape checks with independent activation, domain and
//! matrix dimension mutations. The PCS data is removed because shape
//! acceptance alone makes no polynomial authentication assertion.

use super::*;
use multi_stark::types::ExtVal;

fn bytes(out: &mut Vec<u8>, value: &[u8]) {
  out.extend(u64::try_from(value.len()).unwrap().to_le_bytes());
  out.extend(value);
}

fn modified(
  proof: &AiurProof,
  change: impl FnOnce(&mut AiurProof),
) -> AiurProof {
  let mut result = proof.clone();
  change(&mut result);
  result
}

fn remove_active(system: &AiurSystem, proof: &mut AiurProof, ci: usize) {
  let position = proof.active[..ci].iter().filter(|&&active| active).count();
  assert!(proof.active[ci]);
  proof.active[ci] = false;
  proof.log_degrees.remove(position);
  let _ = proof.intermediate_accumulators.remove(position);
  proof.stage_1_opened_values.remove(position);
  proof.stage_2_opened_values.remove(position);
  proof.quotient_opened_values.remove(position);
  if let Some(slot) = system.system.preprocessed_indices[ci] {
    proof.preprocessed_opened_values.as_mut().unwrap()[slot].clear();
  }
}

fn variants(system: &AiurSystem, proof: &AiurProof) -> Vec<AiurProof> {
  let mut cases = vec![proof.clone()];
  cases.extend([
    modified(proof, |p| p.active.clear()),
    modified(proof, |p| p.active.push(false)),
    modified(proof, |p| {
      p.active.pop();
    }),
    modified(proof, |p| p.active.fill(false)),
    modified(proof, |p| p.log_degrees.clear()),
    modified(proof, |p| p.log_degrees.push(0)),
    modified(proof, |p| {
      p.log_degrees.pop();
    }),
    modified(proof, |p| p.intermediate_accumulators.clear()),
    modified(proof, |p| p.intermediate_accumulators.push(ExtVal::ZERO)),
    modified(proof, |p| {
      p.intermediate_accumulators.pop();
    }),
    modified(proof, |p| p.intermediate_accumulators.fill(ExtVal::ONE)),
    modified(proof, |p| p.preprocessed_opened_values = None),
    modified(proof, |p| p.preprocessed_opened_values = Some(vec![])),
    modified(proof, |p| {
      p.preprocessed_opened_values.as_mut().unwrap().push(vec![])
    }),
    modified(proof, |p| {
      p.preprocessed_opened_values.as_mut().unwrap().pop();
    }),
  ]);
  for ci in 0..proof.active.len() {
    cases.push(modified(proof, |p| p.active[ci] = !p.active[ci]));
    if proof.active[ci] {
      let inactive = modified(proof, |p| remove_active(system, p, ci));
      system.system.verify_shape(&inactive).unwrap();
      cases.push(inactive);
    }
  }
  for position in 0..proof.log_degrees.len() {
    for degree in 0..=255 {
      cases.push(modified(proof, |p| p.log_degrees[position] = degree));
    }
  }
  // Independently remove/append outer matrices, opening points and columns
  // in each of the four rounds, including every quotient slice coordinate.
  for round in 0..4 {
    let select: fn(&mut AiurProof) -> &mut Vec<Vec<Vec<ExtVal>>> = match round {
      0 => |p| &mut p.stage_1_opened_values,
      1 => |p| &mut p.stage_2_opened_values,
      2 => |p| &mut p.quotient_opened_values,
      _ => |p| p.preprocessed_opened_values.as_mut().unwrap(),
    };
    cases.push(modified(proof, |p| select(p).clear()));
    cases.push(modified(proof, |p| select(p).push(vec![])));
    cases.push(modified(proof, |p| {
      select(p).pop();
    }));
    let values = match round {
      0 => &proof.stage_1_opened_values,
      1 => &proof.stage_2_opened_values,
      2 => &proof.quotient_opened_values,
      _ => proof.preprocessed_opened_values.as_ref().unwrap(),
    };
    for (matrix, points) in values.iter().enumerate() {
      cases.push(modified(proof, |p| select(p)[matrix].clear()));
      cases.push(modified(proof, |p| select(p)[matrix].push(vec![])));
      cases.push(modified(proof, |p| {
        select(p)[matrix].pop();
      }));
      for point in 0..points.len() {
        cases.push(modified(proof, |p| select(p)[matrix][point].clear()));
        cases.push(modified(proof, |p| {
          select(p)[matrix][point].push(ExtVal::ZERO)
        }));
        cases.push(modified(proof, |p| {
          select(p)[matrix][point].pop();
        }));
      }
    }
  }
  cases
}

#[test]
fn proof_shape_snapshot() -> std::io::Result<()> {
  let mut out = b"Aiur proof shapes v2\n".to_vec();
  out.extend(4_u64.to_le_bytes());
  let mut total = 0;
  let mut accepted = 0;
  for seed in 0..4 {
    let (mut cp, mut fp) = test_parameters();
    cp.log_blowup = 1 + seed % 2;
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
    let (claim, mut proof) = system.prove(0, &input, &mut empty_io_buffer());
    system.verify(&claim, &proof).unwrap();
    proof.opening_proof.commit_phase_commits.clear();
    proof.opening_proof.commit_pow_witnesses.clear();
    proof.opening_proof.input_openings.clear();
    proof.opening_proof.commit_phase_openings.clear();
    proof.opening_proof.final_poly.clear();
    proof.opening_proof.query_pow_witness = G::ZERO;
    bytes(&mut out, &crate::vk_codec::to_bytes(&system.system, cp, fp));
    let cases = variants(&system, &proof);
    let accepted_before = accepted;
    total += cases.len();
    out.extend(u64::try_from(cases.len()).unwrap().to_le_bytes());
    for case in cases {
      bytes(&mut out, &case.to_bytes().unwrap());
      let result = system.system.verify_shape(&case);
      out.push(u8::from(result.is_ok()));
      if let Ok(degrees) = result {
        accepted += 1;
        out.extend(u64::try_from(degrees.len()).unwrap().to_le_bytes());
        for degree in degrees {
          out.extend(u64::try_from(degree).unwrap().to_le_bytes());
        }
      }
      out.push(u8::from(fixed_trace_heights(
        system.system.circuits.iter().map(|c| c.preprocessed_height),
        &case.active,
        &case.log_degrees,
      )));
      let budget = lookup_query_bound(
        system.slot_widths.iter().map(Vec::len),
        &case.active,
        &case.log_degrees,
      );
      out.push(u8::from(budget.is_some()));
      if let Some(bound) = budget {
        out.extend(bound.to_le_bytes());
      }
      out.push(u8::from(trace_cap_coverage(
        cp.log_blowup,
        cp.cap_height,
        &case.log_degrees,
      )));
    }
    // Retuning the Bytes1 circuit reduces its quotient degree from two to
    // one. Its domain mutations therefore admit one additional exponent
    // in each system, independently of the fixed-height acceptance guard.
    let bytes1 = &system.system.circuits[system.system.circuits.len() - 2];
    assert_eq!(bytes1.preprocessed_height, 256);
    assert_eq!(bytes1.quotient_degree(), 1);
    assert_eq!(
      accepted - accepted_before,
      if seed % 2 == 0 { 99 } else { 158 }
    );
  }
  if let Some(path) = std::env::var_os("IX_PROOF_SHAPE_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  assert_eq!((total, accepted), (4696, 514));
  eprintln!("proof shapes: {total} native cases, {accepted} accepted shapes");
  Ok(())
}
