// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Native binary Merkle authentication and the cap coverage boundary.

use super::*;

#[cfg(not(feature = "cuda"))]
#[test]
fn native_cap_can_omit_a_shorter_matrix() {
  use multi_stark::p3_matrix::Matrix;
  use multi_stark::types::Mmcs;
  use p3_blake3::Blake3;
  use p3_commit::Mmcs as _;
  use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};

  for cap_height in 0..=4 {
    let mmcs = Mmcs::new(
      SerializingHasher::new(Blake3),
      CompressionFunctionFromHasher::new(Blake3),
      cap_height,
    );
    let tall = RowMajorMatrix::new((1..=8).map(G::from_u32).collect(), 1);
    let short = RowMajorMatrix::new(vec![G::from_u32(21), G::from_u32(22)], 1);
    let dimensions = vec![tall.dimensions(), short.dimensions()];
    let (commitment, data) = mmcs.commit(vec![tall.clone(), short]);
    let mut changed = mmcs.open_batch(5, &data);
    mmcs.verify_batch(&commitment, &dimensions, 5, (&changed).into()).unwrap();
    changed.opened_values[1][0] += G::ONE;
    let accepted =
      mmcs.verify_batch(&commitment, &dimensions, 5, (&changed).into()).is_ok();
    assert_eq!(accepted, cap_height > 1);

    let indices = [5, 0, 5, 7];
    let (mut rows, proof) = mmcs.open_multi_batch(&indices, &data);
    mmcs
      .verify_multi_batch(&commitment, &dimensions, &indices, &rows, &proof)
      .unwrap();
    for query in &mut rows {
      query[1][0] += G::ONE;
    }
    let accepted = mmcs
      .verify_multi_batch(&commitment, &dimensions, &indices, &rows, &proof)
      .is_ok();
    assert_eq!(accepted, cap_height > 1);

    let different =
      RowMajorMatrix::new(vec![G::from_u32(31), G::from_u32(32)], 1);
    let (other_commitment, _) = mmcs.commit(vec![tall, different]);
    assert_eq!(commitment == other_commitment, cap_height > 1);
  }
}

#[cfg(not(feature = "cuda"))]
#[test]
fn public_verify_rejects_a_cap_above_the_shortest_trace_lde() {
  let (mut cp, fp) = test_parameters();
  cp.cap_height = 2;
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let (claim, proof) =
    system.prove(0, &[G::ONE, G::ONE], &mut empty_io_buffer());
  assert_eq!(proof.log_degrees[0], 0);
  system.system.verify(&claim, &proof).unwrap();
  assert!(matches!(
    system.verify(&claim, &proof),
    Err(VerificationError::InvalidProofShape)
  ));
}

#[test]
fn public_verify_accepts_a_cap_at_the_shortest_trace_lde() {
  let (mut cp, fp) = test_parameters();
  #[cfg(not(feature = "cuda"))]
  {
    cp.cap_height = 1;
  }
  #[cfg(feature = "cuda")]
  {
    cp.cap_height = 0;
  }
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let (claim, proof) =
    system.prove(0, &[G::from_u32(3), G::from_u32(5)], &mut empty_io_buffer());
  assert_eq!(proof.log_degrees[0], 0);
  system.verify(&claim, &proof).unwrap();
  let mut changed = claim.clone();
  *changed.last_mut().unwrap() += G::ONE;
  assert!(system.verify(&changed, &proof).is_err());
}

#[test]
fn cap_coverage_matches_injection_geometry_at_integer_boundaries() {
  let parameters = [
    0,
    1,
    2,
    3,
    8,
    16,
    31,
    32,
    63,
    64,
    255,
    256,
    65535,
    usize::MAX - 255,
    usize::MAX,
  ];
  let mut total = 0;
  for blowup in parameters {
    for cap in parameters {
      assert!(trace_cap_coverage(blowup, cap, &[]));
      total += 1;
      for degree in 0..=255 {
        for degrees in [
          vec![degree],
          vec![degree, 0],
          vec![degree, 8, 16],
          vec![degree, degree],
          vec![255, degree],
        ] {
          // Check the direct tree-height condition with wide arithmetic,
          // independently of the production guard's saturating subtraction.
          let tallest = u128::from(*degrees.iter().max().unwrap());
          let effective_cap = (cap as u128).min(blowup as u128 + tallest);
          let expected = degrees.iter().all(|&height| {
            effective_cap <= blowup as u128 + u128::from(height)
          });
          assert_eq!(
            trace_cap_coverage(blowup, cap, &degrees),
            expected,
            "blowup={blowup}, cap={cap}, degrees={degrees:?}"
          );
          total += 1;
        }
      }
    }
  }
  assert_eq!(total, 288225);
}
