// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

fn bound(slots: &[usize], active: &[bool], degrees: &[u8]) -> Option<u64> {
  lookup_query_bound(slots.iter().copied(), active, degrees)
}

/// The corpus exercises every u8 exponent, machine/field boundaries,
/// active-position indexing and independently malformed sequence lengths.
#[cfg(target_pointer_width = "64")]
#[test]
fn lookup_budget_snapshot() -> std::io::Result<()> {
  use multi_stark::p3_field::PrimeField64;
  fn append(out: &mut Vec<u8>, value: Option<u64>) {
    out.push(u8::from(value.is_some()));
    out.extend(value.unwrap_or(0).to_le_bytes());
  }
  let header = b"Aiur lookup budget v1\n";
  let mut out = header.to_vec();
  let p = usize::try_from(G::ORDER_U64).unwrap();
  let cases = [
    0,
    1,
    2,
    3,
    4,
    255,
    65536,
    1 << 31,
    1 << 32,
    (1 << 32) - 1,
    p / 2 - 1,
    p - 3,
    p - 2,
    p - 1,
    p,
    usize::MAX,
  ];
  for slots in cases {
    for degree in 0..=255 {
      append(&mut out, bound(&[slots], &[true], &[degree]));
      append(
        &mut out,
        bound(
          &[usize::MAX, slots, usize::MAX],
          &[false, true, false],
          &[degree],
        ),
      );
      append(&mut out, bound(&[slots, 3], &[true, true], &[degree, 31]));
      append(&mut out, bound(&[3, slots], &[true, true], &[31, degree]));
    }
  }
  let slots = [2, 7, 0, 13];
  for slot_count in 0..=4 {
    for active_count in 0..=4 {
      for mask in 0..(1 << active_count) {
        let active = (0..active_count)
          .map(|bit| mask & (1 << bit) != 0)
          .collect::<Vec<_>>();
        for degree_count in 0..=5 {
          for degree in [0, 1, 31, 63, 64, 255] {
            append(
              &mut out,
              bound(&slots[..slot_count], &active, &vec![degree; degree_count]),
            );
          }
        }
      }
    }
  }
  assert_eq!(out.len(), header.len() + 21_964 * 9);
  if let Some(path) = std::env::var_os("IX_LOOKUP_BUDGET_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}

#[test]
fn query_budget_uses_canonical_slots_and_active_heights() {
  assert_eq!(
    bound(&[2, 999, 3, 999], &[true, false, true, false], &[4, 5]),
    Some(129)
  );
  assert_eq!(
    bound(&[999, 3, 999, 2], &[false, true, false, true], &[5, 4]),
    Some(129)
  );
  assert_eq!(bound(&[0], &[true], &[0]), Some(1));
  assert_eq!(bound(&[1], &[true], &[63]), Some((1_u64 << 63) + 1));
}

#[test]
fn query_budget_rejects_malformed_alignment_and_shifts() {
  for (slots, active, degrees) in [
    (vec![], vec![], vec![]),
    (vec![1], vec![false], vec![]),
    (vec![1], vec![], vec![]),
    (vec![], vec![true], vec![0]),
    (vec![1, 2], vec![true], vec![0]),
    (vec![1], vec![true, false], vec![0]),
    (vec![1], vec![true], vec![]),
    (vec![1], vec![true], vec![0, 0]),
    (vec![1, 2], vec![false, true], vec![0, 0]),
  ] {
    assert_eq!(bound(&slots, &active, &degrees), None);
  }
  for degree in 64..=255 {
    for slots in [0, 1, usize::MAX] {
      assert_eq!(bound(&[slots], &[true], &[degree]), None);
    }
  }
}

#[cfg(target_pointer_width = "64")]
#[test]
fn query_budget_checks_the_global_sum_and_both_overflows() {
  use multi_stark::p3_field::PrimeField64;
  let p = usize::try_from(G::ORDER_U64).unwrap();
  assert_eq!(bound(&[p - 2], &[true], &[0]), Some(G::ORDER_U64 - 1));
  assert_eq!(bound(&[p - 1], &[true], &[0]), None);
  assert_eq!(
    bound(&[p - 3, 1], &[true, true], &[0, 0]),
    Some(G::ORDER_U64 - 1)
  );
  assert_eq!(bound(&[p - 3, 2], &[true, true], &[0, 0]), None);
  assert_eq!(bound(&[usize::MAX], &[true], &[1]), None);
  assert_eq!(bound(&[usize::MAX], &[true], &[0]), None);
  assert_eq!(bound(&[1, usize::MAX], &[true, false], &[0]), Some(2));
  let slots = (p - 2) >> 31;
  assert!(bound(&[slots], &[true], &[31]).is_some());
  assert_eq!(bound(&[slots + 1], &[true], &[31]), None);
}

#[test]
fn public_verify_checks_lookup_metadata() {
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(mul_toplevel(), cp, fp);
  let (claim, mut proof) =
    system.prove(0, &[G::ONE, G::ONE], &mut empty_io_buffer());
  system.verify(&claim, &proof).unwrap();
  assert!(
    lookup_query_bound(
      system.slot_widths.iter().map(Vec::len),
      &proof.active,
      &proof.log_degrees
    )
    .is_some()
  );
  let degrees = proof.log_degrees.clone();
  for malformed in
    [vec![], vec![0; degrees.len() + 1], vec![255; degrees.len()]]
  {
    proof.log_degrees = malformed;
    assert!(matches!(
      system.verify(&claim, &proof),
      Err(VerificationError::InvalidProofShape)
    ));
  }
  proof.log_degrees = degrees;
  let active = proof.active.clone();
  for malformed in
    [vec![], vec![false; active.len()], vec![true; active.len() + 1]]
  {
    proof.active = malformed;
    assert!(matches!(
      system.verify(&claim, &proof),
      Err(VerificationError::InvalidProofShape)
    ));
  }
  proof.active = active;
  system.verify(&claim, &proof).unwrap();
}

#[test]
fn serialized_key_maximum_lookup_budget_fits_characteristic() {
  use multi_stark::p3_field::PrimeField64;
  let slots = vec![65535; 65535];
  let active = vec![true; 65535];
  let degrees = vec![32; 65535];
  let maximum = 1 + 65535_u64.pow(2) * (1_u64 << 32);
  assert!(maximum < G::ORDER_U64);
  assert_eq!(bound(&slots, &active, &degrees), Some(maximum));
}
