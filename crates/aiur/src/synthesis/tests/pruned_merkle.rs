// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Actual shared MMCS decisions and hash calls, including late failures.

use super::merkle::{
  Calls, Digest, RecordingHash, RecordingMmcs, digests, number,
};
use super::*;
use multi_stark::{
  p3_field::PrimeField64,
  p3_matrix::{Dimensions, Matrix},
  types::Mmcs,
};
use p3_blake3::Blake3;
use p3_commit::Mmcs as _;
use p3_merkle_tree::PrunedMerklePaths;
use p3_symmetric::{
  CompressionFunctionFromHasher, MerkleCap, SerializingHasher,
};

#[derive(Clone)]
struct Case {
  dimensions: Vec<Dimensions>,
  indices: Vec<usize>,
  rows: Vec<Vec<Vec<G>>>,
  proof: Vec<Digest>,
  cap: Vec<Digest>,
  cap_height: usize,
}

#[derive(Default)]
struct Corpus {
  body: Vec<u8>,
  count: usize,
  accepted: usize,
  omitted: usize,
  unhashed: usize,
  late: usize,
  calls: usize,
}

impl Corpus {
  fn record(&mut self, case: &Case, expected: Option<bool>) -> usize {
    let native = Mmcs::new(
      SerializingHasher::new(Blake3),
      CompressionFunctionFromHasher::new(Blake3),
      case.cap_height,
    );
    let cap = MerkleCap::new(case.cap.clone());
    let proof = PrunedMerklePaths { sibling_hashes: case.proof.clone() };
    let accepted = native
      .verify_multi_batch(
        &cap,
        &case.dimensions,
        &case.indices,
        &case.rows,
        &proof,
      )
      .is_ok();
    if let Some(expected) = expected {
      assert_eq!(accepted, expected);
    }
    let calls = Calls::default();
    let hash = RecordingHash(calls.clone());
    let recording = RecordingMmcs::new(
      SerializingHasher::new(hash.clone()),
      CompressionFunctionFromHasher::new(hash),
      case.cap_height,
    );
    let recorded = recording
      .verify_multi_batch(
        &cap,
        &case.dimensions,
        &case.indices,
        &case.rows,
        &proof,
      )
      .is_ok();
    assert_eq!(accepted, recorded);
    let calls = calls.lock().unwrap();
    let degrees: Vec<u8> = case
      .dimensions
      .iter()
      .map(|dims| u8::try_from(dims.height.ilog2()).unwrap())
      .collect();
    let covered = trace_cap_coverage(0, case.cap_height, &degrees);
    self.count += 1;
    self.accepted += usize::from(accepted);
    self.omitted += usize::from(accepted && !covered);
    self.unhashed += usize::from(calls.is_empty());
    self.late += usize::from(!accepted && !calls.is_empty());
    self.calls += calls.len();
    let out = &mut self.body;
    number(out, case.dimensions.len());
    for dims in &case.dimensions {
      number(out, dims.width);
      number(out, usize::try_from(dims.height.ilog2()).unwrap());
    }
    number(out, case.cap_height);
    number(out, case.indices.len());
    for &index in &case.indices {
      number(out, index);
    }
    number(out, case.rows.len());
    for query in &case.rows {
      number(out, query.len());
      for row in query {
        number(out, row.len());
        for value in row {
          out.extend(value.as_canonical_u64().to_le_bytes());
        }
      }
    }
    digests(out, &case.proof);
    digests(out, &case.cap);
    out.extend([u8::from(accepted), u8::from(covered)]);
    number(out, calls.len());
    for (input, digest) in calls.iter() {
      number(out, input.len());
      out.extend(input);
      out.extend(digest);
    }
    calls.len()
  }
}

#[test]
fn pruned_merkle_snapshot() -> std::io::Result<()> {
  let shapes = [
    vec![0],
    vec![1],
    vec![3],
    vec![5],
    vec![3, 1],
    vec![1, 3],
    vec![3, 0, 2, 1],
    vec![2, 2, 2],
    vec![1, 4, 1, 4, 0],
    vec![4, 2, 3, 2],
  ];
  let widths = [1, 2, 3, 17, 33, 129];
  let mut corpus = Corpus::default();
  for (fixture, logs) in shapes.into_iter().enumerate() {
    let max_log = *logs.iter().max().unwrap();
    let height = 1 << max_log;
    let matrices: Vec<_> = logs
      .iter()
      .enumerate()
      .map(|(matrix, log)| {
        let width = widths[(fixture + matrix * 3) % widths.len()];
        let values = (0..width * (1 << log))
          .map(|i| {
            if i % 5 == 0 {
              -G::ONE
            } else {
              G::from_u64(
                u64::try_from(i * 65537 + matrix * 257 + fixture).unwrap(),
              )
            }
          })
          .collect();
        RowMajorMatrix::new(values, width)
      })
      .collect();
    let dimensions: Vec<_> = matrices.iter().map(Matrix::dimensions).collect();
    let queries = [
      vec![],
      vec![0],
      vec![height - 1],
      (0..height).collect(),
      (0..height).rev().collect(),
      (0..height).step_by(2).collect(),
      (1..height).step_by(2).collect(),
      vec![height - 1, 0, height / 2, height - 1, 0],
      vec![0, 0, 0],
      vec![0, (2 % height)],
    ];
    for cap_height in 0..=max_log + 2 {
      let mmcs = Mmcs::new(
        SerializingHasher::new(Blake3),
        CompressionFunctionFromHasher::new(Blake3),
        cap_height,
      );
      let (cap, data) = mmcs.commit(matrices.clone());
      for indices in &queries {
        let (rows, proof) = mmcs.open_multi_batch(indices, &data);
        let case = Case {
          dimensions: dimensions.clone(),
          indices: indices.clone(),
          rows,
          proof: proof.sibling_hashes,
          cap: cap.roots().to_vec(),
          cap_height,
        };
        corpus.record(&case, Some(true));
        let mut changed = case.clone();
        changed.proof.push([0; 32]);
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.rows.push(vec![]);
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.dimensions.clear();
        corpus.record(&changed, Some(false));
        if case.indices.is_empty() {
          continue;
        }
        for (matrix, &log) in logs.iter().enumerate() {
          let omitted = log < cap_height.min(max_log);
          let mut changed = case.clone();
          for query in &mut changed.rows {
            query[matrix][0] += G::ONE;
          }
          corpus.record(&changed, Some(omitted));
          let mut changed = case.clone();
          changed.rows[0][matrix][0] += G::ONE;
          corpus.record(&changed, if omitted { None } else { Some(false) });
        }
        if !case.proof.is_empty() {
          let mut changed = case.clone();
          changed.proof.pop();
          corpus.record(&changed, Some(false));
          let mut changed = case.clone();
          changed.proof[0][fixture % 32] ^= 1;
          corpus.record(&changed, Some(false));
        }
        let mut changed = case.clone();
        changed.dimensions[0].width += 1;
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.indices[0] = height;
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.cap[0][fixture % 32] ^= 1;
        corpus.record(&changed, None);
        let mut changed = case.clone();
        changed.cap.truncate(1);
        corpus.record(&changed, None);
        let mut changed = case.clone();
        changed.rows[0].pop();
        corpus.record(&changed, Some(false));
        if logs == [3, 1] && cap_height == 0 && indices == &[0, 2] {
          let mut changed = case.clone();
          changed.rows[1][1][0] += G::ONE;
          assert_eq!(corpus.record(&changed, Some(false)), 5);
        }
      }
    }
  }
  assert!(corpus.accepted > 100 && corpus.omitted > 100);
  assert!(corpus.unhashed > 1000 && corpus.late > 1000);
  let mut out = b"Aiur pruned Merkle v1\n".to_vec();
  for count in [
    corpus.count,
    corpus.accepted,
    corpus.omitted,
    corpus.unhashed,
    corpus.late,
    corpus.calls,
  ] {
    number(&mut out, count);
  }
  out.extend(corpus.body);
  println!(
    "Pruned Merkle: {} cases, {} accepted, {} omitted, {} unhashed, {} late, {} calls",
    corpus.count,
    corpus.accepted,
    corpus.omitted,
    corpus.unhashed,
    corpus.late,
    corpus.calls
  );
  if let Some(path) = std::env::var_os("IX_PRUNED_MERKLE_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}
