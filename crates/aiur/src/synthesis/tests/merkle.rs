// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Record the pinned native individual verifier's actual hash calls.
//! Commit/open use the production CPU MMCS; the recording hasher delegates
//! every call to the same native BLAKE3 implementation.

use super::*;
use multi_stark::{
  p3_field::PrimeField64,
  p3_matrix::{Dimensions, Matrix},
  types::Mmcs,
};
use p3_blake3::Blake3;
use p3_commit::{BatchOpeningRef, Mmcs as _};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{
  CompressionFunctionFromHasher, CryptographicHasher, MerkleCap,
  SerializingHasher,
};
use std::sync::{Arc, Mutex};

type Digest = [u8; 32];
type Calls = Arc<Mutex<Vec<(Vec<u8>, Digest)>>>;

#[derive(Clone)]
struct RecordingHash(Calls);

impl CryptographicHasher<u8, Digest> for RecordingHash {
  fn hash_iter<I: IntoIterator<Item = u8>>(&self, input: I) -> Digest {
    let bytes: Vec<_> = input.into_iter().collect();
    let digest = Blake3.hash_iter(bytes.iter().copied());
    self.0.lock().unwrap().push((bytes, digest));
    digest
  }
}

type RecordingMmcs = MerkleTreeMmcs<
  G,
  u8,
  SerializingHasher<RecordingHash>,
  CompressionFunctionFromHasher<RecordingHash, 2, 32>,
  2,
  32,
>;

#[derive(Clone)]
struct Case {
  dimensions: Vec<Dimensions>,
  rows: Vec<Vec<G>>,
  proof: Vec<Digest>,
  cap: Vec<Digest>,
  cap_height: usize,
  index: usize,
}

fn number(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn digests(out: &mut Vec<u8>, values: &[Digest]) {
  number(out, values.len());
  out.extend(values.iter().flatten());
}

#[derive(Default)]
struct Corpus {
  body: Vec<u8>,
  count: usize,
  accepted: usize,
  omitted: usize,
  unhashed: usize,
  calls: usize,
}

impl Corpus {
  fn record(&mut self, case: &Case, expected: Option<bool>) {
    let native = Mmcs::new(
      SerializingHasher::new(Blake3),
      CompressionFunctionFromHasher::new(Blake3),
      case.cap_height,
    );
    let cap = MerkleCap::new(case.cap.clone());
    let accepted = native
      .verify_batch(
        &cap,
        &case.dimensions,
        case.index,
        BatchOpeningRef::new(&case.rows, &case.proof),
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
      .verify_batch(
        &cap,
        &case.dimensions,
        case.index,
        BatchOpeningRef::new(&case.rows, &case.proof),
      )
      .is_ok();
    assert_eq!(accepted, recorded);
    let calls = calls.lock().unwrap();
    let degrees: Vec<u8> = case
      .dimensions
      .iter()
      .map(|dims| u8::try_from(dims.height.ilog2()).unwrap())
      .collect();
    let covered =
      crate::trace_heights::trace_cap_coverage(0, case.cap_height, &degrees);
    self.count += 1;
    self.accepted += usize::from(accepted);
    self.omitted += usize::from(accepted && !covered);
    self.unhashed += usize::from(calls.is_empty());
    self.calls += calls.len();
    let out = &mut self.body;
    number(out, case.dimensions.len());
    for dims in &case.dimensions {
      number(out, dims.width);
      number(out, usize::try_from(dims.height.ilog2()).unwrap());
    }
    number(out, case.cap_height);
    number(out, case.index);
    number(out, case.rows.len());
    for row in &case.rows {
      number(out, row.len());
      for value in row {
        out.extend(value.as_canonical_u64().to_le_bytes());
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
  }
}

#[test]
fn merkle_path_snapshot() -> std::io::Result<()> {
  let shapes = [
    vec![0],
    vec![1],
    vec![2],
    vec![3],
    vec![4],
    vec![7],
    vec![3, 1],
    vec![1, 3],
    vec![3, 0, 2, 1],
    vec![2, 2, 2],
    vec![1, 4, 1, 4, 0],
    vec![4, 2, 3, 2],
  ];
  let widths = [1, 2, 3, 7, 8, 9, 16, 17, 31, 32, 33, 129];
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
            let value = match i % 7 {
              0 => 0,
              1 => 1,
              2 => 0xffff_ffff_0000_0000,
              3 => 0xffff_ffff,
              4 => 0x1_0000_0000,
              _ => u64::try_from(i * 65537 + matrix * 257 + fixture).unwrap(),
            };
            G::from_u64(value)
          })
          .collect();
        RowMajorMatrix::new(values, width)
      })
      .collect();
    let dimensions: Vec<_> = matrices.iter().map(Matrix::dimensions).collect();
    let indices: Vec<_> = if height <= 16 {
      (0..height).collect()
    } else {
      vec![0, 1, 2, height / 2 - 1, height / 2, height - 2, height - 1]
    };
    for cap_height in 0..=max_log + 2 {
      let mmcs = Mmcs::new(
        SerializingHasher::new(Blake3),
        CompressionFunctionFromHasher::new(Blake3),
        cap_height,
      );
      let (cap, data) = mmcs.commit(matrices.clone());
      for &index in &indices {
        let opening = mmcs.open_batch(index, &data);
        let case = Case {
          dimensions: dimensions.clone(),
          rows: opening.opened_values,
          proof: opening.opening_proof,
          cap: cap.roots().to_vec(),
          cap_height,
          index,
        };
        corpus.record(&case, Some(true));
        for (matrix, &log) in logs.iter().enumerate() {
          let mut changed = case.clone();
          changed.rows[matrix][0] += G::ONE;
          corpus.record(&changed, Some(log < cap_height.min(max_log)));
        }
        if !case.proof.is_empty() {
          let mut changed = case.clone();
          changed.proof.pop();
          corpus.record(&changed, Some(false));
          let mut changed = case.clone();
          changed.proof[0][index % 32] ^= 1;
          corpus.record(&changed, Some(false));
        }
        let mut changed = case.clone();
        changed.proof.push([0; 32]);
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.rows.pop();
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.dimensions[0].width += 1;
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.index = height;
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.cap[index >> case.proof.len()][index % 32] ^= 1;
        corpus.record(&changed, Some(false));
        let mut changed = case.clone();
        changed.dimensions[0].height *= 2;
        corpus.record(&changed, None);
        let mut changed = case.clone();
        changed.dimensions[0].width = 0;
        changed.rows[0].clear();
        corpus.record(&changed, None);
        let mut changed = case.clone();
        changed.cap.truncate(1);
        corpus.record(&changed, None);
        let mut changed = case.clone();
        changed.dimensions.clear();
        changed.rows.clear();
        corpus.record(&changed, Some(false));
      }
    }
  }
  assert!(corpus.accepted > 500 && corpus.omitted > 100);
  assert!(corpus.unhashed > 1000 && corpus.calls > 10000);
  let mut out = b"Aiur Merkle paths v1\n".to_vec();
  for count in [
    corpus.count,
    corpus.accepted,
    corpus.omitted,
    corpus.unhashed,
    corpus.calls,
  ] {
    number(&mut out, count);
  }
  out.extend(corpus.body);
  println!(
    "Merkle paths: {} cases, {} accepted, {} omitted, {} unhashed, {} calls",
    corpus.count,
    corpus.accepted,
    corpus.omitted,
    corpus.unhashed,
    corpus.calls
  );
  if let Some(path) = std::env::var_os("IX_MERKLE_PATH_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}
