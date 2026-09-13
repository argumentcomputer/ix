// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Actual extension MMCS delegation, coordinate order and machine widths.

use super::merkle::{
  Calls, Digest, RecordingHash, RecordingMmcs, digests, number,
};
use super::*;
use multi_stark::{
  p3_field::{BasedVectorSpace, PrimeField64},
  p3_matrix::{Dimensions, Matrix},
  types::{ExtMmcs, ExtVal, Mmcs},
};
use p3_blake3::Blake3;
use p3_commit::{BatchOpeningRef, ExtensionMmcs, Mmcs as _};
use p3_merkle_tree::PrunedMerklePaths;
use p3_symmetric::{
  CompressionFunctionFromHasher, MerkleCap, SerializingHasher,
};

#[derive(Clone)]
struct Case {
  shared: bool,
  dimensions: Vec<Dimensions>,
  indices: Vec<usize>,
  rows: Vec<Vec<Vec<ExtVal>>>,
  proof: Vec<Digest>,
  cap: Vec<Digest>,
  cap_height: usize,
}

#[derive(Default)]
struct Corpus {
  body: Vec<u8>,
  count: usize,
  shared: usize,
  accepted: usize,
  omitted: usize,
  overflow: usize,
  late: usize,
  calls: usize,
}

impl Corpus {
  fn record(&mut self, case: &Case, expected: Option<bool>) {
    let base = Mmcs::new(
      SerializingHasher::new(Blake3),
      CompressionFunctionFromHasher::new(Blake3),
      case.cap_height,
    );
    let native = ExtMmcs::new(base.clone());
    let cap = MerkleCap::new(case.cap.clone());
    let proof = PrunedMerklePaths { sibling_hashes: case.proof.clone() };
    let accepted = if case.shared {
      native.verify_multi_batch(
        &cap,
        &case.dimensions,
        &case.indices,
        &case.rows,
        &proof,
      )
    } else {
      native.verify_batch(
        &cap,
        &case.dimensions,
        case.indices[0],
        BatchOpeningRef::new(&case.rows[0], &case.proof),
      )
    }
    .is_ok();
    if let Some(expected) = expected {
      assert_eq!(accepted, expected);
    }
    let dimensions: Vec<_> = case
      .dimensions
      .iter()
      .map(|dim| Dimensions {
        width: dim.width.wrapping_mul(2),
        height: dim.height,
      })
      .collect();
    let rows: Vec<Vec<Vec<G>>> = case
      .rows
      .iter()
      .map(|rows| rows.iter().cloned().map(ExtVal::flatten_to_base).collect())
      .collect();
    let delegated = if case.shared {
      base.verify_multi_batch(&cap, &dimensions, &case.indices, &rows, &proof)
    } else {
      base.verify_batch(
        &cap,
        &dimensions,
        case.indices[0],
        BatchOpeningRef::new(&rows[0], &case.proof),
      )
    }
    .is_ok();
    assert_eq!(accepted, delegated);
    let calls = Calls::default();
    let hash = RecordingHash(calls.clone());
    let recording = ExtensionMmcs::<G, ExtVal, _>::new(RecordingMmcs::new(
      SerializingHasher::new(hash.clone()),
      CompressionFunctionFromHasher::new(hash),
      case.cap_height,
    ));
    let recorded = if case.shared {
      recording.verify_multi_batch(
        &cap,
        &case.dimensions,
        &case.indices,
        &case.rows,
        &proof,
      )
    } else {
      recording.verify_batch(
        &cap,
        &case.dimensions,
        case.indices[0],
        BatchOpeningRef::new(&case.rows[0], &case.proof),
      )
    }
    .is_ok();
    assert_eq!(accepted, recorded);
    let calls = calls.lock().unwrap();
    let degrees: Vec<u8> = case
      .dimensions
      .iter()
      .map(|dim| u8::try_from(dim.height.ilog2()).unwrap())
      .collect();
    let covered =
      crate::trace_heights::trace_cap_coverage(0, case.cap_height, &degrees);
    let widths_fit =
      case.dimensions.iter().all(|dim| dim.width.checked_mul(2).is_some());
    self.count += 1;
    self.shared += usize::from(case.shared);
    self.accepted += usize::from(accepted);
    self.omitted += usize::from(accepted && !covered);
    self.overflow += usize::from(!widths_fit);
    self.late += usize::from(!accepted && !calls.is_empty());
    self.calls += calls.len();
    let out = &mut self.body;
    out.push(u8::from(case.shared));
    number(out, case.dimensions.len());
    for dim in &case.dimensions {
      number(out, dim.width);
      number(out, usize::try_from(dim.height.ilog2()).unwrap());
    }
    number(out, case.cap_height);
    number(out, case.indices.len());
    for &index in &case.indices {
      number(out, index);
    }
    number(out, case.rows.len());
    for rows in &case.rows {
      number(out, rows.len());
      for row in rows {
        number(out, row.len());
        for value in row {
          let coordinates: &[G] = value.as_basis_coefficients_slice();
          for coordinate in coordinates {
            out.extend(coordinate.as_canonical_u64().to_le_bytes());
          }
        }
      }
    }
    digests(out, &case.proof);
    digests(out, &case.cap);
    out.extend([u8::from(accepted), u8::from(covered), u8::from(widths_fit)]);
    number(out, calls.len());
    for (input, digest) in calls.iter() {
      number(out, input.len());
      out.extend(input);
      out.extend(digest);
    }
  }

  fn mutations(&mut self, case: &Case, logs: &[usize]) {
    self.record(case, Some(true));
    let mut changed = case.clone();
    changed.proof.push([0; 32]);
    self.record(&changed, Some(false));
    let mut changed = case.clone();
    changed.dimensions.clear();
    self.record(&changed, Some(false));
    if case.shared {
      let mut changed = case.clone();
      changed.rows.push(vec![]);
      self.record(&changed, Some(false));
    }
    if case.indices.is_empty() {
      return;
    }
    let max_log = *logs.iter().max().unwrap();
    for (matrix, &log) in logs.iter().enumerate() {
      let omitted = log < case.cap_height.min(max_log);
      for increment in [ExtVal::ONE, ExtVal::new([G::ZERO, G::ONE])] {
        let mut changed = case.clone();
        for query in &mut changed.rows {
          query[matrix][0] += increment;
        }
        self.record(&changed, Some(omitted));
        if case.shared {
          let mut changed = case.clone();
          changed.rows[0][matrix][0] += increment;
          self.record(&changed, if omitted { None } else { Some(false) });
        }
      }
    }
    if !case.proof.is_empty() {
      let mut changed = case.clone();
      changed.proof.pop();
      self.record(&changed, Some(false));
      let mut changed = case.clone();
      changed.proof[0][0] ^= 1;
      self.record(&changed, Some(false));
    }
    let mut changed = case.clone();
    changed.dimensions[0].width += 1;
    self.record(&changed, Some(false));
    let mut changed = case.clone();
    changed.indices[0] = 1 << max_log;
    self.record(&changed, Some(false));
    let mut changed = case.clone();
    changed.cap[0][0] ^= 1;
    self.record(&changed, None);
    let mut changed = case.clone();
    changed.cap.truncate(1);
    self.record(&changed, None);
    let mut changed = case.clone();
    changed.rows[0].pop();
    self.record(&changed, Some(false));
    // The adapter multiplies verifier metadata using release usize arithmetic.
    // Exercise the wrap explicitly; debug builds instead check overflow.
    if !cfg!(debug_assertions) {
      let mut changed = case.clone();
      changed.dimensions[0].width += 1usize << (usize::BITS - 1);
      self.record(&changed, Some(true));
    }
  }
}

#[test]
fn extension_mmcs_snapshot() -> std::io::Result<()> {
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
  ];
  let widths = [1, 2, 3, 9, 17, 65];
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
            ExtVal::new([
              G::from_u64(u64::try_from(i * 65537 + fixture).unwrap()),
              if i % 3 == 0 {
                -G::ONE
              } else {
                G::from_u64(u64::try_from(i * 257 + matrix + 1).unwrap())
              },
            ])
          })
          .collect();
        RowMajorMatrix::new(values, width)
      })
      .collect();
    let dimensions: Vec<_> = matrices.iter().map(Matrix::dimensions).collect();
    let flat_matrices: Vec<_> = matrices
      .iter()
      .map(|matrix| {
        RowMajorMatrix::new(
          ExtVal::flatten_to_base(matrix.values.clone()),
          matrix.width * 2,
        )
      })
      .collect();
    let queries = [
      vec![],
      vec![0],
      vec![height - 1],
      (0..height).rev().collect(),
      (0..height).step_by(2).collect(),
      (1..height).step_by(2).collect(),
      vec![height - 1, 0, height / 2, height - 1, 0],
      vec![0, (2 % height)],
    ];
    for cap_height in 0..=max_log + 2 {
      let base = Mmcs::new(
        SerializingHasher::new(Blake3),
        CompressionFunctionFromHasher::new(Blake3),
        cap_height,
      );
      let mmcs = ExtMmcs::new(base.clone());
      let (cap, data) = mmcs.commit(matrices.clone());
      let (base_cap, _) = base.commit(flat_matrices.clone());
      assert_eq!(cap, base_cap);
      for index in [0, height / 2, height - 1] {
        let (rows, proof) = mmcs.open_batch(index, &data).unpack();
        corpus.mutations(
          &Case {
            shared: false,
            dimensions: dimensions.clone(),
            indices: vec![index],
            rows: vec![rows],
            proof,
            cap: cap.roots().to_vec(),
            cap_height,
          },
          &logs,
        );
      }
      for indices in &queries {
        let (rows, proof) = mmcs.open_multi_batch(indices, &data);
        corpus.mutations(
          &Case {
            shared: true,
            dimensions: dimensions.clone(),
            indices: indices.clone(),
            rows,
            proof: proof.sibling_hashes,
            cap: cap.roots().to_vec(),
            cap_height,
          },
          &logs,
        );
      }
    }
  }
  let counts = [
    corpus.count,
    corpus.shared,
    corpus.accepted,
    corpus.omitted,
    corpus.overflow,
    corpus.late,
    corpus.calls,
  ];
  assert!(corpus.count > 1000 && corpus.calls > 1000);
  println!("Extension MMCS: {counts:?}");
  let mut out = b"Aiur extension MMCS v1\n".to_vec();
  number(&mut out, usize::BITS as usize);
  for count in counts {
    number(&mut out, count);
  }
  out.extend(corpus.body);
  if let Some(path) = std::env::var_os("IX_EXTENSION_MMCS_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}
