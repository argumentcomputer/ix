// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Independent native outputs for the checked unkeyed BLAKE3 implementation.

use ::blake3::{
  Hasher,
  hazmat::{
    HasherExt, Mode, left_subtree_len, merge_subtrees_non_root,
    merge_subtrees_root,
  },
};
use p3_symmetric::CryptographicHasher;
use std::collections::BTreeSet;

fn number(out: &mut Vec<u8>, value: u64) {
  out.extend(value.to_le_bytes());
}

fn bytes(out: &mut Vec<u8>, value: &[u8]) {
  number(out, u64::try_from(value.len()).unwrap());
  out.extend(value);
}

fn input(length: usize, salt: usize) -> Vec<u8> {
  (0..length)
    .map(|i| u8::try_from((i * 17 + i / 251 * 13 + salt * 29) % 256).unwrap())
    .collect()
}

#[test]
fn blake3_snapshot() -> std::io::Result<()> {
  let mut out = b"Aiur Blake3 v1\n".to_vec();
  let mut lengths: BTreeSet<usize> = (0..=128).chain(960..=1024).collect();
  lengths.extend([255, 256, 257, 511, 512, 513]);
  for chunks in (1..=17).chain([32, 64, 128]) {
    lengths.extend([chunks * 1024 - 1, chunks * 1024, chunks * 1024 + 1]);
  }
  number(&mut out, u64::try_from(lengths.len()).unwrap());
  for (case, length) in lengths.into_iter().enumerate() {
    let data = input(length, case);
    let expected = ::blake3::hash(&data);
    let p3: [u8; 32] = p3_blake3::Blake3.hash_iter(data.iter().copied());
    assert_eq!(p3, *expected.as_bytes());
    let mut stream = Hasher::new();
    for part in
      data.chunks([1, 63, 64, 65, 511, 512, 1023, 1024, 1025][case % 9])
    {
      stream.update(part);
    }
    assert_eq!(stream.finalize(), expected);
    bytes(&mut out, &data);
    out.extend(expected.as_bytes());
    if length > 1024 {
      let split = left_subtree_len(u64::try_from(length).unwrap());
      number(&mut out, split);
      let split = usize::try_from(split).unwrap();
      let left = Hasher::new().update(&data[..split]).finalize_non_root();
      let right = Hasher::new()
        .set_input_offset(u64::try_from(split).unwrap())
        .update(&data[split..])
        .finalize_non_root();
      assert_eq!(merge_subtrees_root(&left, &right, Mode::Hash), expected);
      out.extend(left);
      out.extend(right);
    }
  }
  let counters = [0, 1, 2, 255, (1 << 32) - 1, 1 << 32, (1 << 54) - 1];
  let chunk_lengths = [1, 63, 64, 65, 1023, 1024];
  number(
    &mut out,
    u64::try_from(counters.len() * chunk_lengths.len()).unwrap(),
  );
  for counter in counters {
    for length in chunk_lengths {
      let data = input(length, usize::try_from(counter % 251).unwrap());
      let cv = Hasher::new()
        .set_input_offset(counter * 1024)
        .update(&data)
        .finalize_non_root();
      number(&mut out, counter);
      bytes(&mut out, &data);
      out.extend(cv);
    }
  }
  number(&mut out, 64);
  for salt in 0..64 {
    let left: [u8; 32] = input(32, salt).try_into().unwrap();
    let right: [u8; 32] = input(32, salt + 83).try_into().unwrap();
    out.extend(left);
    out.extend(right);
    out.extend(merge_subtrees_non_root(&left, &right, Mode::Hash));
    out.extend(merge_subtrees_root(&left, &right, Mode::Hash).as_bytes());
    // PCS Merkle compression is an ordinary hash of 64 digest bytes.
    out.extend(::blake3::hash(&[left, right].concat()).as_bytes());
  }
  if let Some(path) = std::env::var_os("IX_BLAKE3_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}
