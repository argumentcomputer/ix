//! MultiStark-native execute path.
//!
//! Parallel to `aiur::execute::Toplevel::execute`, but routes the
//! Aiur fn invocation through the codegen'd Rust recursive verifier
//! (`crate::aiur_multi_stark::execute_generated`) instead of the
//! interpreter. Mirror of `aiur_ixvm_runner` for the MultiStark
//! toplevel — same `QueryRecord` shape, same multiplicity rules,
//! same memory and IO side effects, so the trace produced here is
//! byte-for-byte identical to the interpreter's (modulo the
//! `execute_generated` codegen's correctness, which is the standing
//! parity invariant).
//!
//! Also home to `verifier_io_buffer`, the native builder for
//! `verify_multi_stark_proof`'s IO advice — replaces the Lean-side
//! `MultiStark.verifierInput` buffer construction, which boxed every
//! proof/vk/claims byte into a Lean `G` and marshalled the whole
//! buffer across FFI.

use multi_stark::p3_field::PrimeCharacteristicRing;
use rustc_hash::FxHashMap;

use crate::aiur_multi_stark::execute_generated;
use aiur::G;
use aiur::bytecode::{FunIdx, Toplevel};
use aiur::execute::{ExecError, IOBuffer, IOKeyInfo, QueryRecord};

/// One content-addressed preimage consumed by `join_two` on IO channel 4.
/// The digest is keyed in the same packed-four-byte form as an Aiur public
/// digest; the circuit re-hashes `bytes` before using the decoded claim.
#[derive(Clone, Copy, Debug)]
pub struct JoinPreimage<'a> {
  pub digest: [u8; 32],
  pub bytes: &'a [u8],
}

/// One serialized `AssumptionTree` consumed by `join_two` on IO channel 5.
/// Tree roots use the kernel's address key representation: one field element
/// per byte, rather than the packed public-digest representation.
#[derive(Clone, Copy, Debug)]
pub struct JoinTree<'a> {
  pub root: [u8; 32],
  pub bytes: &'a [u8],
}

/// One carried/discharged choice consumed by `join_two_structural` on IO
/// channel 6. Candidates use the same raw-address key representation as trees;
/// the circuit strictly parses the choice and verifies every discharge path.
#[derive(Clone, Copy, Debug)]
pub struct JoinPath<'a> {
  pub candidate: [u8; 32],
  pub bytes: &'a [u8],
}

/// Raw advice for one binary aggregate-first join.
///
/// This is deliberately a borrowed view: real shard and recursive proofs are
/// multi-megabyte blobs, so constructing an IO buffer must not first clone the
/// caller's byte arrays into an intermediate owned request object.
#[derive(Clone, Copy, Debug)]
pub struct JoinAdvice<'a> {
  pub proofs: [&'a [u8]; 2],
  pub recursion_vk: &'a [u8],
  pub child_claims: [&'a [u8]; 2],
  pub output_claim: &'a [u8],
  pub allowed: &'a [u8],
  pub preimages: &'a [JoinPreimage<'a>],
  pub trees: &'a [JoinTree<'a>],
  pub paths: &'a [JoinPath<'a>],
}

/// Decode the compact host/FFI representation of digest-addressed join
/// preimages. The wire format is a little-endian `u32` entry count followed
/// by `(32-byte key, u32 payload length, payload)` entries.
pub fn decode_join_preimages(
  blob: &[u8],
) -> Result<Vec<JoinPreimage<'_>>, String> {
  decode_keyed_blobs(blob, "join preimages").map(|entries| {
    entries
      .into_iter()
      .map(|(digest, bytes)| JoinPreimage { digest, bytes })
      .collect()
  })
}

/// Decode the compact host/FFI representation of root-addressed join trees.
/// Its framing is identical to [`decode_join_preimages`].
pub fn decode_join_trees(blob: &[u8]) -> Result<Vec<JoinTree<'_>>, String> {
  decode_keyed_blobs(blob, "join trees").map(|entries| {
    entries.into_iter().map(|(root, bytes)| JoinTree { root, bytes }).collect()
  })
}

/// Decode the compact candidate-addressed structural-discharge choices. Its
/// framing is identical to [`decode_join_preimages`]; payload semantics are
/// checked by the circuit.
pub fn decode_join_paths(blob: &[u8]) -> Result<Vec<JoinPath<'_>>, String> {
  decode_keyed_blobs(blob, "join paths").map(|entries| {
    entries
      .into_iter()
      .map(|(candidate, bytes)| JoinPath { candidate, bytes })
      .collect()
  })
}

fn decode_keyed_blobs<'a>(
  blob: &'a [u8],
  label: &str,
) -> Result<Vec<([u8; 32], &'a [u8])>, String> {
  let mut cursor = 0usize;
  let count = read_u32(blob, &mut cursor, label)? as usize;
  let max_entries = blob.len().saturating_sub(cursor) / 36;
  if count > max_entries {
    return Err(format!(
      "{label}: declares {count} entries, but the blob can contain at most \
       {max_entries} complete key/length headers"
    ));
  }
  let mut entries = Vec::with_capacity(count);
  for entry_index in 0..count {
    let key_end = cursor.checked_add(32).ok_or_else(|| {
      format!("{label}: entry {entry_index} key offset overflow")
    })?;
    let key_slice = blob.get(cursor..key_end).ok_or_else(|| {
      format!("{label}: truncated 32-byte key for entry {entry_index}")
    })?;
    let key: [u8; 32] =
      key_slice.try_into().expect("slice length was checked above");
    cursor = key_end;

    let payload_len = read_u32(blob, &mut cursor, label)? as usize;
    let payload_end = cursor.checked_add(payload_len).ok_or_else(|| {
      format!("{label}: entry {entry_index} payload offset overflow")
    })?;
    let payload = blob.get(cursor..payload_end).ok_or_else(|| {
      format!(
        "{label}: entry {entry_index} declares {payload_len} payload bytes, \
         but only {} remain",
        blob.len().saturating_sub(cursor)
      )
    })?;
    cursor = payload_end;
    entries.push((key, payload));
  }
  if cursor != blob.len() {
    return Err(format!(
      "{label}: {} trailing bytes after {count} entries",
      blob.len() - cursor
    ));
  }
  Ok(entries)
}

fn read_u32(
  blob: &[u8],
  cursor: &mut usize,
  label: &str,
) -> Result<u32, String> {
  let end = cursor
    .checked_add(4)
    .ok_or_else(|| format!("{label}: length offset overflow"))?;
  let bytes: [u8; 4] = blob
    .get(*cursor..end)
    .ok_or_else(|| format!("{label}: truncated u32 length"))?
    .try_into()
    .expect("slice length was checked above");
  *cursor = end;
  Ok(u32::from_le_bytes(bytes))
}

/// Append one keyed byte stream to an IO channel arena.
#[inline]
fn extend_bytes(io: &mut IOBuffer, channel: G, key: Vec<G>, bytes: &[u8]) {
  let arena = io.data.entry(channel).or_default();
  let idx = arena.len();
  let len = bytes.len();
  arena.extend(bytes.iter().map(|b| G::from_u8(*b)));
  io.map.insert((channel, key), IOKeyInfo { idx, len });
}

/// An integer stream index (`[0]`, `[1]`, or `[2]`) as an Aiur IO key.
#[inline]
fn index_key(index: u8) -> Vec<G> {
  vec![G::from_u8(index)]
}

/// A Blake3 digest as eight packed little-endian `u32` field elements.
/// Mirrors in-circuit `b3_pack` and Lean `MultiStark.digestGs`.
#[inline]
fn packed_digest_key(digest: &[u8; 32]) -> Vec<G> {
  digest
    .chunks_exact(4)
    .map(|word| {
      G::from_u32(u32::from_le_bytes(word.try_into().expect("four-byte chunk")))
    })
    .collect()
}

/// A 32-byte address as 32 field elements, matching the IxVM tree-loader key.
#[inline]
fn address_key(address: &[u8; 32]) -> Vec<G> {
  address.iter().map(|b| G::from_u8(*b)).collect()
}

/// Mirror of `Toplevel::execute` (same return shape, same
/// `entry`-flag gate), but routes execution through the codegen'd
/// Rust verifier. Deep recursion is handled via per-fn
/// `stacker::maybe_grow` checks in the generated code.
// `args: Vec<G>` mirrors `Toplevel::execute`'s signature so this fn
// can be used as an `impl Fn(&Toplevel, _, Vec<G>, _) -> _` in
// `AiurSystem::prove_ixvm` — a `&[G]` here would break that bound.
#[allow(clippy::needless_pass_by_value)]
pub fn execute_multi_stark(
  toplevel: &Toplevel,
  fun_idx: FunIdx,
  args: Vec<G>,
  io_buffer: &mut IOBuffer,
) -> Result<(QueryRecord, Vec<G>), ExecError> {
  if !toplevel.functions[fun_idx].entry {
    return Err(ExecError::NotEntryFunction(fun_idx));
  }
  let mut record = QueryRecord::new(toplevel);
  let output = execute_generated(fun_idx, &args, &mut record, io_buffer)?;
  Ok((record, output))
}

/// Build `verify_multi_stark_proof`'s IO advice directly from the raw
/// byte blobs: channel 0 = proof, 1 = vk, 2 = claims, each registered
/// under key `[0]` on its channel (one stream per channel). Mirrors
/// the layout of `MultiStark.verifierInput` (`Ix/MultiStark.lean`).
pub fn verifier_io_buffer(proof: &[u8], vk: &[u8], claims: &[u8]) -> IOBuffer {
  // Measurement hook: dump the raw advice blobs for offline analysis
  // (vk encoding/activation studies) when IX_DUMP_RECURSION_IO is set
  // to a directory.
  if let Ok(dir) = std::env::var("IX_DUMP_RECURSION_IO") {
    let _ = std::fs::write(format!("{dir}/proof.bin"), proof);
    let _ = std::fs::write(format!("{dir}/vk.bin"), vk);
    let _ = std::fs::write(format!("{dir}/claims.bin"), claims);
  }
  let mut io =
    IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };
  for (channel, bytes) in [(0u8, proof), (1, vk), (2, claims)] {
    extend_bytes(&mut io, G::from_u8(channel), index_key(0), bytes);
  }
  io
}

/// Build the flat/structural join entrypoints' seven-channel IO advice buffer.
///
/// Layout (the circuit binds every digest-addressed blob before decoding):
///
/// * ch 0 `[0]`, `[1]`: left/right recursive proof bytes;
/// * ch 1 `[0]`: the recursion system verifying key;
/// * ch 2 `[0]`, `[1]`, `[2]`: child outer claims and output `CheckEnv` claim;
/// * ch 3 `[0]`: the digest-bound allowed-vk blob;
/// * ch 4 `packed(blake3)`: nested claim preimages;
/// * ch 5 `root bytes`: serialized subject/assumption trees;
/// * ch 6 `candidate bytes`: carried/discharged choices and Merkle paths.
pub fn join_io_buffer(advice: &JoinAdvice<'_>) -> IOBuffer {
  let mut io =
    IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };

  extend_bytes(&mut io, G::from_u8(0), index_key(0), advice.proofs[0]);
  extend_bytes(&mut io, G::from_u8(0), index_key(1), advice.proofs[1]);
  extend_bytes(&mut io, G::from_u8(1), index_key(0), advice.recursion_vk);
  extend_bytes(&mut io, G::from_u8(2), index_key(0), advice.child_claims[0]);
  extend_bytes(&mut io, G::from_u8(2), index_key(1), advice.child_claims[1]);
  extend_bytes(&mut io, G::from_u8(2), index_key(2), advice.output_claim);
  extend_bytes(&mut io, G::from_u8(3), index_key(0), advice.allowed);

  for preimage in advice.preimages {
    extend_bytes(
      &mut io,
      G::from_u8(4),
      packed_digest_key(&preimage.digest),
      preimage.bytes,
    );
  }
  for tree in advice.trees {
    extend_bytes(&mut io, G::from_u8(5), address_key(&tree.root), tree.bytes);
  }
  for path in advice.paths {
    extend_bytes(
      &mut io,
      G::from_u8(6),
      address_key(&path.candidate),
      path.bytes,
    );
  }

  io
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::p3_field::PrimeField64;

  fn info(io: &IOBuffer, channel: u8, key: Vec<G>) -> (usize, usize) {
    let info =
      io.map.get(&(G::from_u8(channel), key)).expect("missing IO mapping");
    (info.idx, info.len)
  }

  fn arena_bytes(io: &IOBuffer, channel: u8) -> Vec<u8> {
    io.data[&G::from_u8(channel)]
      .iter()
      .map(|g| u8::try_from(g.as_canonical_u64()).expect("IO test byte"))
      .collect()
  }

  #[test]
  fn verifier_layout_remains_three_zero_keyed_channels() {
    let io = verifier_io_buffer(&[1, 2], &[3], &[4, 5, 6]);
    assert_eq!(info(&io, 0, index_key(0)), (0, 2));
    assert_eq!(info(&io, 1, index_key(0)), (0, 1));
    assert_eq!(info(&io, 2, index_key(0)), (0, 3));
    assert_eq!(arena_bytes(&io, 0), vec![1, 2]);
    assert_eq!(arena_bytes(&io, 1), vec![3]);
    assert_eq!(arena_bytes(&io, 2), vec![4, 5, 6]);
  }

  #[test]
  fn join_layout_indexes_streams_and_uses_both_digest_key_encodings() {
    let mut digest = [0u8; 32];
    for (i, byte) in digest.iter_mut().enumerate() {
      *byte = u8::try_from(i).expect("32-byte index");
    }
    let mut root = [0u8; 32];
    for (i, byte) in root.iter_mut().enumerate() {
      *byte = u8::try_from(31 - i).expect("32-byte reverse index");
    }
    let preimages = [JoinPreimage { digest, bytes: &[11, 12] }];
    let trees = [JoinTree { root, bytes: &[13, 14, 15] }];
    let paths = [JoinPath { candidate: root, bytes: &[1, 0] }];
    let advice = JoinAdvice {
      proofs: [&[1, 2], &[3]],
      recursion_vk: &[4, 5],
      child_claims: [&[6], &[7, 8]],
      output_claim: &[9],
      allowed: &[10],
      preimages: &preimages,
      trees: &trees,
      paths: &paths,
    };

    let io = join_io_buffer(&advice);

    assert_eq!(arena_bytes(&io, 0), vec![1, 2, 3]);
    assert_eq!(info(&io, 0, index_key(0)), (0, 2));
    assert_eq!(info(&io, 0, index_key(1)), (2, 1));

    assert_eq!(arena_bytes(&io, 2), vec![6, 7, 8, 9]);
    assert_eq!(info(&io, 2, index_key(0)), (0, 1));
    assert_eq!(info(&io, 2, index_key(1)), (1, 2));
    assert_eq!(info(&io, 2, index_key(2)), (3, 1));

    assert_eq!(info(&io, 3, index_key(0)), (0, 1));
    assert_eq!(info(&io, 4, packed_digest_key(&digest)), (0, 2));
    assert_eq!(info(&io, 5, address_key(&root)), (0, 3));
    assert_eq!(info(&io, 6, address_key(&root)), (0, 2));
    assert_ne!(packed_digest_key(&digest), address_key(&digest));
  }

  #[test]
  fn keyed_join_blobs_decode_strictly_without_copying_payloads() {
    let key = [7u8; 32];
    let mut blob = Vec::new();
    blob.extend_from_slice(&1u32.to_le_bytes());
    blob.extend_from_slice(&key);
    blob.extend_from_slice(&3u32.to_le_bytes());
    blob.extend_from_slice(&[8, 9, 10]);

    let preimages = decode_join_preimages(&blob).expect("valid preimage blob");
    assert_eq!(preimages.len(), 1);
    assert_eq!(preimages[0].digest, key);
    assert_eq!(preimages[0].bytes, &[8, 9, 10]);

    let trees = decode_join_trees(&blob).expect("valid tree blob");
    assert_eq!(trees[0].root, key);
    assert_eq!(trees[0].bytes, &[8, 9, 10]);

    let paths = decode_join_paths(&blob).expect("valid path blob");
    assert_eq!(paths[0].candidate, key);
    assert_eq!(paths[0].bytes, &[8, 9, 10]);

    blob.push(11);
    assert!(decode_join_preimages(&blob).is_err());
    assert!(decode_join_trees(&[1, 0, 0]).is_err());
    assert!(decode_join_paths(&[1, 0, 0]).is_err());
  }
}
