//! ixAggr-native execute path.
//!
//! Mirror of `aiur_multi_stark_runner` for the `ixAggr` toplevel: routes the
//! Aiur fn invocation through the codegen'd Rust aggregator
//! (`crate::aiur_ix_aggr::execute_generated`) instead of the interpreter,
//! with the same `QueryRecord` shape, multiplicity rules, and IO side
//! effects, so the trace produced here is byte-for-byte identical to the
//! interpreter's (modulo the codegen parity invariant).
//!
//! Also home to `aggr_io_buffer`, the native builder for `ix_aggr`'s
//! seven-channel IO advice, and the strict decoders for the compact keyed
//! blob framing the Lean host uses to hand preimages and trees across FFI.

use multi_stark::p3_field::PrimeCharacteristicRing;
use rustc_hash::FxHashMap;

use crate::aiur_ix_aggr::execute_generated;
use aiur::G;
use aiur::bytecode::{FunIdx, Toplevel};
use aiur::execute::{ExecError, IOBuffer, IOKeyInfo, QueryRecord};

/// One content-addressed `CheckEnv` preimage consumed by `ix_aggr` on IO
/// channel 4. The digest is keyed in the packed-four-byte public-digest
/// form; the circuit re-hashes `bytes` before using the decoded claim.
#[derive(Clone, Copy, Debug)]
pub struct AggrPreimage<'a> {
  pub digest: [u8; 32],
  pub bytes: &'a [u8],
}

/// One serialized canonical `AssumptionTree` consumed by `ix_aggr` on IO
/// channel 5. Tree roots use the raw-address key representation: one field
/// element per byte.
#[derive(Clone, Copy, Debug)]
pub struct AggrTree<'a> {
  pub root: [u8; 32],
  pub bytes: &'a [u8],
}

/// One carried/discharged choice consumed by structural `ix_aggr` shapes on
/// IO channel 6. Candidates use the raw-address key representation; the
/// circuit strictly parses each payload and verifies every discharge path.
#[derive(Clone, Copy, Debug)]
pub struct AggrPath<'a> {
  pub candidate: [u8; 32],
  pub bytes: &'a [u8],
}

/// Raw advice for one `ix_aggr` invocation, any shape.
///
/// Borrowed view: real proofs are multi-megabyte blobs, so constructing an
/// IO buffer must not first clone the caller's byte arrays. `proof_advice`
/// contains the expanded per-query transport, never compact proof wire bytes. Wrap shapes
/// leave the right-child slots empty; the circuit never reads them.
#[derive(Clone, Copy, Debug)]
pub struct AggrAdvice<'a> {
  pub shape: u8,
  pub proof_advice: [&'a [u8]; 2],
  pub ixvm_vk: &'a [u8],
  pub self_vk: &'a [u8],
  pub child_claims: [&'a [u8]; 2],
  pub output_claim: &'a [u8],
  pub allowed: &'a [u8],
  pub preimages: &'a [AggrPreimage<'a>],
  pub trees: &'a [AggrTree<'a>],
  pub paths: &'a [AggrPath<'a>],
}

/// Decode the compact host/FFI representation of digest-addressed
/// preimages. The wire format is a little-endian `u32` entry count followed
/// by `(32-byte key, u32 payload length, payload)` entries.
pub fn decode_aggr_preimages(
  blob: &[u8],
) -> Result<Vec<AggrPreimage<'_>>, String> {
  decode_keyed_blobs(blob, "aggr preimages").map(|entries| {
    entries
      .into_iter()
      .map(|(digest, bytes)| AggrPreimage { digest, bytes })
      .collect()
  })
}

/// Decode the compact host/FFI representation of root-addressed trees. Its
/// framing is identical to [`decode_aggr_preimages`].
pub fn decode_aggr_trees(blob: &[u8]) -> Result<Vec<AggrTree<'_>>, String> {
  decode_keyed_blobs(blob, "aggr trees").map(|entries| {
    entries.into_iter().map(|(root, bytes)| AggrTree { root, bytes }).collect()
  })
}

/// Decode compact candidate-addressed structural-discharge choices. Framing
/// is identical to [`decode_aggr_preimages`]; payload semantics are checked by
/// the circuit.
pub fn decode_aggr_paths(blob: &[u8]) -> Result<Vec<AggrPath<'_>>, String> {
  decode_keyed_blobs(blob, "aggr paths").map(|entries| {
    entries
      .into_iter()
      .map(|(candidate, bytes)| AggrPath { candidate, bytes })
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
/// Mirrors in-circuit `b3_pack` and Lean `Aggr.digestGs`.
#[inline]
fn packed_digest_key(digest: &[u8; 32]) -> Vec<G> {
  digest
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| G::from_u32(u32::from_le_bytes(*word)))
    .collect()
}

/// A 32-byte address as 32 field elements, matching the tree-loader key.
#[inline]
fn address_key(address: &[u8; 32]) -> Vec<G> {
  address.iter().map(|b| G::from_u8(*b)).collect()
}

/// Mirror of `Toplevel::execute` (same return shape, same `entry`-flag
/// gate), but routes execution through the codegen'd Rust aggregator. Deep
/// recursion is handled via per-fn `stacker::maybe_grow` checks in the
/// generated code.
// `args: Vec<G>` mirrors `Toplevel::execute`'s signature so this fn can be
// used as an `impl Fn(&Toplevel, _, Vec<G>, _) -> _` in
// `AiurSystem::prove_ixvm` — a `&[G]` here would break that bound.
#[allow(clippy::needless_pass_by_value)]
pub fn execute_ix_aggr(
  toplevel: &Toplevel,
  fun_idx: FunIdx,
  args: Vec<G>,
  io_buffer: &mut IOBuffer,
) -> Result<(QueryRecord, Vec<G>), ExecError> {
  if !toplevel.functions[fun_idx].entry {
    return Err(ExecError::NotEntryFunction(fun_idx));
  }
  let mut record = QueryRecord::new(toplevel, false);
  let output = execute_generated(fun_idx, &args, &mut record, io_buffer)?;
  Ok((record, output))
}

/// Build `ix_aggr`'s seven-channel IO advice buffer.
///
/// Layout (the circuit binds every digest-addressed blob before decoding):
///
/// * ch 0 `[0]`, `[1]`: left/right expanded child proof advice;
/// * ch 1 `[0]`, `[1]`: the IxVM and self verifying keys, by child kind;
/// * ch 2 `[0]`, `[1]`, `[2]`: child claims and the output `CheckEnv` claim;
/// * ch 3 `[0]`: the digest-bound 80-byte allowed blob;
/// * ch 4 `packed(blake3)`: `CheckEnv` claim preimages;
/// * ch 5 `root bytes`: serialized canonical assumption trees;
/// * ch 6 `[0]`: the one-byte shape hint;
/// * ch 6 `candidate bytes`: structural carried/discharged choices and paths.
pub fn aggr_io_buffer(advice: &AggrAdvice<'_>) -> IOBuffer {
  let mut io =
    IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };

  extend_bytes(&mut io, G::from_u8(0), index_key(0), advice.proof_advice[0]);
  extend_bytes(&mut io, G::from_u8(0), index_key(1), advice.proof_advice[1]);
  extend_bytes(&mut io, G::from_u8(1), index_key(0), advice.ixvm_vk);
  extend_bytes(&mut io, G::from_u8(1), index_key(1), advice.self_vk);
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
  extend_bytes(&mut io, G::from_u8(6), index_key(0), &[advice.shape]);
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
  fn aggr_layout_indexes_streams_and_uses_both_digest_key_encodings() {
    let mut digest = [0u8; 32];
    for (i, byte) in digest.iter_mut().enumerate() {
      *byte = u8::try_from(i).expect("32-byte index");
    }
    let mut root = [0u8; 32];
    for (i, byte) in root.iter_mut().enumerate() {
      *byte = u8::try_from(31 - i).expect("32-byte reverse index");
    }
    let preimages = [AggrPreimage { digest, bytes: &[11, 12] }];
    let trees = [AggrTree { root, bytes: &[13, 14, 15] }];
    let paths = [AggrPath { candidate: root, bytes: &[1, 0] }];
    let advice = AggrAdvice {
      shape: 3,
      proof_advice: [&[1, 2], &[3]],
      ixvm_vk: &[4, 5],
      self_vk: &[16, 17, 18],
      child_claims: [&[6], &[7, 8]],
      output_claim: &[9],
      allowed: &[10],
      preimages: &preimages,
      trees: &trees,
      paths: &paths,
    };

    let io = aggr_io_buffer(&advice);

    assert_eq!(arena_bytes(&io, 0), vec![1, 2, 3]);
    assert_eq!(info(&io, 0, index_key(0)), (0, 2));
    assert_eq!(info(&io, 0, index_key(1)), (2, 1));

    assert_eq!(arena_bytes(&io, 1), vec![4, 5, 16, 17, 18]);
    assert_eq!(info(&io, 1, index_key(0)), (0, 2));
    assert_eq!(info(&io, 1, index_key(1)), (2, 3));

    assert_eq!(arena_bytes(&io, 2), vec![6, 7, 8, 9]);
    assert_eq!(info(&io, 2, index_key(0)), (0, 1));
    assert_eq!(info(&io, 2, index_key(1)), (1, 2));
    assert_eq!(info(&io, 2, index_key(2)), (3, 1));

    assert_eq!(info(&io, 3, index_key(0)), (0, 1));
    assert_eq!(info(&io, 4, packed_digest_key(&digest)), (0, 2));
    assert_eq!(info(&io, 5, address_key(&root)), (0, 3));
    assert_eq!(arena_bytes(&io, 6), vec![3, 1, 0]);
    assert_eq!(info(&io, 6, index_key(0)), (0, 1));
    assert_eq!(info(&io, 6, address_key(&root)), (1, 2));
    assert_ne!(packed_digest_key(&digest), address_key(&digest));
  }

  #[test]
  fn keyed_aggr_blobs_decode_strictly_without_copying_payloads() {
    let key = [7u8; 32];
    let mut blob = Vec::new();
    blob.extend_from_slice(&1u32.to_le_bytes());
    blob.extend_from_slice(&key);
    blob.extend_from_slice(&3u32.to_le_bytes());
    blob.extend_from_slice(&[8, 9, 10]);

    let preimages = decode_aggr_preimages(&blob).expect("valid preimage blob");
    assert_eq!(preimages.len(), 1);
    assert_eq!(preimages[0].digest, key);
    assert_eq!(preimages[0].bytes, &[8, 9, 10]);

    let trees = decode_aggr_trees(&blob).expect("valid tree blob");
    assert_eq!(trees[0].root, key);
    assert_eq!(trees[0].bytes, &[8, 9, 10]);

    let paths = decode_aggr_paths(&blob).expect("valid path blob");
    assert_eq!(paths[0].candidate, key);
    assert_eq!(paths[0].bytes, &[8, 9, 10]);

    blob.push(11);
    assert!(decode_aggr_preimages(&blob).is_err());
    assert!(decode_aggr_trees(&[1, 0, 0]).is_err());
    assert!(decode_aggr_paths(&[1, 0, 0]).is_err());
  }
}
