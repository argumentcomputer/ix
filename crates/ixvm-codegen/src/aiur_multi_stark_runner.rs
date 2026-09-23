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
/// the layout of `MultiStark.verifierInput` (`MultiStark.lean`).
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
}
