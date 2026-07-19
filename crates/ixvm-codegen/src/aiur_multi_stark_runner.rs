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
  let mut io =
    IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };
  for (channel, bytes) in
    [(0u64, proof), (1, vk), (2, claims)].map(|(c, b)| (G::from_u64(c), b))
  {
    let data: Vec<G> = bytes.iter().map(|b| G::from_u8(*b)).collect();
    let len = data.len();
    io.data.insert(channel, data);
    io.map.insert((channel, vec![G::ZERO]), IOKeyInfo { idx: 0, len });
  }
  io
}
