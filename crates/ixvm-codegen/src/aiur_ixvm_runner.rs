//! IxVM-native execute path.
//!
//! Parallel to `aiur::execute::Toplevel::execute`, but routes the
//! Aiur fn invocation through the codegen'd Rust kernel
//! (`crate::aiur_ixvm::execute_generated`) instead of the interpreter.
//!
//! Same `QueryRecord` shape, same multiplicity rules, same memory and
//! IO side effects — so the trace produced here is byte-for-byte
//! identical to the interpreter's (modulo the `execute_generated`
//! codegen's correctness, which is the standing parity invariant).
//!
//! Caller still needs a `Toplevel` to size the `QueryRecord` correctly
//! (one `QueryMap` per function, one per `memory_sizes` entry). The
//! `Toplevel`'s bytecode is NOT walked at execution time; only its
//! shape is consulted.

use crate::aiur_ixvm::execute_generated;
use aiur::G;
use aiur::bytecode::{FunIdx, Toplevel};
use aiur::execute::{ExecError, IOBuffer, QueryRecord};

/// Mirror of `Toplevel::execute` (same return shape, same
/// `entry`-flag gate), but routes execution through the codegen'd
/// Rust kernel. Deep recursion is handled via per-fn
/// `stacker::maybe_grow` checks in the generated code — no
/// pre-reserved giant stack on this thread, no scope dance.
// `args: Vec<G>` mirrors `Toplevel::execute`'s signature so this fn
// can be used as an `impl Fn(&Toplevel, _, Vec<G>, _) -> _` in
// `AiurSystem::prove_ixvm` — a `&[G]` here would break that bound.
#[allow(clippy::needless_pass_by_value)]
pub fn execute_ixvm(
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
