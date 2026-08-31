use multi_stark::{
  p3_field::PrimeField64,
  types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::sync::LazyLock;

use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExcept,
  LeanExternal, LeanNat, LeanOwned, LeanProd, LeanRef, LeanString,
};

use crate::{
  aiur::{lean_unbox_g, lean_unbox_nat_as_usize, toplevel::decode_toplevel},
  lean::{
    LeanAiurCircuitShape, LeanAiurCommitmentParameters, LeanAiurExecuteResult,
    LeanAiurFriParameters, LeanAiurIOKeyInfo, LeanAiurProveEnvResult,
    LeanAiurProveResult, LeanAiurQueryCount, LeanAiurToplevel,
  },
};
use aiur::{
  G,
  execute::{IOBuffer, IOKeyInfo, QueryRecord},
  synthesis::{AiurProof, AiurSystem, CircuitShape},
};

// =============================================================================
// External class registration
// =============================================================================

static AIUR_PROOF_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<AiurProof>);
static AIUR_SYSTEM_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<AiurSystem>);
static IX_ENV_HANDLE_CLASS: LazyLock<ExternalClass> = LazyLock::new(
  ExternalClass::register_with_drop::<ixvm_codegen::env_handle::EnvHandle>,
);

// =============================================================================
// Lean FFI functions
// =============================================================================

/// `Aiur.Proof.toBytes : @& Proof → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_bytes(
  proof_obj: LeanExternal<AiurProof, LeanBorrowed<'_>>,
) -> LeanByteArray<LeanOwned> {
  let bytes = proof_obj.get().to_bytes().expect("Serialization error");
  LeanByteArray::from_bytes(&bytes)
}

/// `Aiur.Proof.ofBytes : @& ByteArray → Proof`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_of_bytes(
  byte_array: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<AiurProof, LeanOwned> {
  let proof = AiurProof::from_bytes(byte_array.as_bytes())
    .expect("Deserialization error");
  LeanExternal::alloc(&AIUR_PROOF_CLASS, proof)
}

/// `Aiur.Proof.ofBytesChecked : @& ByteArray → Except String Proof`
///
/// Unlike the legacy trusted-byte constructor above, this is safe at cache and
/// network boundaries: malformed bytes become a Lean error instead of a Rust
/// panic that aborts the process.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_of_bytes_checked(
  byte_array: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  match AiurProof::from_bytes(byte_array.as_bytes()) {
    Ok(proof) => {
      let lean_proof: LeanOwned =
        LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
      LeanExcept::ok(lean_proof)
    },
    Err(err) => {
      LeanExcept::error_string(&format!("proof deserialization failed: {err}"))
    },
  }
}

/// `Aiur.AiurSystem.vkBytes : @& AiurSystem → ByteArray`
///
/// Serializes the verifying key (`System<AiurCircuit>`) — see
/// `aiur::vk_codec`.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_vk_bytes(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
) -> LeanByteArray<LeanOwned> {
  let bytes = aiur::vk_codec::aiur_system_to_bytes(system.get())
    .expect("VK serialization error");
  LeanByteArray::from_bytes(&bytes)
}

/// `AiurSystem.build : @&Bytecode.Toplevel → @&CommitmentParameters → @&FriParameters → AiurSystem`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_build(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  commitment_parameters: LeanAiurCommitmentParameters<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
) -> LeanExternal<AiurSystem, LeanOwned> {
  let system = AiurSystem::build(
    decode_toplevel(&toplevel),
    decode_commitment_parameters(&commitment_parameters),
    decode_fri_parameters(&fri_parameters),
  );
  LeanExternal::alloc(&AIUR_SYSTEM_CLASS, system)
}

/// Helper: encode `CircuitShape`s as a Lean `Array CircuitShape`. Field
/// order must match `Aiur.CircuitShape` in `Ix/Aiur/Protocol.lean`.
fn build_circuit_shapes_array(shapes: &[CircuitShape]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(shapes.len());
  for (i, shape) in shapes.iter().enumerate() {
    let s = LeanAiurCircuitShape::alloc(0);
    s.set_obj(0, LeanOwned::box_usize(shape.main_width));
    s.set_obj(1, LeanOwned::box_usize(shape.stage2_width));
    s.set_obj(2, LeanOwned::box_usize(shape.quotient_degree));
    s.set_obj(3, LeanOwned::box_usize(shape.preprocessed_width));
    s.set_obj(4, LeanOwned::box_usize(shape.preprocessed_height));
    arr.set(i, s);
  }
  arr
}

/// `AiurSystem.circuitShapes : @& AiurSystem → Array CircuitShape`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_circuit_shapes(
  system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
) -> LeanArray<LeanOwned> {
  build_circuit_shapes_array(&system.get().circuit_shapes())
}

/// `Aiur.circuitShapes : @&Bytecode.Toplevel → @&CommitmentParameters → @&FriParameters → Array CircuitShape`
///
/// One-shot variant for flows that never build an `AiurSystem` (`ix check`
/// statistics): builds the system, extracts the shapes, and drops it.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_circuit_shapes(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  commitment_parameters: LeanAiurCommitmentParameters<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
) -> LeanArray<LeanOwned> {
  let system = AiurSystem::build(
    decode_toplevel(&toplevel),
    decode_commitment_parameters(&commitment_parameters),
    decode_fri_parameters(&fri_parameters),
  );
  build_circuit_shapes_array(&system.circuit_shapes())
}

/// `AiurSystem.verify : @& AiurSystem → @& Array G → @& Proof → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_verify(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  proof_obj: LeanExternal<AiurProof, LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let claim = claim.map(|x| lean_unbox_g(&x));
  match aiur_system_obj.get().verify(&claim, proof_obj.get()) {
    Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
    Err(err) => LeanExcept::error_string(&format!("{err:?}")),
  }
}

/// `AiurSystem.proofToAdviceBytes : @& AiurSystem → @& Array G → @& Proof → Except String ByteArray`
///
/// The proof re-encoded in the per-query advice transport the in-circuit
/// verifier consumes (pruned FRI multiproofs expanded to one path per
/// query); errors if the proof does not verify natively.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_advice_bytes(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  proof_obj: LeanExternal<AiurProof, LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let claim = claim.map(|x| lean_unbox_g(&x));
  match aiur_system_obj.get().proof_to_advice_bytes(&claim, proof_obj.get()) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&format!("{err:?}")),
  }
}

/// `Bytecode.Toplevel.execute`: runs execution only (no proof) and returns
/// `Except String ExecuteResult` (see `Ix/Aiur/Semantics/BytecodeFfi.lean`).
/// On execution failure (e.g. assertion mismatch from a typechecker
/// rejecting a constant), returns `Except.error msg` instead of panicking
/// — letting Lean test runners (`KernelArena.lean`) classify failures.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_execute(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (query_record, output) = match toplevel.execute(
    fun_idx,
    args.map(|x| lean_unbox_g(&x)),
    &mut io_buffer,
  ) {
    Ok(pair) => pair,
    Err(err) => return LeanExcept::error_string(&err.to_string()),
  };

  LeanExcept::ok(build_execute_result(
    &output,
    &io_buffer,
    &query_record,
    &toplevel,
  ))
}

/// `Bytecode.Toplevel.executeIxVM`: same shape as `rs_aiur_toplevel_execute`,
/// but routes execution through the codegen'd IxVM Rust kernel
/// (`ixvm_codegen::aiur_ixvm::execute_generated`) via the helper in
/// `ixvm_codegen::aiur_ixvm_runner::execute_ixvm`. The resulting
/// `QueryRecord` is byte-for-byte identical to the interpreter's
/// (modulo standing codegen parity invariant).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_execute_ixvm(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  // Same execution-phase span as `dispatch_execute`/the prove pipeline.
  let _g = tracing::info_span!("aiur/execute_ixvm").entered();
  let (query_record, output) =
    match ixvm_codegen::aiur_ixvm_runner::execute_ixvm(
      &toplevel,
      fun_idx,
      args.map(|x| lean_unbox_g(&x)),
      &mut io_buffer,
    ) {
      Ok(pair) => pair,
      Err(err) => return LeanExcept::error_string(&err.to_string()),
    };

  LeanExcept::ok(build_execute_result(
    &output,
    &io_buffer,
    &query_record,
    &toplevel,
  ))
}

/// `AiurSystem.prove`: runs the prover and returns a `ProveResult`
/// (see `Ix/Aiur/Protocol.lean`).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind("AiurSystem.prove", || {
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let args = args.map(|x| lean_unbox_g(&x));
    let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

    let (claim, proof) =
      aiur_system_obj.get().prove(fun_idx, &args, &mut io_buffer);

    build_prove_result(&claim, proof, &io_buffer).into()
  })
}

// =============================================================================
// EnvHandle constructors + with-env FFIs: the env is parsed once per CLI
// invocation into an opaque Rust-owned handle, and every per-target call
// borrows it, so no call re-parses the environment.
// =============================================================================

/// `Aiur.EnvHandle.fromIxe`: open and parse a `.ixe` file once,
/// return an opaque Rust-owned handle. The mmap stays alive inside
/// the handle (via per-constant `Arc<Mmap>` windows) for as long as
/// Lean retains the `LeanExternal<EnvHandle>` reference.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_env_handle_from_ixe(
  path_bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let path_str = String::from_utf8_lossy(path_bytes.as_bytes()).into_owned();
  match ixvm_codegen::env_handle::EnvHandle::from_ixe_path(
    std::path::Path::new(&path_str),
  ) {
    Ok(h) => {
      let lean_handle: LeanOwned =
        LeanExternal::alloc(&IX_ENV_HANDLE_CLASS, h).into();
      LeanExcept::ok(lean_handle)
    },
    Err(e) => LeanExcept::error_string(&format!("env handle from_ixe: {e}")),
  }
}

/// `Aiur.EnvHandle.fromBytes`: decode a serialized env blob
/// (`Ixon.serEnv` output) and harvest `anon_hints` post-decode.
/// Used by the compiled-Lean-env path (`ix check NAME` without
/// `--ixe`).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_env_handle_from_bytes(
  bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  match ixvm_codegen::env_handle::EnvHandle::from_bytes(bytes.as_bytes()) {
    Ok(h) => {
      let lean_handle: LeanOwned =
        LeanExternal::alloc(&IX_ENV_HANDLE_CLASS, h).into();
      LeanExcept::ok(lean_handle)
    },
    Err(e) => LeanExcept::error_string(&format!("env handle from_bytes: {e}")),
  }
}

/// Helper: summarise one execute's `QueryRecord` into a Lean
/// `Array QueryCount` of `(uniqueRows, totalHits)` structures, one per
/// function circuit followed by one per memory size. Used by every
/// check/prove FFI.
fn build_query_counts_array(
  query_record: &QueryRecord,
  toplevel: &aiur::bytecode::Toplevel,
) -> LeanArray<LeanOwned> {
  let mut query_counts: Vec<(usize, usize)> = Vec::with_capacity(
    query_record.function_queries.len() + toplevel.memory_sizes.len(),
  );
  let summarize = |q: &aiur::querymap::QueryMap| -> (usize, usize) {
    let mut rows = 0usize;
    let mut hits = 0usize;
    for (_, res) in q.iter() {
      let m = usize::try_from(res.multiplicity.as_canonical_u64())
        .expect("multiplicity exceeds usize");
      if m != 0 {
        rows += 1;
        hits += m;
      }
    }
    (rows, hits)
  };
  for queries in &query_record.function_queries {
    query_counts.push(summarize(queries));
  }
  for size in &toplevel.memory_sizes {
    let pair = query_record.memory_queries.get(size).map_or((0, 0), summarize);
    query_counts.push(pair);
  }
  let arr = LeanArray::alloc(query_counts.len());
  for (i, &(rows, hits)) in query_counts.iter().enumerate() {
    let qc = LeanAiurQueryCount::alloc(0);
    qc.set_obj(0, LeanOwned::box_usize(rows));
    qc.set_obj(1, LeanOwned::box_usize(hits));
    arr.set(i, qc);
  }
  arr
}

/// Helper: build a Lean `ExecuteResult` (output, ioData, ioMap,
/// queryCounts) — the return shape shared by every execute/check FFI.
fn build_execute_result(
  output: &[G],
  io_buffer: &IOBuffer,
  query_record: &QueryRecord,
  toplevel: &aiur::bytecode::Toplevel,
) -> LeanAiurExecuteResult<LeanOwned> {
  let result = LeanAiurExecuteResult::alloc(0);
  result.set_obj(0, build_g_array(output));
  result.set_obj(1, build_lean_io_data(io_buffer));
  result.set_obj(2, build_lean_io_map(io_buffer));
  result.set_obj(3, build_query_counts_array(query_record, toplevel));
  result
}

/// Helper: build a Lean `ProveResult` (claim, proof, ioData, ioMap).
fn build_prove_result(
  claim: &[G],
  proof: AiurProof,
  io_buffer: &IOBuffer,
) -> LeanAiurProveResult<LeanOwned> {
  let result = LeanAiurProveResult::alloc(0);
  result.set_obj(0, build_g_array(claim));
  result.set_obj(1, LeanExternal::alloc(&AIUR_PROOF_CLASS, proof));
  result.set_obj(2, build_lean_io_data(io_buffer));
  result.set_obj(3, build_lean_io_map(io_buffer));
  result
}

/// Helper: build a Lean `ProveEnvResult` (claimBytes, proof, ioData,
/// ioMap) — the claim's wire bytes are serialized via
/// `ixon::Claim::put` so Lean can deserialize directly.
fn build_prove_env_result(
  claim: &ixon::proof::Claim,
  proof: AiurProof,
  io_buffer: &IOBuffer,
) -> LeanAiurProveEnvResult<LeanOwned> {
  let mut claim_bytes: Vec<u8> = Vec::new();
  claim.put(&mut claim_bytes);
  let result = LeanAiurProveEnvResult::alloc(0);
  result.set_obj(0, LeanByteArray::from_bytes(&claim_bytes));
  result.set_obj(1, LeanExternal::alloc(&AIUR_PROOF_CLASS, proof));
  result.set_obj(2, build_lean_io_data(io_buffer));
  result.set_obj(3, build_lean_io_map(io_buffer));
  result
}

/// Helper: decode a 32-byte address from a `LeanByteArray`.
fn decode_addr(
  addr_bytes: &LeanByteArray<LeanBorrowed<'_>>,
) -> Result<ix_common::address::Address, String> {
  let slice = addr_bytes.as_bytes();
  if slice.len() != 32 {
    return Err(format!(
      "addr_bytes: expected 32-byte address, got {} bytes",
      slice.len()
    ));
  }
  Ok(
    ix_common::address::Address::from_slice(slice)
      .expect("32-byte slice already length-checked"),
  )
}

/// Helper: decode a flat 32-byte-block owned blob into `Vec<Address>`.
fn decode_owned_blob(
  owned_blob: &LeanByteArray<LeanBorrowed<'_>>,
) -> Result<Vec<ix_common::address::Address>, String> {
  let bytes = owned_blob.as_bytes();
  if !bytes.len().is_multiple_of(32) {
    return Err(format!(
      "owned_blob: length {} not a multiple of 32",
      bytes.len()
    ));
  }
  Ok(
    bytes
      .as_chunks::<32>()
      .0
      .iter()
      .map(|c| ix_common::address::Address::from_slice(c).unwrap())
      .collect(),
  )
}

/// Run `fun_idx` with `input` + `io_buffer`, routing through either
/// the codegen'd IxVM kernel (`use_bytecode = false`) or the
/// generic Aiur bytecode interpreter (`use_bytecode = true`).
/// The bytecode interpreter doesn't require regenerating the
/// codegen'd Rust kernel after Lean-side IxVM source changes —
/// useful for tight iteration loops on `Ix/IxVM/*.lean`.
#[inline]
fn dispatch_execute(
  toplevel: &aiur::bytecode::Toplevel,
  fun_idx: aiur::bytecode::FunIdx,
  input: Vec<G>,
  io_buffer: &mut IOBuffer,
  use_bytecode: bool,
) -> Result<(QueryRecord, Vec<G>), String> {
  // Same span name as the prove pipeline's execution phase
  // (`synthesis.rs`), so a standalone execute renders/records through the
  // one texray channel — timing and RAM come from the subscriber, not
  // per-benchmark arithmetic.
  let _g = tracing::info_span!("aiur/execute_ixvm").entered();
  if use_bytecode {
    toplevel
      .execute(fun_idx, input, io_buffer)
      .map_err(|e| format!("execute (bytecode): {e}"))
  } else {
    ixvm_codegen::aiur_ixvm_runner::execute_ixvm(
      toplevel, fun_idx, input, io_buffer,
    )
    .map_err(|e| format!("execute_ixvm: {e}"))
  }
}

/// `Bytecode.Toplevel.checkAddrWithEnv`: per-claim check against a
/// Rust-owned `EnvHandle`. `use_bytecode` selects the executor:
/// `false` = codegen'd IxVM kernel (`execute_ixvm`),
/// `true`  = generic Aiur bytecode interpreter
/// (`Toplevel::execute`).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_check_addr_with_env(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  addr_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let addr = match decode_addr(&addr_bytes) {
    Ok(a) => a,
    Err(e) => return LeanExcept::error_string(&e),
  };
  let env = &env_handle.get().env;

  let (_claim, input, mut io_buffer) =
    match ixvm_codegen::aiur_ixvm_witness::build_claim_check_witness(env, &addr)
    {
      Ok(t) => t,
      Err(e) => {
        return LeanExcept::error_string(&format!("witness build: {e}"));
      },
    };

  let (query_record, output) = match dispatch_execute(
    &toplevel,
    fun_idx,
    input,
    &mut io_buffer,
    use_bytecode,
  ) {
    Ok(p) => p,
    Err(e) => return LeanExcept::error_string(&e),
  };

  LeanExcept::ok(build_execute_result(
    &output,
    &io_buffer,
    &query_record,
    &toplevel,
  ))
}

/// `Bytecode.Toplevel.checkAddrsWithEnv`: check a BATCH of full-closure
/// claims (`Claim.check addr none`, one per address in `addrs_blob`) in
/// PARALLEL — rayon over the list, each task running exactly the
/// single-claim machinery above (`build_claim_check_witness` +
/// `dispatch_execute`) over entirely task-private data: its own
/// `IOBuffer`, its own `QueryRecord`, both dropped inside the task.
/// Parallel, not concurrent: nothing is shared between tasks except
/// the read-only `toplevel` and `env` (the compiler enforces this —
/// `par_iter` closures only capture `Sync` data). Each claim's record
/// is single-threaded and therefore bit-deterministic regardless of
/// `jobs` or scheduling. Peak RAM is bounded by `jobs` concurrent
/// claim cones (rayon keeps at most one in-flight task per pool
/// thread; records free at task end).
///
/// Returns the FAILURES as an array of `(batch index, error)` pairs
/// (the index as a decimal string, resolving back to the caller's
/// label order) —
/// empty means every claim passed. Per-claim outputs and records are
/// deliberately not round-tripped to Lean; the single-claim entry
/// keeps the full result shape for that. `jobs = 0` uses rayon's
/// default pool width.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_check_addrs_with_env(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  addrs_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
  jobs: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use rayon::prelude::*;
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let jobs = lean_unbox_nat_as_usize(jobs.inner());
  let addrs = match decode_owned_blob(&addrs_blob) {
    Ok(v) => v,
    Err(e) => return LeanExcept::error_string(&e),
  };
  let env = &env_handle.get().env;
  let check_batch = || -> Vec<(String, String)> {
    addrs
      .par_iter()
      .enumerate()
      .filter_map(|(i, addr)| {
        let err =
          match ixvm_codegen::aiur_ixvm_witness::build_claim_check_witness(
            env, addr,
          ) {
            Err(e) => Some(format!("witness build: {e}")),
            Ok((_claim, input, mut io_buffer)) => dispatch_execute(
              &toplevel,
              fun_idx,
              input,
              &mut io_buffer,
              use_bytecode,
            )
            .err(),
          };
        err.map(|e| (i.to_string(), e))
      })
      .collect()
  };
  let failures = if jobs == 0 {
    check_batch()
  } else {
    let pool = match rayon::ThreadPoolBuilder::new().num_threads(jobs).build() {
      Ok(p) => p,
      Err(e) => {
        return LeanExcept::error_string(&format!("rayon pool: {e}"));
      },
    };
    pool.install(check_batch)
  };
  let arr = LeanArray::alloc(failures.len());
  for (i, (idx, err)) in failures.iter().enumerate() {
    arr.set(i, LeanProd::new(LeanString::new(idx), LeanString::new(err)));
  }
  LeanExcept::ok(arr)
}

/// Byte-weighted admission gate: a counting semaphore over estimated
/// execution RSS, expressed with the std Mutex+Condvar construction.
/// Bounds MEMORY in flight instead of shards in flight, so the rayon
/// pool can run at full width: cheap shards run many-wide while a
/// heavy one takes a proportional slice of the budget. Workers block
/// in `acquire` until reserving their estimate fits the budget.
struct RamGate {
  reserved: std::sync::Mutex<usize>,
  cv: std::sync::Condvar,
  budget: usize,
}

impl RamGate {
  fn acquire(&self, bytes: usize) {
    let mut used = self.reserved.lock().unwrap();
    // Admit-when-alone: a shard whose estimate alone exceeds the
    // budget must still run (by itself) rather than deadlock.
    while *used > 0 && *used + bytes > self.budget {
      used = self.cv.wait(used).unwrap();
    }
    *used += bytes;
  }

  fn release(&self, bytes: usize) {
    *self.reserved.lock().unwrap() -= bytes;
    self.cv.notify_all();
  }
}

/// Per-shard execution-RSS reserve for [`RamGate`], an AFFINE model:
/// `EXEC_RSS_FIXED_BYTES + EXEC_RSS_PER_OWNED_BYTE x owned bytes`. The
/// byte basis is the sum of the shard's owned constants' raw
/// serialized bytes (`Env::get_const_bytes`) — NOT the shard's share
/// of `.ixe` FILE bytes, which also carry blobs, names, and indices
/// and run ~2.6x larger. The fixed term is the closure/frontier
/// ingress every shard pays regardless of owned size; without it a
/// pure ratio calibrated on large shards under-reserves small ones
/// (measured: 151 ISLB shards at 1.1-4.8 GiB estimated ran to 175 GB
/// actual against a 110 GiB budget — an OOM on a real 128 GB box).
/// Fit on the two ISLB partitions (2026-08-22, measured in-flight
/// RSS): 5.7 MB owned -> ~9.6 GB and 1.4 MB -> ~5.5 GB, giving
/// ~4 GiB + ~1000x; both terms rounded up for cross-shard spread.
const EXEC_RSS_FIXED_BYTES: usize = 9 * (1 << 29); // 4.5 GiB
const EXEC_RSS_PER_OWNED_BYTE: usize = 1100;

/// `MemAvailable` from `/proc/meminfo`, in bytes (Linux; includes
/// reclaimable page cache). `None` if unreadable — the caller then
/// disables the gate rather than guessing.
fn available_ram_bytes() -> Option<usize> {
  let s = std::fs::read_to_string("/proc/meminfo").ok()?;
  let rest = s.lines().find_map(|l| l.strip_prefix("MemAvailable:"))?;
  let kib: usize = rest.trim().trim_end_matches("kB").trim().parse().ok()?;
  Some(kib * 1024)
}

/// `Bytecode.Toplevel.shardCheckBatchWithEnv`: check EVERY shard of a
/// partition in one call — rayon over the shard list with true
/// work-stealing (no chunk barriers), each shard through the exact
/// single-shard machinery (`build_shard_check_env_witness` +
/// `dispatch_execute`) over its own private record and witness io.
/// Parallel, not concurrent: tasks share only the read-only toplevel,
/// env, and the `AiurSystem` built once here for the prover RAM model.
///
/// `shards_blob` encodes the partition as, per shard, a 4-byte LE
/// owned-constant count followed by that many 32-byte addresses.
/// Returns one `(error, peak_bytes)` pair PER SHARD in shard order:
/// an empty error string means the shard checked clean, and
/// `peak_bytes` is the analytic prover peak
/// ([`aiur::synthesis::AiurSystem::peak_prove_bytes`]) of its executed
/// record — the number split/merge decisions compare against a prover
/// budget (0 when the shard failed). `jobs = 0` uses rayon's default
/// pool width (all cores) — safe at full width because admission is
/// bounded by [`RamGate`], not by thread count; pass `jobs` only to
/// narrow CPU use.
// cast_precision_loss: the [ram-gate] line renders byte counts in GiB
// for humans; f64's 52-bit mantissa is exact far past any real budget.
#[allow(clippy::cast_precision_loss)]
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_shard_check_batch(
  toplevel_obj: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  shards_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
  jobs: LeanNat<LeanBorrowed<'_>>,
  commitment_parameters: LeanAiurCommitmentParameters<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use rayon::prelude::*;
  let toplevel = decode_toplevel(&toplevel_obj);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let jobs = lean_unbox_nat_as_usize(jobs.inner());
  let mut shards: Vec<Vec<ix_common::address::Address>> = Vec::new();
  {
    let bytes = shards_blob.as_bytes();
    let mut off = 0usize;
    while off < bytes.len() {
      if off + 4 > bytes.len() {
        return LeanExcept::error_string("shards_blob: truncated count");
      }
      let n =
        u32::from_le_bytes(bytes[off..off + 4].try_into().unwrap()) as usize;
      off += 4;
      if off + n * 32 > bytes.len() {
        return LeanExcept::error_string("shards_blob: truncated addresses");
      }
      shards.push(
        bytes[off..off + n * 32]
          .as_chunks::<32>()
          .0
          .iter()
          .map(|c| ix_common::address::Address::from_slice(c).unwrap())
          .collect(),
      );
      off += n * 32;
    }
  }
  let env = &env_handle.get().env;
  // One system build for the whole batch: the RAM model reads circuit
  // widths and lookup counts off the compiled circuits.
  let system = AiurSystem::build(
    decode_toplevel(&toplevel_obj),
    decode_commitment_parameters(&commitment_parameters),
    decode_fri_parameters(&fri_parameters),
  );
  // RAM-gated admission: reserve each shard's estimated execution RSS
  // (fixed ingress cost + owned serialized bytes x measured slope)
  // against most of the RAM available at entry. Memory in flight —
  // not `jobs` — is what bounds peak RSS; an unreadable meminfo
  // disables the gate.
  let estimates: Vec<usize> = shards
    .iter()
    .map(|owned| {
      EXEC_RSS_FIXED_BYTES.saturating_add(
        owned
          .iter()
          .filter_map(|a| env.get_const_bytes(a).map(|b| b.len()))
          .sum::<usize>()
          .saturating_mul(EXEC_RSS_PER_OWNED_BYTE),
      )
    })
    .collect();
  let gate = RamGate {
    reserved: std::sync::Mutex::new(0),
    cv: std::sync::Condvar::new(),
    budget: available_ram_bytes().map_or(usize::MAX, |b| b / 100 * 85),
  };
  {
    let gib = 1024.0 * 1024.0 * 1024.0;
    let min = estimates.iter().min().copied().unwrap_or(0);
    let max = estimates.iter().max().copied().unwrap_or(0);
    eprintln!(
      "[ram-gate] budget {:.1} GiB, {} shard estimates: min {:.1} / max {:.1} GiB",
      gate.budget as f64 / gib,
      estimates.len(),
      min as f64 / gib,
      max as f64 / gib,
    );
  }
  let check_batch = || -> Vec<(String, usize)> {
    shards
      .par_iter()
      .zip(estimates.par_iter())
      .map(|(owned, est)| {
        gate.acquire(*est);
        let result =
          match ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness(
            env, owned,
          ) {
            Err(e) => (format!("witness build: {e}"), 0),
            Ok((_claim, input, mut io_buffer)) => match dispatch_execute(
              &toplevel,
              fun_idx,
              input,
              &mut io_buffer,
              use_bytecode,
            ) {
              Err(e) => (e, 0),
              Ok((record, _output)) => {
                (String::new(), system.peak_prove_bytes(&record).peak)
              },
            },
          };
        gate.release(*est);
        result
      })
      .collect()
  };
  let results = if jobs == 0 {
    check_batch()
  } else {
    let pool = match rayon::ThreadPoolBuilder::new().num_threads(jobs).build() {
      Ok(p) => p,
      Err(e) => {
        return LeanExcept::error_string(&format!("rayon pool: {e}"));
      },
    };
    pool.install(check_batch)
  };
  let arr = LeanArray::alloc(results.len());
  for (i, (err, peak)) in results.iter().enumerate() {
    arr
      .set(i, LeanProd::new(LeanString::new(err), LeanOwned::box_usize(*peak)));
  }
  LeanExcept::ok(arr)
}

/// `Bytecode.Toplevel.shardCheckWithEnv`: per-shard check against a
/// Rust-owned `EnvHandle`. See `checkAddrWithEnv` for `use_bytecode`
/// semantics.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_shard_check_with_env(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  owned_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let owned = match decode_owned_blob(&owned_blob) {
    Ok(v) => v,
    Err(e) => return LeanExcept::error_string(&e),
  };
  let env = &env_handle.get().env;

  // Migration Phase 1: the generated kernel is the kernel, so the default
  // shard entrypoint builds the the kernel witness (thin frontier + wrapper
  // augmentation).
  let (_claim, input, mut io_buffer) =
    match ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness(
      env, &owned,
    ) {
      Ok(t) => t,
      Err(e) => {
        return LeanExcept::error_string(&format!("witness build: {e}"));
      },
    };

  let (query_record, output) = match dispatch_execute(
    &toplevel,
    fun_idx,
    input,
    &mut io_buffer,
    use_bytecode,
  ) {
    Ok(p) => p,
    Err(e) => return LeanExcept::error_string(&e),
  };

  LeanExcept::ok(build_execute_result(
    &output,
    &io_buffer,
    &query_record,
    &toplevel,
  ))
}

/// `AiurSystem.proveAddrWithEnv`: per-claim prove against a
/// Rust-owned `EnvHandle`. Returns a `ProveEnvResult` — the claim's
/// wire bytes are serialized via `ixon::Claim::put` so Lean can
/// deserialize directly into `Ix.Claim` without reconstructing it
/// from the target addr.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove_addr_with_env(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  addr_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("AiurSystem.proveAddrWithEnv", || {
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let addr = match decode_addr(&addr_bytes) {
      Ok(a) => a,
      Err(e) => return LeanExcept::error_string(&e),
    };
    let env = &env_handle.get().env;

    let (claim, input, mut io_buffer) =
      match ixvm_codegen::aiur_ixvm_witness::build_claim_check_witness(
        env, &addr,
      ) {
        Ok(t) => t,
        Err(e) => {
          return LeanExcept::error_string(&format!("witness build: {e}"));
        },
      };

    // `use_bytecode` selects the generic Aiur bytecode interpreter over the
    // codegen'd IxVM kernel (same toggle as
    // `rs_aiur_toplevel_check_addr_with_env`).
    let (_aiur_claim_arr, proof) = if use_bytecode {
      aiur_system_obj.get().prove_ixvm(
        fun_idx,
        &input,
        &mut io_buffer,
        |toplevel, fun_idx, input, io_buffer| {
          toplevel.execute(fun_idx, input, io_buffer)
        },
      )
    } else {
      aiur_system_obj.get().prove_ixvm(
        fun_idx,
        &input,
        &mut io_buffer,
        ixvm_codegen::aiur_ixvm_runner::execute_ixvm,
      )
    };

    LeanExcept::ok(build_prove_env_result(&claim, proof, &io_buffer))
  })
}

/// `AiurSystem.shardProveWithEnv`: per-shard prove against a
/// Rust-owned `EnvHandle`. Same `ProveEnvResult` return shape as
/// `proveAddrWithEnv`.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_shard_prove_with_env(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  owned_blob: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("AiurSystem.shardProveWithEnv", || {
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let owned = match decode_owned_blob(&owned_blob) {
      Ok(v) => v,
      Err(e) => return LeanExcept::error_string(&e),
    };
    let env = &env_handle.get().env;

    let (claim, input, mut io_buffer) =
      match ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness(
        env, &owned,
      ) {
        Ok(t) => t,
        Err(e) => {
          return LeanExcept::error_string(&format!("witness build: {e}"));
        },
      };

    let (_aiur_claim_arr, proof) = aiur_system_obj.get().prove_ixvm(
      fun_idx,
      &input,
      &mut io_buffer,
      ixvm_codegen::aiur_ixvm_runner::execute_ixvm,
    );

    LeanExcept::ok(build_prove_env_result(&claim, proof, &io_buffer))
  })
}

/// `AiurSystem.proveIxVM`: IxVM-native prove path. Same return shape
/// as `rs_aiur_system_prove`, but routes execution through the
/// codegen'd Rust kernel (`execute_generated`) via
/// `AiurSystem::prove_ixvm`. The resulting `Proof` is verification-
/// compatible with `rs_aiur_system_prove`.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove_ixvm(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind("AiurSystem.proveIxVM", || {
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let args = args.map(|x| lean_unbox_g(&x));
    let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

    let (claim, proof) = aiur_system_obj.get().prove_ixvm(
      fun_idx,
      &args,
      &mut io_buffer,
      ixvm_codegen::aiur_ixvm_runner::execute_ixvm,
    );

    build_prove_result(&claim, proof, &io_buffer).into()
  })
}

/// `Bytecode.Toplevel.executeMultiStark`: run the MultiStark recursive
/// verifier over proof-advice/vk/claims byte blobs. The proof blob is the
/// expanded per-query transport produced by `proof_to_advice_bytes`, not the
/// compact persisted `Proof::to_bytes` representation. The IO advice buffer
/// (channel 0 = proof, 1 = vk, 2 = claims, key `[0]` each) is built
/// natively via `verifier_io_buffer` — no per-byte Lean boxing, no
/// buffer marshalling across FFI. `use_bytecode` selects the executor:
/// `false` = codegen'd verifier (`execute_multi_stark`),
/// `true`  = generic Aiur bytecode interpreter.
/// Returns `(output, query_counts)`; the final buffer is not returned
/// (the verifier only reads its advice).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_multi_stark_execute(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  pub_input: LeanArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = ixvm_codegen::aiur_multi_stark_runner::verifier_io_buffer(
    proof_bytes.as_bytes(),
    vk_bytes.as_bytes(),
    claims_bytes.as_bytes(),
  );
  let input = pub_input.map(|x| lean_unbox_g(&x));

  // Same execution-phase span as the prove pipeline.
  let _g = tracing::info_span!("aiur/execute_multi_stark").entered();
  let result = if use_bytecode {
    toplevel.execute(fun_idx, input, &mut io_buffer)
  } else {
    ixvm_codegen::aiur_multi_stark_runner::execute_multi_stark(
      &toplevel,
      fun_idx,
      input,
      &mut io_buffer,
    )
  };
  let (query_record, output) = match result {
    Ok(pair) => pair,
    Err(err) => return LeanExcept::error_string(&err.to_string()),
  };

  let lean_query_counts = build_query_counts_array(&query_record, &toplevel);
  // (Array G, Array (Nat × Nat))
  let result = LeanProd::new(build_g_array(&output), lean_query_counts);
  LeanExcept::ok(result)
}

#[allow(clippy::too_many_arguments)]
fn build_multi_stark_join_io_buffer(
  left_proof: &[u8],
  right_proof: &[u8],
  recursion_vk: &[u8],
  left_claims: &[u8],
  right_claims: &[u8],
  output_claim: &[u8],
  allowed: &[u8],
  preimages_blob: &[u8],
  trees_blob: &[u8],
  paths_blob: &[u8],
) -> Result<IOBuffer, String> {
  use ixvm_codegen::aiur_multi_stark_runner::{
    JoinAdvice, decode_join_paths, decode_join_preimages, decode_join_trees,
    join_io_buffer,
  };

  let preimages = decode_join_preimages(preimages_blob)?;
  let trees = decode_join_trees(trees_blob)?;
  let paths = decode_join_paths(paths_blob)?;
  Ok(join_io_buffer(&JoinAdvice {
    proofs: [left_proof, right_proof],
    recursion_vk,
    child_claims: [left_claims, right_claims],
    output_claim,
    allowed,
    preimages: &preimages,
    trees: &trees,
    paths: &paths,
  }))
}

/// `Bytecode.Toplevel.executeMultiStarkJoin`: execute either join entrypoint over
/// child proof-advice/claim/tree/path blobs. Each proof is expanded with
/// `proof_to_advice_bytes` before crossing this boundary. The native builder expands the compact keyed
/// framing directly into the circuit's seven-channel IO buffer.
/// As with `rs_aiur_multi_stark_execute`, callers may select either generated
/// execution or the generic bytecode interpreter.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
extern "C" fn rs_aiur_multi_stark_join_execute(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  pub_input: LeanArray<LeanBorrowed<'_>>,
  left_proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  recursion_vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  left_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  output_claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  allowed_bytes: LeanByteArray<LeanBorrowed<'_>>,
  preimages_blob: LeanByteArray<LeanBorrowed<'_>>,
  trees_blob: LeanByteArray<LeanBorrowed<'_>>,
  paths_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = match build_multi_stark_join_io_buffer(
    left_proof_bytes.as_bytes(),
    right_proof_bytes.as_bytes(),
    recursion_vk_bytes.as_bytes(),
    left_claims_bytes.as_bytes(),
    right_claims_bytes.as_bytes(),
    output_claim_bytes.as_bytes(),
    allowed_bytes.as_bytes(),
    preimages_blob.as_bytes(),
    trees_blob.as_bytes(),
    paths_blob.as_bytes(),
  ) {
    Ok(io) => io,
    Err(err) => return LeanExcept::error_string(&err),
  };
  let input = pub_input.map(|x| lean_unbox_g(&x));

  let _g = tracing::info_span!("aiur/execute_multi_stark_join").entered();
  let result = if use_bytecode {
    toplevel.execute(fun_idx, input, &mut io_buffer)
  } else {
    ixvm_codegen::aiur_multi_stark_runner::execute_multi_stark(
      &toplevel,
      fun_idx,
      input,
      &mut io_buffer,
    )
  };
  let (query_record, output) = match result {
    Ok(pair) => pair,
    Err(err) => return LeanExcept::error_string(&err.to_string()),
  };

  let lean_query_counts = build_query_counts_array(&query_record, &toplevel);
  LeanExcept::ok(LeanProd::new(build_g_array(&output), lean_query_counts))
}

/// `AiurSystem.proveMultiStark`: prove the MultiStark recursive
/// verifier over proof-advice/vk/claims byte blobs. The proof blob is the
/// expanded per-query transport, while `Proof::to_bytes` remains the compact
/// storage/wire representation. Buffer construction
/// and executor selection as in `rs_aiur_multi_stark_execute`; the
/// prove itself reuses the executor-generic `AiurSystem::prove_ixvm`.
/// Returns `(claim, proof)`; the final buffer is not returned.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_multi_stark_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  pub_input: LeanArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind("AiurSystem.proveMultiStark", || {
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let mut io_buffer =
      ixvm_codegen::aiur_multi_stark_runner::verifier_io_buffer(
        proof_bytes.as_bytes(),
        vk_bytes.as_bytes(),
        claims_bytes.as_bytes(),
      );
    let args = pub_input.map(|x| lean_unbox_g(&x));

    let system = aiur_system_obj.get();
    let (claim, proof) = if use_bytecode {
      system.prove(fun_idx, &args, &mut io_buffer)
    } else {
      system.prove_ixvm(
        fun_idx,
        &args,
        &mut io_buffer,
        ixvm_codegen::aiur_multi_stark_runner::execute_multi_stark,
      )
    };

    let lean_proof: LeanOwned =
      LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
    // Array G × Proof
    LeanProd::new(build_g_array(&claim), lean_proof).into()
  })
}

/// `AiurSystem.proveMultiStarkJoin`: prove one valid join-entrypoint execution
/// using the same native advice builder and generated/interpreted executor
/// selection as `rs_aiur_multi_stark_join_execute`.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
extern "C" fn rs_aiur_multi_stark_join_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  pub_input: LeanArray<LeanBorrowed<'_>>,
  left_proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  recursion_vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  left_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  output_claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  allowed_bytes: LeanByteArray<LeanBorrowed<'_>>,
  preimages_blob: LeanByteArray<LeanBorrowed<'_>>,
  trees_blob: LeanByteArray<LeanBorrowed<'_>>,
  paths_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = match build_multi_stark_join_io_buffer(
    left_proof_bytes.as_bytes(),
    right_proof_bytes.as_bytes(),
    recursion_vk_bytes.as_bytes(),
    left_claims_bytes.as_bytes(),
    right_claims_bytes.as_bytes(),
    output_claim_bytes.as_bytes(),
    allowed_bytes.as_bytes(),
    preimages_blob.as_bytes(),
    trees_blob.as_bytes(),
    paths_blob.as_bytes(),
  ) {
    Ok(io) => io,
    Err(err) => return LeanExcept::error_string(&err),
  };
  let args = pub_input.map(|x| lean_unbox_g(&x));

  let system = aiur_system_obj.get();
  let (claim, proof) = if use_bytecode {
    system.prove(fun_idx, &args, &mut io_buffer)
  } else {
    system.prove_ixvm(
      fun_idx,
      &args,
      &mut io_buffer,
      ixvm_codegen::aiur_multi_stark_runner::execute_multi_stark,
    )
  };

  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  LeanExcept::ok(LeanProd::new(build_g_array(&claim), lean_proof))
}

#[allow(clippy::too_many_arguments)]
fn build_ix_aggr_io_buffer(
  shape: usize,
  left_proof_advice: &[u8],
  right_proof_advice: &[u8],
  ixvm_vk: &[u8],
  self_vk: &[u8],
  left_claims: &[u8],
  right_claims: &[u8],
  output_claim: &[u8],
  allowed: &[u8],
  preimages_blob: &[u8],
  trees_blob: &[u8],
  paths_blob: &[u8],
) -> Result<IOBuffer, String> {
  use ixvm_codegen::aiur_ix_aggr_runner::{
    AggrAdvice, aggr_io_buffer, decode_aggr_paths, decode_aggr_preimages,
    decode_aggr_trees,
  };

  let shape = u8::try_from(shape)
    .map_err(|err| format!("aggr shape {shape} out of range: {err}"))?;
  let preimages = decode_aggr_preimages(preimages_blob)?;
  let trees = decode_aggr_trees(trees_blob)?;
  let paths = decode_aggr_paths(paths_blob)?;
  Ok(aggr_io_buffer(&AggrAdvice {
    shape,
    proof_advice: [left_proof_advice, right_proof_advice],
    ixvm_vk,
    self_vk,
    child_claims: [left_claims, right_claims],
    output_claim,
    allowed,
    preimages: &preimages,
    trees: &trees,
    paths: &paths,
  }))
}

/// `Bytecode.Toplevel.executeIxAggr`: execute the `ix_aggr` entrypoint over
/// raw proof-advice/claim/tree blobs plus the shape hint. The native builder
/// expands the compact keyed framing directly into the circuit's
/// seven-channel IO buffer. As with `rs_aiur_multi_stark_execute`, callers
/// may select either generated execution or the generic bytecode
/// interpreter.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
extern "C" fn rs_aiur_ix_aggr_execute(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  pub_input: LeanArray<LeanBorrowed<'_>>,
  shape: LeanNat<LeanBorrowed<'_>>,
  left_proof_advice_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_proof_advice_bytes: LeanByteArray<LeanBorrowed<'_>>,
  ixvm_vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  self_vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  left_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  output_claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  allowed_bytes: LeanByteArray<LeanBorrowed<'_>>,
  preimages_blob: LeanByteArray<LeanBorrowed<'_>>,
  trees_blob: LeanByteArray<LeanBorrowed<'_>>,
  paths_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = match build_ix_aggr_io_buffer(
    lean_unbox_nat_as_usize(shape.inner()),
    left_proof_advice_bytes.as_bytes(),
    right_proof_advice_bytes.as_bytes(),
    ixvm_vk_bytes.as_bytes(),
    self_vk_bytes.as_bytes(),
    left_claims_bytes.as_bytes(),
    right_claims_bytes.as_bytes(),
    output_claim_bytes.as_bytes(),
    allowed_bytes.as_bytes(),
    preimages_blob.as_bytes(),
    trees_blob.as_bytes(),
    paths_blob.as_bytes(),
  ) {
    Ok(io) => io,
    Err(err) => return LeanExcept::error_string(&err),
  };
  let input = pub_input.map(|x| lean_unbox_g(&x));

  let _g = tracing::info_span!("aiur/execute_ix_aggr").entered();
  let result = if use_bytecode {
    toplevel.execute(fun_idx, input, &mut io_buffer)
  } else {
    ixvm_codegen::aiur_ix_aggr_runner::execute_ix_aggr(
      &toplevel,
      fun_idx,
      input,
      &mut io_buffer,
    )
  };
  let (query_record, output) = match result {
    Ok(pair) => pair,
    Err(err) => return LeanExcept::error_string(&err.to_string()),
  };

  let lean_query_counts = build_query_counts_array(&query_record, &toplevel);
  LeanExcept::ok(LeanProd::new(build_g_array(&output), lean_query_counts))
}

/// `AiurSystem.proveIxAggr`: prove one valid `ix_aggr` execution using the
/// same native advice builder and generated/interpreted executor selection
/// as `rs_aiur_ix_aggr_execute`.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
extern "C" fn rs_aiur_ix_aggr_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  pub_input: LeanArray<LeanBorrowed<'_>>,
  shape: LeanNat<LeanBorrowed<'_>>,
  left_proof_advice_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_proof_advice_bytes: LeanByteArray<LeanBorrowed<'_>>,
  ixvm_vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  self_vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  left_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  right_claims_bytes: LeanByteArray<LeanBorrowed<'_>>,
  output_claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  allowed_bytes: LeanByteArray<LeanBorrowed<'_>>,
  preimages_blob: LeanByteArray<LeanBorrowed<'_>>,
  trees_blob: LeanByteArray<LeanBorrowed<'_>>,
  paths_blob: LeanByteArray<LeanBorrowed<'_>>,
  use_bytecode: bool,
) -> LeanExcept<LeanOwned> {
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = match build_ix_aggr_io_buffer(
    lean_unbox_nat_as_usize(shape.inner()),
    left_proof_advice_bytes.as_bytes(),
    right_proof_advice_bytes.as_bytes(),
    ixvm_vk_bytes.as_bytes(),
    self_vk_bytes.as_bytes(),
    left_claims_bytes.as_bytes(),
    right_claims_bytes.as_bytes(),
    output_claim_bytes.as_bytes(),
    allowed_bytes.as_bytes(),
    preimages_blob.as_bytes(),
    trees_blob.as_bytes(),
    paths_blob.as_bytes(),
  ) {
    Ok(io) => io,
    Err(err) => return LeanExcept::error_string(&err),
  };
  let args = pub_input.map(|x| lean_unbox_g(&x));

  let system = aiur_system_obj.get();
  let (claim, proof) = if use_bytecode {
    system.prove(fun_idx, &args, &mut io_buffer)
  } else {
    system.prove_ixvm(
      fun_idx,
      &args,
      &mut io_buffer,
      ixvm_codegen::aiur_ix_aggr_runner::execute_ix_aggr,
    )
  };

  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  LeanExcept::ok(LeanProd::new(build_g_array(&claim), lean_proof))
}

// =============================================================================
// Helpers
// =============================================================================

/// Prevent Rust panics (including CUDA runtime failures) from unwinding across
/// the Lean C ABI. Lean receives the failure as an ordinary `Except.error`.
fn ffi_catch_unwind(
  context: &str,
  f: impl FnOnce() -> LeanOwned,
) -> LeanExcept<LeanOwned> {
  match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
    Ok(value) => LeanExcept::ok(value),
    Err(payload) => {
      let message = payload
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
        .unwrap_or("unknown Rust panic");
      LeanExcept::error_string(&format!("{context}: {message}"))
    },
  }
}

fn ffi_catch_unwind_except(
  context: &str,
  f: impl FnOnce() -> LeanExcept<LeanOwned>,
) -> LeanExcept<LeanOwned> {
  match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
    Ok(result) => result,
    Err(payload) => {
      let message = payload
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
        .unwrap_or("unknown Rust panic");
      LeanExcept::error_string(&format!("{context}: {message}"))
    },
  }
}

/// Build a Lean `Array G` from a slice of field elements.
fn build_g_array(values: &[G]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(values.len());
  for (i, g) in values.iter().enumerate() {
    arr.set(i, LeanOwned::box_u64(g.as_canonical_u64()));
  }
  arr
}

fn decode_io_buffer(
  io_data_arr: &LeanArray<LeanBorrowed<'_>>,
  io_map_arr: &LeanArray<LeanBorrowed<'_>>,
) -> IOBuffer {
  let data = decode_io_buffer_data(io_data_arr);
  let map = decode_io_buffer_map(io_map_arr);
  IOBuffer { data, map }
}

/// Build a Lean `Array (G × Array G)` enumerating the per-channel
/// data arenas of an `IOBuffer`.
fn build_lean_io_data(io_buffer: &IOBuffer) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(io_buffer.data.len());
  for (i, (channel, arena)) in io_buffer.data.iter().enumerate() {
    let channel_box = LeanOwned::box_u64(channel.as_canonical_u64());
    let arena_arr = build_g_array(arena);
    let elt = LeanProd::new(channel_box, arena_arr);
    arr.set(i, elt);
  }
  arr
}

/// Build a Lean `Array ((G × Array G) × IOKeyInfo)` enumerating the
/// channel-keyed info map of an `IOBuffer`.
fn build_lean_io_map(io_buffer: &IOBuffer) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(io_buffer.map.len());
  for (i, ((channel, key), info)) in io_buffer.map.iter().enumerate() {
    let channel_box = LeanOwned::box_u64(channel.as_canonical_u64());
    let key_arr = build_g_array(key);
    let channel_key = LeanProd::new(channel_box, key_arr);
    let key_info = LeanAiurIOKeyInfo::alloc(0);
    key_info.set_obj(0, LeanOwned::box_usize(info.idx));
    key_info.set_obj(1, LeanOwned::box_usize(info.len));
    let map_elt = LeanProd::new(channel_key, key_info);
    arr.set(i, map_elt);
  }
  arr
}

fn decode_commitment_parameters(
  obj: &LeanAiurCommitmentParameters<impl LeanRef>,
) -> CommitmentParameters {
  let ctor = obj.as_ctor();
  CommitmentParameters {
    log_blowup: lean_unbox_nat_as_usize(&ctor.get(0)),
    cap_height: lean_unbox_nat_as_usize(&ctor.get(1)),
  }
}

fn decode_fri_parameters(
  obj: &LeanAiurFriParameters<impl LeanRef>,
) -> FriParameters {
  let ctor = obj.as_ctor();
  FriParameters {
    log_final_poly_len: lean_unbox_nat_as_usize(&ctor.get(0)),
    max_log_arity: lean_unbox_nat_as_usize(&ctor.get(1)),
    num_queries: lean_unbox_nat_as_usize(&ctor.get(2)),
    commit_proof_of_work_bits: lean_unbox_nat_as_usize(&ctor.get(3)),
    query_proof_of_work_bits: lean_unbox_nat_as_usize(&ctor.get(4)),
  }
}

fn decode_io_buffer_data(
  arr: &LeanArray<LeanBorrowed<'_>>,
) -> FxHashMap<G, Vec<G>> {
  let mut data = FxHashMap::with_capacity_and_hasher(arr.len(), FxBuildHasher);
  for elt in arr.iter() {
    let pair = elt.as_ctor();
    let channel = lean_unbox_g(&pair.get(0));
    let arena = pair.get(1).as_array().map(|x| lean_unbox_g(&x));
    data.insert(channel, arena);
  }
  data
}

fn decode_io_buffer_map(
  arr: &LeanArray<LeanBorrowed<'_>>,
) -> FxHashMap<(G, Vec<G>), IOKeyInfo> {
  let mut map = FxHashMap::with_capacity_and_hasher(arr.len(), FxBuildHasher);
  for elt in arr.iter() {
    let pair = elt.as_ctor();
    let channel_key = pair.get(0).as_ctor();
    let channel = lean_unbox_g(&channel_key.get(0));
    let key = channel_key.get(1).as_array().map(|x| lean_unbox_g(&x));
    let info_ctor = pair.get(1).as_ctor();
    let info = IOKeyInfo {
      idx: lean_unbox_nat_as_usize(&info_ctor.get(0)),
      len: lean_unbox_nat_as_usize(&info_ctor.get(1)),
    };
    map.insert((channel, key), info);
  }
  map
}

// =============================================================================
// SP1 aggregate-root terminal (feature `sp1`)
// =============================================================================

/// `Aiur.sp1CompressAggregateRoot` verifies one `ix_aggr` root inside SP1 and
/// optionally runs the stock SP1 recursion tail through Groth16/Plonk.
/// Default builds retain this symbol as a checked feature-disabled stub.
#[unsafe(no_mangle)]
extern "C" fn rs_sp1_compress_aggregate_root(
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  mode: LeanString<LeanBorrowed<'_>>,
  output: LeanString<LeanBorrowed<'_>>,
  onchain_output: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  #[cfg(feature = "sp1")]
  {
    let fri = decode_fri_parameters(&fri_parameters);
    let mode = match mode.as_str().parse::<sp1_compress_host::Mode>() {
      Ok(mode) => mode,
      Err(error) => return LeanExcept::error_string(&error),
    };
    let output = match output.as_str() {
      "" => None,
      path => Some(std::path::PathBuf::from(path)),
    };
    let onchain_output = match onchain_output.as_str() {
      "" => None,
      path => Some(std::path::PathBuf::from(path)),
    };
    match sp1_compress_host::run_sp1_blocking(
      vk_bytes.as_bytes().to_vec(),
      claim_bytes.as_bytes().to_vec(),
      proof_bytes.as_bytes().to_vec(),
      &fri,
      mode,
      output.as_deref(),
      onchain_output.as_deref(),
    ) {
      Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
      Err(error) => LeanExcept::error_string(&format!("{error:#}")),
    }
  }
  #[cfg(not(feature = "sp1"))]
  {
    let _ = (
      &vk_bytes,
      &claim_bytes,
      &proof_bytes,
      &fri_parameters,
      &mode,
      &output,
      &onchain_output,
    );
    LeanExcept::error_string(
      "ix was built without SP1 compression; rebuild with IX_SP1=1",
    )
  }
}

// =============================================================================
// Flock aggregate-root Stage 3 (feature `flock`)
// =============================================================================

/// Profile, compile/evaluate, or prove the Flock P3-verifier leaf relation for
/// one canonical raw IxVM proof. The proof mode is intentionally diagnostic
/// until the Stage 2 internal-node artifact codec and uniform claim land.
#[unsafe(no_mangle)]
extern "C" fn rs_flock_stage2_ixvm_leaf(
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  verify_claim_index: LeanNat<LeanBorrowed<'_>>,
  query_count: LeanNat<LeanBorrowed<'_>>,
  mode: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  #[cfg(feature = "flock")]
  {
    let result = (|| {
      let fri = decode_fri_parameters(&fri_parameters);
      let verify_claim_index =
        u64::try_from(lean_unbox_nat_as_usize(verify_claim_index.inner()))
          .map_err(|error| {
            anyhow::anyhow!("verify_claim index exceeds u64: {error}")
          })?;
      let query_count = lean_unbox_nat_as_usize(query_count.inner());
      let backend = flock_stage3_host::FlockStage2Backend;
      match mode.as_str().to_ascii_lowercase().as_str() {
        "profile" => {
          let report = backend.profile_ixvm_leaf(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
          )?;
          println!("{report}");
          Ok(())
        },
        "pcs-size" => {
          let report = backend.size_ixvm_leaf_pcs_fri_prefix(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
            query_count,
          )?;
          println!("{report}");
          Ok(())
        },
        "size" => {
          let report = backend.size_ixvm_leaf(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
          )?;
          println!("{report}");
          Ok(())
        },
        "pcs" => {
          let report = backend.profile_ixvm_leaf_pcs_fri_prefix(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
            query_count,
          )?;
          println!("{report}");
          Ok(())
        },
        "preflight" => {
          let report = backend.preflight_ixvm_leaf(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
          )?;
          println!("{report}");
          Ok(())
        },
        "prove" => {
          let report = backend.preflight_ixvm_leaf(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
          )?;
          println!("{report}");
          println!("starting Flock Stage 2 P3 leaf prover");
          let artifact = backend.prove_ixvm_leaf(
            vk_bytes.as_bytes(),
            claim_bytes.as_bytes(),
            proof_bytes.as_bytes(),
            &fri,
            verify_claim_index,
          )?;
          if artifact.statement().digest() != report.p3_statement_digest
            || artifact.relation_manifest().relation_digest()
              != report.relation_digest
          {
            return Err(anyhow::anyhow!(
              "Flock leaf prover rebuilt an identity different from preflight"
            ));
          }
          backend.verify_ixvm_leaf(
            &artifact,
            artifact.statement(),
            &report.relation_digest,
          )?;
          println!(
            "Flock Stage 2 P3 leaf proof verified; bundle={} bytes",
            artifact.proof_bundle_bytes().len(),
          );
          Ok(())
        },
        other => Err(anyhow::anyhow!(
          "unknown Flock Stage 2 leaf mode `{other}` (expected profile|pcs-size|size|pcs|preflight|prove)"
        )),
      }
    })();
    match result {
      Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
      Err(error) => LeanExcept::error_string(&format!("{error:#}")),
    }
  }
  #[cfg(not(feature = "flock"))]
  {
    let _ = (
      &vk_bytes,
      &claim_bytes,
      &proof_bytes,
      &fri_parameters,
      &verify_claim_index,
      &query_count,
      &mode,
    );
    LeanExcept::error_string(
      "ix was built without Flock Stage 2; rebuild with IX_FLOCK=1",
    )
  }
}

/// Structured verifier-core lower-bound benchmark for one canonical IxVM P3
/// proof. The JSON explicitly identifies the missing `CheckEnv` semantics and
/// the exact-witness cache scope so callers cannot mistake it for the binding
/// Stage 2 comparison.
#[unsafe(no_mangle)]
extern "C" fn rs_flock_stage2_ixvm_leaf_benchmark(
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  verify_claim_index: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  #[cfg(feature = "flock")]
  {
    let result = (|| {
      let fri = decode_fri_parameters(&fri_parameters);
      let verify_claim_index =
        u64::try_from(lean_unbox_nat_as_usize(verify_claim_index.inner()))
          .map_err(|error| {
            anyhow::anyhow!("verify_claim index exceeds u64: {error}")
          })?;
      let report = flock_stage3_host::FlockStage2Backend
        .benchmark_ixvm_verifier_core(
          vk_bytes.as_bytes(),
          claim_bytes.as_bytes(),
          proof_bytes.as_bytes(),
          &fri,
          verify_claim_index,
        )?;
      let digest_hex = |digest: [u8; 32]| {
        blake3::Hash::from_bytes(digest).to_hex().to_string()
      };
      let preflight = &report.preflight;
      let relation = &preflight.relation;
      let advice = &preflight.advice;
      let timings = &report.timings;
      let json = serde_json::json!({
        "schema_version": 1,
        "status": "ok",
        "backend": "flock-verifier-core",
        "semantic_scope": "p3-verifier-only",
        "cache_scope": "same-witness-lower-bound",
        "identity": {
          "p3_statement_digest": digest_hex(preflight.p3_statement_digest),
          "output_claim_digest": digest_hex(preflight.output_claim_digest),
          "relation_digest": digest_hex(preflight.relation_digest),
          "circuit_digest": digest_hex(report.circuit_digest),
          "config_digest": digest_hex(preflight.config_digest),
        },
        "transport": {
          "verifying_key_bytes": preflight.verifying_key_bytes,
          "claim_bytes": preflight.claim_bytes,
          "compact_proof_bytes": preflight.compact_proof_bytes,
          "advice_bytes": advice.advice_bytes,
        },
        "p3_shape": {
          "total_circuits": advice.total_circuits,
          "active_circuits": advice.active_circuits,
          "queries": advice.queries,
          "fri_rounds": advice.fri_rounds,
          "input_rounds_per_query": advice.input_rounds_per_query,
          "commitment_cap_digests": advice.commitment_cap_digests,
          "input_merkle_siblings": advice.input_merkle_siblings,
          "fri_merkle_siblings": advice.fri_merkle_siblings,
          "opened_base_values": advice.opened_base_values,
          "fri_sibling_extension_values": advice.fri_sibling_extension_values,
          "other_extension_values": advice.other_extension_values,
        },
        "relation": {
          "nu": relation.nu,
          "table_capacity": relation.table_capacity,
          "inputs": relation.relation_inputs,
          "public_values": relation.public_values,
          "total_rows": relation.total_rows(),
          "rows": {
            "blake3": relation.blake3_rows,
            "digest_order": relation.digest_order_rows,
            "goldilocks_add": relation.goldilocks_add_rows,
            "goldilocks_mul": relation.goldilocks_mul_rows,
            "lane_repack": relation.lane_repack_rows,
            "canonical_goldilocks": relation.canonical_goldilocks_rows,
            "equality": relation.equality_rows,
            "zero_constraint": relation.zero_constraint_rows,
            "hash_sample": relation.hash_sample_rows,
            "field_sample": relation.field_sample_rows,
            "u64_split": relation.u64_split_rows,
            "byte_window": relation.byte_window_rows,
          },
        },
        "timings_ns": {
          "prepare": timings.prepare_ns,
          "typed_witness": timings.typed_witness_ns,
          "preflight": timings.preflight_ns,
          "manifest": timings.manifest_ns,
          "same_witness_prove": timings.same_witness_prove_ns,
          "valid_verify": timings.valid_verify_ns,
          "corrupt_reject": timings.corrupt_reject_ns,
          "input_to_verified_output": timings.input_to_verified_output_ns,
          "wall_with_negative_check": timings.wall_with_negative_check_ns,
        },
        "proof": {
          "bundle_bytes": report.proof_bundle_bytes,
          "bundle_digest": digest_hex(report.proof_bundle_digest),
          "valid_verification": true,
          "corrupted_rejected": true,
        },
      });
      serde_json::to_vec_pretty(&json).map_err(|error| {
        anyhow::anyhow!("encode Flock benchmark JSON: {error}")
      })
    })();
    match result {
      Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
      Err(error) => LeanExcept::error_string(&format!("{error:#}")),
    }
  }
  #[cfg(not(feature = "flock"))]
  {
    let _ = (
      &vk_bytes,
      &claim_bytes,
      &proof_bytes,
      &fri_parameters,
      &verify_claim_index,
    );
    LeanExcept::error_string(
      "ix was built without Flock Stage 2; rebuild with IX_FLOCK=1",
    )
  }
}

#[cfg(feature = "flock")]
fn write_flock_artifact_atomic(
  path: &std::path::Path,
  bytes: &[u8],
) -> anyhow::Result<()> {
  use anyhow::{Context, bail};

  let Some(file_name) = path.file_name() else {
    bail!("Flock output path has no file name: {}", path.display());
  };
  let temporary = path.with_file_name(format!(
    ".{}.tmp-{}",
    file_name.to_string_lossy(),
    std::process::id(),
  ));
  std::fs::write(&temporary, bytes).with_context(|| {
    format!("write temporary Flock artifact {}", temporary.display())
  })?;
  if let Err(error) = std::fs::rename(&temporary, path) {
    let _ = std::fs::remove_file(&temporary);
    return Err(error)
      .with_context(|| format!("install Flock artifact {}", path.display()));
  }
  Ok(())
}

/// Compile/evaluate or prove the complete no-RISC-V Flock relation for one
/// canonical `ix_aggr` root. Default builds retain a checked feature-disabled
/// stub so the Lean CLI remains linkable.
#[unsafe(no_mangle)]
extern "C" fn rs_flock_stage3_aggregate_root(
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  mode: LeanString<LeanBorrowed<'_>>,
  output: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  #[cfg(feature = "flock")]
  {
    let fri = decode_fri_parameters(&fri_parameters);
    let backend = flock_stage3_host::FlockStage3Backend;
    let result = match mode.as_str().to_ascii_lowercase().as_str() {
      "preflight" => {
        if !output.as_str().is_empty() {
          Err(anyhow::anyhow!("--output is only valid with --mode prove"))
        } else {
          backend
            .preflight_stage2(
              vk_bytes.as_bytes(),
              claim_bytes.as_bytes(),
              proof_bytes.as_bytes(),
              &fri,
            )
            .map(|report| println!("{report}"))
        }
      },
      "prove" => {
        if output.as_str().is_empty() {
          Err(anyhow::anyhow!(
            "Flock proving requires --output so the expensive artifact is retained"
          ))
        } else {
          (|| {
            let report = backend.preflight_stage2(
              vk_bytes.as_bytes(),
              claim_bytes.as_bytes(),
              proof_bytes.as_bytes(),
              &fri,
            )?;
            println!("{report}");
            println!("starting Flock Stage 3 prover");
            let artifact = backend.prove_stage2(
              vk_bytes.as_bytes(),
              claim_bytes.as_bytes(),
              proof_bytes.as_bytes(),
              &fri,
            )?;
            if artifact.statement().stage2_root_digest()
              != &report.stage2_root_digest
              || artifact.statement().relation_digest()
                != &report.relation_digest
              || artifact.statement().digest() != report.stage3_statement_digest
            {
              return Err(anyhow::anyhow!(
                "Flock prover rebuilt a statement different from preflight"
              ));
            }
            backend.verify_stage2(&artifact, artifact.statement())?;
            let encoded = artifact.to_bytes();
            let output_path = std::path::Path::new(output.as_str());
            write_flock_artifact_atomic(output_path, &encoded)?;
            println!(
              "Flock Stage 3 proof verified; artifact={} bytes; saved to {}",
              encoded.len(),
              output_path.display(),
            );
            Ok(())
          })()
        }
      },
      other => Err(anyhow::anyhow!(
        "unknown Flock mode `{other}` (expected preflight|prove)"
      )),
    };
    match result {
      Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
      Err(error) => LeanExcept::error_string(&format!("{error:#}")),
    }
  }
  #[cfg(not(feature = "flock"))]
  {
    let _ =
      (&vk_bytes, &claim_bytes, &proof_bytes, &fri_parameters, &mode, &output);
    LeanExcept::error_string(
      "ix was built without Flock Stage 3; rebuild with IX_FLOCK=1",
    )
  }
}
