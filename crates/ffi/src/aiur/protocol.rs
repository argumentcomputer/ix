use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::sync::LazyLock;

use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExcept,
  LeanExternal, LeanNat, LeanOption, LeanOwned, LeanProd, LeanRef, LeanString,
};

use crate::{
  aiur::{lean_unbox_g, lean_unbox_nat_as_usize, toplevel::decode_toplevel},
  lean::{
    LeanAiurCircuitShape, LeanAiurCommitmentParameters, LeanAiurExecuteResult,
    LeanAiurFriParameters, LeanAiurIOKeyInfo, LeanAiurProveEnvResult,
    LeanAiurProveResult, LeanAiurQueryCount, LeanAiurShardProveResult,
    LeanAiurShardResult, LeanAiurToplevel,
  },
};
use aiur::{
  G,
  execute::{IOBuffer, IOKeyInfo, QueryRecord},
  synthesis::{
    AiurProof, AiurSystem, CircuitShape, GatedProve,
    ShardRetention as Retention,
  },
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
/// Verify and serialize the proof transport consumed by the in-circuit
/// recursive verifier.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_advice_bytes(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  proof_obj: LeanExternal<AiurProof, LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let claim = claim.map(|x| lean_unbox_g(&x));
  match aiur_system_obj.get().proof_to_advice_bytes(&claim, proof_obj.get()) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err),
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

/// Decode a counted address-list blob (`Ix.Cli.CheckCmd.addrListsBlob`):
/// per list, a 4-byte LE count followed by that many 32-byte addresses.
/// The wire format of every partition crossing the FFI (the shard
/// batch, the manifest emit).
pub(crate) fn decode_addr_lists(
  bytes: &[u8],
) -> Result<Vec<Vec<ix_common::address::Address>>, String> {
  let mut lists = Vec::new();
  let mut off = 0usize;
  while off < bytes.len() {
    if off + 4 > bytes.len() {
      return Err("addr lists: truncated count".into());
    }
    let n =
      u32::from_le_bytes(bytes[off..off + 4].try_into().unwrap()) as usize;
    off += 4;
    if off + n * 32 > bytes.len() {
      return Err("addr lists: truncated addresses".into());
    }
    lists.push(
      ix_common::address::Address::unpack(&bytes[off..off + n * 32]).collect(),
    );
    off += n * 32;
  }
  Ok(lists)
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
// Two calibrations, each accurate in its own regime, combined as a MAX
// in `exec_rss_estimate` because the per-owned-byte execution footprint
// is env-dependent and the gate's contract is NEVER OOM:
// - The affine fit (4.5 GiB + 1100x) measured on ISLB's small shards
//   (1.4-5.7 MB owned; a pure ratio under-reserved them and OOM'd a
//   128 GB box).
// - The pure ratio (2500x, ~2300x measured + margin) validated on
//   Mathlib's full-width 233-shard batch at +2% of estimate; the
//   affine slope alone under-reserved Mathlib-class shards and
//   over-admitted a 132-shard full-width batch to 486/495 GB
//   (OOM, 2026-08-29 — the first Mathlib full-width run under the
//   affine constant).
// The max reproduces each fit where it was measured: small shards take
// the affine branch (ISLB bench reservations unchanged), large shards
// the ratio branch.
const EXEC_RSS_PER_OWNED_BYTE: usize = 1100;
const EXEC_RSS_RATIO_PER_OWNED_BYTE: usize = 2500;

/// Per-shard execution-RSS reserve: the max of the two measured fits
/// (see the constants above).
fn exec_rss_estimate(owned_bytes: usize) -> usize {
  EXEC_RSS_FIXED_BYTES
    .saturating_add(owned_bytes.saturating_mul(EXEC_RSS_PER_OWNED_BYTE))
    .max(owned_bytes.saturating_mul(EXEC_RSS_RATIO_PER_OWNED_BYTE))
}

/// FFI: the detected prover/execution RAM budget in bytes
/// ([`detected_ram_budget`]: [`ix_kernel::shard::RAM_USABLE_FRAC`] of
/// `MemAvailable`), or `0` when `/proc/meminfo` is unreadable — the caller
/// decides whether to fail closed.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_detected_ram_budget()
-> lean_ffi::object::LeanIOResult<LeanOwned> {
  let bytes = detected_ram_budget().unwrap_or(0);
  lean_ffi::object::LeanIOResult::ok(LeanOwned::box_u64(bytes as u64))
}

/// Detected prover/execution RAM budget:
/// [`ix_kernel::shard::RAM_USABLE_FRAC`] of `MemAvailable`, reserving
/// the rest for the OS. `None` (no gate) when meminfo is unreadable —
/// disabling the check beats guessing at it.
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)]
#[allow(clippy::cast_sign_loss)] // MemAvailable and the fraction are positive
fn detected_ram_budget() -> Option<usize> {
  available_ram_bytes()
    .map(|b| (b as f64 * ix_kernel::shard::RAM_USABLE_FRAC) as usize)
}

/// `MemAvailable` from `/proc/meminfo`, in bytes (Linux; includes
/// reclaimable page cache). `None` if unreadable — the caller then
/// disables the gate rather than guessing.
fn available_ram_bytes() -> Option<usize> {
  let s = std::fs::read_to_string("/proc/meminfo").ok()?;
  let rest = s.lines().find_map(|l| l.strip_prefix("MemAvailable:"))?;
  let kib: usize = rest.trim().trim_end_matches("kB").trim().parse().ok()?;
  Some(kib * 1024)
}

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
  max_ram_bytes: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use rayon::prelude::*;
  let toplevel = decode_toplevel(&toplevel_obj);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let jobs = lean_unbox_nat_as_usize(jobs.inner());
  let max_ram_bytes = lean_unbox_nat_as_usize(max_ram_bytes.inner());
  let shards = match decode_addr_lists(shards_blob.as_bytes()) {
    Ok(v) => v,
    Err(e) => return LeanExcept::error_string(&e),
  };
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
      exec_rss_estimate(
        owned
          .iter()
          .filter_map(|a| env.get_const_bytes(a).map(|b| b.len()))
          .sum::<usize>(),
      )
    })
    .collect();
  let gate = RamGate {
    reserved: std::sync::Mutex::new(0),
    cv: std::sync::Condvar::new(),
    budget: detected_ram_budget().unwrap_or(usize::MAX),
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
  let check_batch = || -> Vec<(String, usize, usize)> {
    shards
      .par_iter()
      .zip(estimates.par_iter())
      .map(|(owned, est)| {
        gate.acquire(*est);
        let result =
          match ixvm_codegen::aiur_ixvm_witness::build_shard_check_env_witness(
            env, owned,
          ) {
            Err(e) => (format!("witness build: {e}"), 0, 1),
            Ok((_claim, input, mut io_buffer)) => match dispatch_execute(
              &toplevel,
              fun_idx,
              input,
              &mut io_buffer,
              use_bytecode,
            ) {
              Err(e) => (e, 0, 1),
              // Both reductions happen here, while the record is
              // still owned by this task: it is dropped before
              // `gate.release`, so admission keeps bounding peak RSS by
              // the shards in flight rather than by the whole partition.
              Ok((record, _output)) => {
                let peak = system.peak_prove_bytes(&record).peak;
                let parts = if max_ram_bytes > 0 && peak > max_ram_bytes {
                  system.suggested_split_parts(&record, max_ram_bytes)
                } else {
                  1
                };
                (String::new(), peak, parts)
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
  for (i, (err, peak, parts)) in results.iter().enumerate() {
    let row = LeanAiurShardResult::alloc(0);
    row.set_obj(0, LeanString::new(err));
    row.set_obj(1, LeanOwned::box_usize(*peak));
    row.set_obj(2, LeanOwned::box_usize(*parts));
    arr.set(i, row);
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
        |toplevel, fun_idx, input, io_buffer| {
          ixvm_codegen::aiur_ixvm_runner::execute_ixvm(
            toplevel, fun_idx, input, io_buffer,
          )
        },
      )
    };

    LeanExcept::ok(build_prove_env_result(&claim, proof, &io_buffer))
  })
}

/// `AiurSystem.shardProveWithEnv`: per-shard prove against a Rust-owned
/// `EnvHandle`, executing ONCE and proving from that record.
///
/// `max_ram_bytes` is a per-shard prover-RAM budget checked against the
/// executed record's projected peak, in the gap between execution and
/// the witness phase. `0` means "detect": 85% of `MemAvailable`, the
/// same policy the check batch's RAM gate uses. An unreadable
/// `/proc/meminfo` disables the check rather than guessing at it.
///
/// Over budget, the record is dropped and `proof` comes back as `none`
/// with the measured `peakBytes` and `suggestedParts` — the part count
/// the peak model projects will fit the budget
/// ([`AiurSystem::suggested_split_parts`], measured on the record while
/// it still exists). That is a RESULT, not an error: the caller's
/// answer is to cut the shard into that many parts and prove those.
/// Learning it here costs one execution instead of an OOM part-way
/// through an FFT. `suggestedParts` is `1` whenever the prove ran.
///
/// `exec_only` stops after execution + measurement: `proof` is `none`
/// either way, and `suggestedParts` is 1 exactly when the peak fits —
/// the split loop runs on executions alone, no STARK ever starts.
///
/// `trace_shards` lets an over-budget record be proven as a batch of
/// trace shards instead of being split into parts, whenever some shard
/// count fits the budget; `peakBytes` is then the heaviest shard's
/// projection and `suggestedParts` stays 1. `retention` overrides what the
/// batch keeps across its barrier: 1 retains every shard's stage 1, 2
/// regenerates each shard for round two, anything else lets the RAM model
/// choose (retain when the retained batch fits the budget).
///
/// Returns `(claimBytes, proof?, peakBytes, suggestedParts)`. The final IO buffer is
/// deliberately NOT returned: it is the shard's whole ingested byte
/// scope, both Lean callers discarded it, and marshalling it back is
/// pure cost on the largest buffers in the system.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_shard_prove_with_env(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  owned_blob: LeanByteArray<LeanBorrowed<'_>>,
  max_ram_bytes: LeanNat<LeanBorrowed<'_>>,
  exec_only: bool,
  trace_shards: bool,
  retention: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("AiurSystem.shardProveWithEnv", || {
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let max_ram_bytes = lean_unbox_nat_as_usize(max_ram_bytes.inner());
    let retention = match lean_unbox_nat_as_usize(retention.inner()) {
      1 => Some(Retention::Retain),
      2 => Some(Retention::Regenerate),
      _ => None,
    };
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

    // 0 = detect. Matching the check batch's gate keeps one RAM policy in
    // the system rather than two that can disagree.
    let budget = if max_ram_bytes > 0 {
      Some(max_ram_bytes)
    } else {
      detected_ram_budget()
    };
    let proved = aiur_system_obj.get().prove_ixvm_within_budget(
      fun_idx,
      &input,
      &mut io_buffer,
      |toplevel, fun_idx, input, io_buffer| {
        ixvm_codegen::aiur_ixvm_runner::execute_ixvm(
          toplevel, fun_idx, input, io_buffer,
        )
      },
      budget,
      exec_only,
      trace_shards,
      retention,
    );
    let (proof, peak, parts) = match proved {
      GatedProve::Proved { proof, peak, .. } => (
        LeanOption::some(LeanExternal::alloc(&AIUR_PROOF_CLASS, proof)),
        peak,
        1,
      ),
      GatedProve::Split { peak, parts } => (LeanOption::none(), peak, parts),
      GatedProve::Measured { peak } => (LeanOption::none(), peak, 1),
    };
    drop(io_buffer);

    let mut claim_bytes: Vec<u8> = Vec::new();
    claim.put(&mut claim_bytes);
    let result = LeanAiurShardProveResult::alloc(0);
    result.set_obj(0, LeanByteArray::from_bytes(&claim_bytes));
    result.set_obj(1, proof);
    result.set_obj(2, LeanOwned::box_usize(peak));
    result.set_obj(3, LeanOwned::box_usize(parts));
    LeanExcept::ok(result)
  })
}

/// `AiurSystem.proveEnvDistributed`: the whole environment as ONE claim,
/// `CheckEnv(root, none)`, proven from several worker records
/// (trace-sharding design §13.3). `owners_blob` is a `u32` worker count,
/// then a `u32` address count per worker, then every worker's owned
/// addresses (32 bytes each) in worker order. Worker 0 runs `verify_claim`
/// and defers every `check_owned` call for a constant it does not own;
/// worker `r` runs `check_owned` over the leaves it owns, in pointer
/// namespace `r`. The workers execute in parallel, the deferred calls'
/// counts are absorbed by their owners, and the records are proven as one
/// batch, each planned to `max_cells` committed cells (`0`: one shard per
/// record). `exec_only` stops after execution and the absorption of the
/// deferred calls, reporting each record's size (`proof` is `none`). Same
/// result shape as `shardProveWithEnv`, with `peakBytes` 0 and
/// `suggestedParts` 1.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove_env_distributed(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  check_owned_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  owners_blob: LeanByteArray<LeanBorrowed<'_>>,
  max_cells: LeanNat<LeanBorrowed<'_>>,
  exec_only: bool,
  exec_jobs: LeanNat<LeanBorrowed<'_>>,
  prefetch: bool,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("AiurSystem.proveEnvDistributed", || {
    let verify_idx = lean_unbox_nat_as_usize(verify_idx.inner());
    let check_owned_idx = lean_unbox_nat_as_usize(check_owned_idx.inner());
    let max_cells = lean_unbox_nat_as_usize(max_cells.inner());
    let exec_jobs = lean_unbox_nat_as_usize(exec_jobs.inner());
    let owners = match decode_owners_blob(&owners_blob) {
      Ok(owners) => owners,
      Err(e) => return LeanExcept::error_string(&e),
    };
    let proved = prove_env_distributed(
      aiur_system_obj.get(),
      &env_handle.get().env,
      verify_idx,
      check_owned_idx,
      &owners,
      max_cells,
      exec_only,
      exec_jobs,
      prefetch,
    );
    let (claim_bytes, proof) = match proved {
      Ok(proved) => proved,
      Err(e) => return LeanExcept::error_string(&e),
    };
    let result = LeanAiurShardProveResult::alloc(0);
    result.set_obj(0, LeanByteArray::from_bytes(&claim_bytes));
    result.set_obj(
      1,
      match proof {
        Some(proof) => {
          LeanOption::some(LeanExternal::alloc(&AIUR_PROOF_CLASS, proof))
        },
        None => LeanOption::none(),
      },
    );
    result.set_obj(2, LeanOwned::box_usize(0));
    result.set_obj(3, LeanOwned::box_usize(1));
    LeanExcept::ok(result)
  })
}

/// `u32 W`, `u32` counts, then the addresses (see
/// `rs_aiur_system_prove_env_distributed`).
fn decode_owners_blob(
  blob: &LeanByteArray<LeanBorrowed<'_>>,
) -> Result<Vec<Vec<ix_common::address::Address>>, String> {
  let bytes = blob.as_bytes();
  let word = |at: usize| -> Result<usize, String> {
    let chunk: [u8; 4] = bytes
      .get(at..at + 4)
      .and_then(|c| c.try_into().ok())
      .ok_or_else(|| "owners_blob: truncated header".to_string())?;
    Ok(u32::from_le_bytes(chunk) as usize)
  };
  let workers = word(0)?;
  let counts: Vec<usize> =
    (0..workers).map(|w| word(4 + 4 * w)).collect::<Result<_, _>>()?;
  let mut at = 4 + 4 * workers;
  let mut owners = Vec::with_capacity(workers);
  for count in counts {
    let end = at + 32 * count;
    let slice = bytes
      .get(at..end)
      .ok_or_else(|| "owners_blob: truncated addresses".to_string())?;
    owners.push(
      slice
        .as_chunks::<32>()
        .0
        .iter()
        .map(|c| {
          ix_common::address::Address::from_slice(c)
            .expect("32-byte chunk is an address")
        })
        .collect(),
    );
    at = end;
  }
  if at != bytes.len() {
    return Err("owners_blob: trailing bytes".into());
  }
  Ok(owners)
}

/// What a worker's execution produced: its record and IO buffer while they
/// are kept, and always its deferred calls and its output.
struct Executed {
  record: Option<(Box<QueryRecord>, Box<IOBuffer>)>,
  deferred: FxHashMap<Vec<G>, u64>,
  output: Vec<G>,
}

/// The order records are committed in, callers before callees: the workers
/// that may call into a worker (`callers`) must have executed before it
/// commits, so its rows carry the calls' multiplicities. Strongly connected
/// groups of mutually calling workers execute together and commit one after
/// the other; between groups one record at a time is in flight.
fn commit_order(callers: &[Vec<usize>]) -> Vec<Vec<usize>> {
  // Tarjan's components over the edges `caller -> callee`.
  let n = callers.len();
  let mut callees: Vec<Vec<usize>> = vec![Vec::new(); n];
  for (callee, cs) in callers.iter().enumerate() {
    for &caller in cs {
      callees[caller].push(callee);
    }
  }
  struct Tarjan<'a> {
    callees: &'a [Vec<usize>],
    index: Vec<Option<usize>>,
    low: Vec<usize>,
    on_stack: Vec<bool>,
    stack: Vec<usize>,
    next: usize,
    components: Vec<Vec<usize>>,
  }
  impl Tarjan<'_> {
    fn visit(&mut self, v: usize) {
      self.index[v] = Some(self.next);
      self.low[v] = self.next;
      self.next += 1;
      self.stack.push(v);
      self.on_stack[v] = true;
      for &w in &self.callees[v] {
        match self.index[w] {
          None => {
            self.visit(w);
            self.low[v] = self.low[v].min(self.low[w]);
          },
          Some(index) if self.on_stack[w] => {
            self.low[v] = self.low[v].min(index);
          },
          Some(_) => {},
        }
      }
      if self.low[v] == self.index[v].expect("indexed") {
        let mut component = Vec::new();
        loop {
          let w = self.stack.pop().expect("stack holds v");
          self.on_stack[w] = false;
          component.push(w);
          if w == v {
            break;
          }
        }
        component.sort_unstable();
        self.components.push(component);
      }
    }
  }
  let mut tarjan = Tarjan {
    callees: &callees,
    index: vec![None; n],
    low: vec![0; n],
    on_stack: vec![false; n],
    stack: Vec::new(),
    next: 0,
    components: Vec::new(),
  };
  for v in 0..n {
    if tarjan.index[v].is_none() {
      tarjan.visit(v);
    }
  }
  // Tarjan emits components in reverse topological order of `callees`
  // edges: a callee's component before its callers'. Reverse for callers
  // first.
  tarjan.components.reverse();
  tarjan.components
}

fn prove_env_distributed(
  system: &AiurSystem,
  env: &ixon::Env,
  verify_idx: usize,
  check_owned_idx: usize,
  owners: &[Vec<ix_common::address::Address>],
  max_cells: usize,
  exec_only: bool,
  exec_jobs: usize,
  prefetch: bool,
) -> Result<(Vec<u8>, Option<AiurProof>), String> {
  use aiur::execute::{Ownership, pointer_stride};
  use ixvm_codegen::aiur_ixvm_runner::execute_ixvm_in;
  use ixvm_codegen::aiur_ixvm_witness::{
    EnvCheckStatement, addr_key, worker_callers,
  };
  use rustc_hash::FxHashSet;

  if owners.is_empty() {
    return Err("no workers".into());
  }
  let statement = EnvCheckStatement::new(env)?;
  let input = statement.digest_key.clone();
  let toplevel = system.toplevel();
  let owned_keys: Vec<FxHashSet<Vec<G>>> = owners
    .iter()
    .map(|owned| owned.iter().map(addr_key).collect())
    .collect();
  let mut owner_of: FxHashMap<Vec<G>, usize> = FxHashMap::default();
  for (worker, keys) in owned_keys.iter().enumerate() {
    for key in keys {
      if owner_of.insert(key.clone(), worker).is_some() {
        return Err("a constant is owned by two workers".into());
      }
    }
  }
  let workers = owners.len();
  let jobs = if exec_jobs == 0 { workers } else { exec_jobs.min(workers) };
  let callers = worker_callers(env, owners);
  let groups = commit_order(&callers);
  let order: Vec<usize> = groups.iter().flatten().copied().collect();
  eprintln!(
    "[distributed] {workers} workers in {} groups, committed in order {order:?}, {jobs} executing at a time",
    groups.len()
  );

  // One execution of worker `worker`: worker 0 the claimed entry, the
  // others their owned leaves, each in its own pointer namespace, over a
  // fresh IO buffer. Deterministic, so a record can be re-executed for
  // its second round; the batch checks the headers agree.
  let execute = |worker: usize, round: &str| -> Result<Executed, String> {
    let started = std::time::Instant::now();
    let mut io = statement.worker_io(env, owners, worker);
    let mut record = QueryRecord::with_pointer_base(
      toplevel,
      worker * pointer_stride(workers),
    );
    record.ownership =
      Some(Ownership { callee: check_owned_idx, owned: owned_keys[worker].clone() });
    let mut output = Vec::new();
    if worker == 0 {
      output =
        execute_ixvm_in(toplevel, verify_idx, &input, &mut io, &mut record)
          .map_err(|e| format!("worker 0: {e}"))?;
    } else {
      // Leaves run as entries; each registers a multiplicity no claim
      // pulls, taken off only once every leaf has run: a zeroed entry
      // would read as a hint to a later leaf's walk and be replayed,
      // double-counting its callees.
      let mut entries: Vec<Vec<G>> = Vec::new();
      for addr in &owners[worker] {
        let key = addr_key(addr);
        let queries = &record.function_queries[check_owned_idx];
        // Reached already through another owned leaf's walk.
        if queries
          .get_index_of(&key)
          .is_some_and(|i| queries.mult_at(i) != G::ZERO)
        {
          continue;
        }
        execute_ixvm_in(toplevel, check_owned_idx, &key, &mut io, &mut record)
          .map_err(|e| format!("worker {worker}: {e}"))?;
        entries.push(key);
      }
      let queries = &mut record.function_queries[check_owned_idx];
      for key in entries {
        let i = queries.get_index_of(&key).expect("executed as an entry");
        let (_, multiplicity) =
          queries.get_index_mut(i).expect("index just found");
        *multiplicity -= G::ONE;
      }
    }
    // Every table must stay inside the worker's pointer namespace, or its
    // pointers collide with the next worker's.
    let stride = pointer_stride(workers);
    for (width, table) in &record.memory_queries {
      if table.len() > stride {
        return Err(format!(
          "worker {worker}: width-{width} table of {} entries exceeds the \
           pointer namespace of {stride}",
          table.len()
        ));
      }
    }
    let function_rows: usize =
      record.function_queries.iter().map(|q| q.len()).sum();
    let memory_rows: usize =
      record.memory_queries.iter().map(|(_, m)| m.len()).sum();
    let io_bytes: usize = io.data.values().map(|arena| 8 * arena.len()).sum();
    eprintln!(
      "[distributed] worker {worker}: executed for {round} in {:.1?}; {function_rows} function queries, {memory_rows} memory entries, {} B retained, {io_bytes} B of IO, {} deferred calls",
      started.elapsed(),
      aiur::execute::record_retained_bytes(&record),
      record.deferred.len()
    );
    let deferred = record.deferred.clone();
    Ok(Executed {
      record: Some((Box::new(record), Box::new(io))),
      deferred,
      output,
    })
  };
  let mut claim_bytes: Vec<u8> = Vec::new();
  statement.claim.put(&mut claim_bytes);
  std::thread::scope(|scope| {
    let mut pool = Workers {
      scope,
      execute: &execute,
      jobs,
      order: &order,
      callers: &callers,
      owner_of: &owner_of,
      check_owned_idx,
      executed: (0..workers).map(|_| None).collect(),
      served: vec![0; workers],
      prefetch,
      ahead: None,
    };
    if exec_only {
      let started = std::time::Instant::now();
      pool.execute_group(&order, "round one")?;
      for &worker in &order {
        drop(pool.take_record(worker, "round one")?);
      }
      eprintln!(
        "[distributed] {workers} workers executed and absorbed in {:.1?}",
        started.elapsed()
      );
      return Ok((claim_bytes, None));
    }

    // The first group executes before the batch, worker 0 among it (its
    // walk calls into every worker): its output is the claim's. From there
    // the batch asks for records in commit order (`Workers::supply`).
    let first = order[0];
    let mut wanted = callers[first].clone();
    wanted.push(first);
    pool.execute_group(&wanted, "round one")?;
    let output = pool.output();
    let (_, proof) = system.prove_record_supplier(
      verify_idx,
      &input,
      move || output,
      workers,
      |position| pool.supply(position),
      (max_cells > 0).then_some(max_cells),
    )?;
    Ok((claim_bytes, Some(proof)))
  })
}

/// The workers' executions, owned by the driver: run in groups, handed to
/// the prover one record at a time, the next one's execution started
/// ahead of its turn when asked to.
struct Workers<'scope, 'env> {
  scope: &'scope std::thread::Scope<'scope, 'env>,
  execute:
    &'env (dyn Fn(usize, &'static str) -> Result<Executed, String> + Sync),
  /// How many workers execute at once.
  jobs: usize,
  /// The commit order.
  order: &'env [usize],
  /// The workers that may call into each worker.
  callers: &'env [Vec<usize>],
  owner_of: &'env FxHashMap<Vec<G>, usize>,
  check_owned_idx: usize,
  executed: Vec<Option<Executed>>,
  /// How many times the prover has asked for each worker's record.
  served: Vec<u8>,
  /// Whether to execute the next worker in commit order while the prover
  /// works on the current one, at the price of a second resident record.
  prefetch: bool,
  /// The execution started ahead of its turn, if any.
  ahead: Option<(
    usize,
    std::thread::ScopedJoinHandle<'scope, Result<Executed, String>>,
  )>,
}

impl Workers<'_, '_> {
  /// Execute the workers among `wanted` that have not executed, `jobs` at
  /// a time: `jobs` threads each take the next pending worker from a shared
  /// counter until none is left, so a freed slot starts the next worker at
  /// once, and each thread's results come back through its join.
  fn execute_group(
    &mut self,
    wanted: &[usize],
    round: &'static str,
  ) -> Result<(), String> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    for &worker in wanted {
      self.settle_ahead(worker)?;
    }
    let pending: Vec<usize> = wanted
      .iter()
      .copied()
      .filter(|&worker| self.executed[worker].is_none())
      .collect();
    let execute = self.execute;
    let next = AtomicUsize::new(0);
    let results: Vec<Vec<(usize, Result<Executed, String>)>> =
      std::thread::scope(|scope| {
        let handles: Vec<_> = (0..self.jobs.max(1).min(pending.len()))
          .map(|_| {
            scope.spawn(|| {
              let mut done = Vec::new();
              loop {
                let at = next.fetch_add(1, Ordering::Relaxed);
                let Some(&worker) = pending.get(at) else { break };
                done.push((worker, execute(worker, round)));
              }
              done
            })
          })
          .collect();
        handles
          .into_iter()
          .map(|handle| handle.join().expect("worker thread panicked"))
          .collect()
      });
    for (worker, result) in results.into_iter().flatten() {
      self.executed[worker] = Some(result?);
    }
    Ok(())
  }

  /// If `worker`'s execution was started ahead of its turn, wait for it and
  /// keep it.
  fn settle_ahead(&mut self, worker: usize) -> Result<(), String> {
    if self.ahead.as_ref().is_some_and(|(started, _)| *started == worker) {
      let (_, handle) = self.ahead.take().expect("checked just above");
      let done = handle.join().expect("prefetch thread panicked")?;
      self.executed[worker] = Some(done);
    }
    Ok(())
  }

  /// The record of `worker` as the prover needs it: kept from its
  /// execution if still there, else executed again; the calls into it
  /// from every executed worker absorbed.
  fn take_record(
    &mut self,
    worker: usize,
    round: &'static str,
  ) -> Result<aiur::synthesis::Supplied<'static>, String> {
    self.settle_ahead(worker)?;
    let kept = self.executed[worker]
      .as_mut()
      .expect("executed before it is taken")
      .record
      .take();
    let (mut record, io) = match kept {
      Some(kept) => kept,
      None => (self.execute)(worker, round)?
        .record
        .expect("a fresh execution keeps its record"),
    };
    let mut into: FxHashMap<Vec<G>, u64> = FxHashMap::default();
    for (caller, done) in self.executed.iter().enumerate() {
      let Some(done) = done else { continue };
      for (args, &count) in &done.deferred {
        let Some(&owner) = self.owner_of.get(args) else {
          return Err(format!(
            "worker {caller} deferred a constant no worker owns"
          ));
        };
        if owner == worker {
          *into.entry(args.clone()).or_insert(0) += count;
        }
      }
    }
    record
      .absorb_deferred(self.check_owned_idx, &into)
      .map_err(|e| format!("worker {worker}: {e}"))?;
    Ok(aiur::synthesis::Supplied::Owned(record, io))
  }

  /// The prover's request for the record at `position` of the commit
  /// order. The first time, the worker and the callers it still lacks
  /// execute first; the second time, all callers have executed, and the
  /// worker is executed again. With prefetching, the next worker's
  /// execution for its coming round starts before this record is handed
  /// over, so it runs while the prover works on this one.
  fn supply(
    &mut self,
    position: usize,
  ) -> Result<aiur::synthesis::Supplied<'static>, String> {
    let worker = self.order[position];
    let first = self.served[worker] == 0;
    self.served[worker] += 1;
    if first {
      let mut wanted = self.callers[worker].clone();
      wanted.push(worker);
      self.execute_group(&wanted, "round one")?;
    }
    let supplied =
      self.take_record(worker, if first { "round one" } else { "round two" })?;
    if self.prefetch && self.ahead.is_none() {
      let next = self.order[(position + 1) % self.order.len()];
      let (needed, round) = match self.served[next] {
        0 => (self.executed[next].is_none(), "round one"),
        1 => (true, "round two"),
        _ => (false, ""),
      };
      if needed && next != worker {
        let execute = self.execute;
        self.ahead =
          Some((next, self.scope.spawn(move || execute(next, round))));
      }
    }
    Ok(supplied)
  }

  /// Worker 0's output, the claim's.
  fn output(&self) -> Vec<G> {
    self.executed[0]
      .as_ref()
      .expect("worker 0 executed with the first group")
      .output
      .clone()
  }
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
      |toplevel, fun_idx, input, io_buffer| {
        ixvm_codegen::aiur_ixvm_runner::execute_ixvm(
          toplevel, fun_idx, input, io_buffer,
        )
      },
    );

    build_prove_result(&claim, proof, &io_buffer).into()
  })
}

/// `Bytecode.Toplevel.executeMultiStark`: run the MultiStark recursive
/// verifier over proof-advice/vk/claims byte blobs. The proof blob is the
/// verified native transport produced by `proof_to_advice_bytes`. The IO advice buffer
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
/// child proof-advice/claim/tree/path blobs. Each proof is verified and
/// serialized with `proof_to_advice_bytes` before crossing this boundary. The native builder expands the compact keyed
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
/// verifier over proof-advice/vk/claims byte blobs. The proof blob uses the
/// native serialized transport returned by `proof_to_advice_bytes`. Buffer construction
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
