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
    LeanAiurCommitmentParameters, LeanAiurFriParameters, LeanAiurToplevel,
  },
};
use aiur::{
  G,
  execute::{IOBuffer, IOKeyInfo, QueryRecord},
  synthesis::{AiurProof, AiurSystem},
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

/// `Bytecode.Toplevel.execute`: runs execution only (no proof) and returns
/// `Except String (Array G × (Array G × Array (Array G × IOKeyInfo)) × Array (Nat × Nat))`.
/// The trailing `Array (Nat × Nat)` is one `(uniqueRows, totalHits)` pair per
/// function circuit followed by one per memory size.
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

  // Build per-circuit (unique_rows, total_hits) pairs:
  // one per function, then one per memory size. `unique_rows` is the trace
  // height (number of distinct queries); `total_hits` is the sum of
  // multiplicities (how often those rows were hit).
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
  let lean_query_counts = {
    let arr = LeanArray::alloc(query_counts.len());
    for (i, &(rows, hits)) in query_counts.iter().enumerate() {
      let pair =
        LeanProd::new(LeanOwned::box_usize(rows), LeanOwned::box_usize(hits));
      arr.set(i, pair);
    }
    arr
  };

  let lean_io = build_lean_io_buffer(&io_buffer);
  // (Array G, (Array G × Array (Array G × IOKeyInfo), Array (Nat × Nat)))
  let io_counts = LeanProd::new(lean_io, lean_query_counts);
  let result = LeanProd::new(build_g_array(&output), io_counts);
  LeanExcept::ok(result)
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

  // Same query-count summarisation as `rs_aiur_toplevel_execute`.
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
  let lean_query_counts = {
    let arr = LeanArray::alloc(query_counts.len());
    for (i, &(rows, hits)) in query_counts.iter().enumerate() {
      let pair =
        LeanProd::new(LeanOwned::box_usize(rows), LeanOwned::box_usize(hits));
      arr.set(i, pair);
    }
    arr
  };

  let lean_io = build_lean_io_buffer(&io_buffer);
  let io_counts = LeanProd::new(lean_io, lean_query_counts);
  let result = LeanProd::new(build_g_array(&output), io_counts);
  LeanExcept::ok(result)
}

/// `AiurSystem.prove`: runs the prover and returns
/// `Array G × Proof × Array G × Array (Array G × IOKeyInfo)`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanOwned {
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let args = args.map(|x| lean_unbox_g(&x));
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (claim, proof) =
    aiur_system_obj.get().prove(fun_idx, &args, &mut io_buffer);

  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  let lean_io = build_lean_io_buffer(&io_buffer);
  // Proof × Array G × Array (Array G × IOKeyInfo)
  let proof_io_tuple = LeanProd::new(lean_proof, lean_io);
  // Array G × Proof × Array G × Array (Array G × IOKeyInfo)
  let result = LeanProd::new(build_g_array(&claim), proof_io_tuple);
  result.into()
}

// =============================================================================
// EnvHandle constructors + with-env FFIs (PLAN.md "EnvHandle redesign")
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
/// `Array (Nat × Nat)` of `(unique_rows, total_hits)` pairs, one per
/// function circuit followed by one per memory size. Mirrors the
/// summary code used by every check/prove FFI.
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
    let pair =
      LeanProd::new(LeanOwned::box_usize(rows), LeanOwned::box_usize(hits));
    arr.set(i, pair);
  }
  arr
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
      .chunks_exact(32)
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

  let lean_query_counts = build_query_counts_array(&query_record, &toplevel);
  let lean_io = build_lean_io_buffer(&io_buffer);
  let io_counts = LeanProd::new(lean_io, lean_query_counts);
  let result = LeanProd::new(build_g_array(&output), io_counts);
  LeanExcept::ok(result)
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

  let lean_query_counts = build_query_counts_array(&query_record, &toplevel);
  let lean_io = build_lean_io_buffer(&io_buffer);
  let io_counts = LeanProd::new(lean_io, lean_query_counts);
  let result = LeanProd::new(build_g_array(&output), io_counts);
  LeanExcept::ok(result)
}

/// `AiurSystem.proveAddrWithEnv`: per-claim prove against a
/// Rust-owned `EnvHandle`. Returns `(claim_bytes, proof, ioBuffer)`
/// — the claim's wire bytes are serialized via `ixon::Claim::put`
/// so Lean can deserialize directly into `Ix.Claim` without
/// reconstructing it from the target addr.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove_addr_with_env(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  env_handle: LeanExternal<
    ixvm_codegen::env_handle::EnvHandle,
    LeanBorrowed<'_>,
  >,
  addr_bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let addr = match decode_addr(&addr_bytes) {
    Ok(a) => a,
    Err(e) => return LeanExcept::error_string(&e),
  };
  let env = &env_handle.get().env;

  let (claim, input, mut io_buffer) =
    match ixvm_codegen::aiur_ixvm_witness::build_claim_check_witness(env, &addr)
    {
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

  let mut claim_bytes: Vec<u8> = Vec::new();
  claim.put(&mut claim_bytes);
  let lean_claim_bytes = LeanByteArray::from_bytes(&claim_bytes);
  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  let lean_io = build_lean_io_buffer(&io_buffer);
  let proof_io = LeanProd::new(lean_proof, lean_io);
  let result = LeanProd::new(lean_claim_bytes, proof_io);
  LeanExcept::ok(result)
}

/// `AiurSystem.shardProveWithEnv`: per-shard prove against a
/// Rust-owned `EnvHandle`. Same `(claim_bytes, proof, ioBuffer)`
/// return shape as `proveAddrWithEnv`.
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

  let mut claim_bytes: Vec<u8> = Vec::new();
  claim.put(&mut claim_bytes);
  let lean_claim_bytes = LeanByteArray::from_bytes(&claim_bytes);
  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  let lean_io = build_lean_io_buffer(&io_buffer);
  let proof_io = LeanProd::new(lean_proof, lean_io);
  let result = LeanProd::new(lean_claim_bytes, proof_io);
  LeanExcept::ok(result)
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
) -> LeanOwned {
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let args = args.map(|x| lean_unbox_g(&x));
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (claim, proof) = aiur_system_obj.get().prove_ixvm(
    fun_idx,
    &args,
    &mut io_buffer,
    ixvm_codegen::aiur_ixvm_runner::execute_ixvm,
  );

  let lean_proof: LeanOwned =
    LeanExternal::alloc(&AIUR_PROOF_CLASS, proof).into();
  let lean_io = build_lean_io_buffer(&io_buffer);
  let proof_io_tuple = LeanProd::new(lean_proof, lean_io);
  let result = LeanProd::new(build_g_array(&claim), proof_io_tuple);
  result.into()
}

// =============================================================================
// Helpers
// =============================================================================

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

/// Build a Lean
/// `Array (G × Array G) × Array ((G × Array G) × IOKeyInfo)` from an
/// `IOBuffer`. The first array enumerates per-channel data arenas;
/// the second is the channel-keyed info map.
fn build_lean_io_buffer(io_buffer: &IOBuffer) -> LeanOwned {
  let lean_io_data = {
    let arr = LeanArray::alloc(io_buffer.data.len());
    for (i, (channel, arena)) in io_buffer.data.iter().enumerate() {
      let channel_box = LeanOwned::box_u64(channel.as_canonical_u64());
      let arena_arr = build_g_array(arena);
      let elt = LeanProd::new(channel_box, arena_arr);
      arr.set(i, elt);
    }
    arr
  };
  let lean_io_map = {
    let arr = LeanArray::alloc(io_buffer.map.len());
    for (i, ((channel, key), info)) in io_buffer.map.iter().enumerate() {
      let channel_box = LeanOwned::box_u64(channel.as_canonical_u64());
      let key_arr = build_g_array(key);
      let channel_key = LeanProd::new(channel_box, key_arr);
      let key_info = LeanProd::new(
        LeanOwned::box_usize(info.idx),
        LeanOwned::box_usize(info.len),
      );
      let map_elt = LeanProd::new(channel_key, key_info);
      arr.set(i, map_elt);
    }
    arr
  };
  let io_tuple = LeanProd::new(lean_io_data, lean_io_map);
  io_tuple.into()
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
// SP1 proof compression (feature `sp1`)
// =============================================================================

/// `Aiur.sp1CompressAiurProof : @& ByteArray → @& ByteArray → @& ByteArray →
/// @& FriParameters → @& String → @& String → Except String Unit`
///
/// Verifies an Aiur proof inside the SP1 zkVM guest and produces a recursive
/// SP1 proof of that verification (see `sp1-compress/`). Arguments are the
/// verifying-key bytes (`vk_codec` format), the claim as canonical u64 LE
/// Goldilocks elements, and the `Proof::to_bytes` bytes. `mode` is one of
/// `execute|core|compressed|groth16|plonk`; `output` is the path the SP1
/// proof is saved to (`""` = don't save).
///
/// Without the `sp1` cargo feature (lake: `IX_SP1=1`) this is a stub that
/// returns an error, so the Lean binding always links.
#[unsafe(no_mangle)]
extern "C" fn rs_sp1_compress_aiur_proof(
  vk_bytes: LeanByteArray<LeanBorrowed<'_>>,
  claim_bytes: LeanByteArray<LeanBorrowed<'_>>,
  proof_bytes: LeanByteArray<LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  mode: LeanString<LeanBorrowed<'_>>,
  output: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  #[cfg(feature = "sp1")]
  {
    let fri = decode_fri_parameters(&fri_parameters);
    let mode = match mode.as_str().parse::<sp1_compress_host::Mode>() {
      Ok(m) => m,
      Err(e) => return LeanExcept::error_string(&e),
    };
    let output = match output.as_str() {
      "" => None,
      s => Some(std::path::PathBuf::from(s)),
    };
    match sp1_compress_host::run_sp1_blocking(
      vk_bytes.as_bytes().to_vec(),
      claim_bytes.as_bytes().to_vec(),
      proof_bytes.as_bytes().to_vec(),
      &fri,
      mode,
      output.as_deref(),
    ) {
      Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
      Err(e) => LeanExcept::error_string(&format!("{e:#}")),
    }
  }
  #[cfg(not(feature = "sp1"))]
  {
    let _ =
      (&vk_bytes, &claim_bytes, &proof_bytes, &fri_parameters, &mode, &output);
    LeanExcept::error_string(
      "ix was built without SP1 support; rebuild with `IX_SP1=1 lake build`",
    )
  }
}
