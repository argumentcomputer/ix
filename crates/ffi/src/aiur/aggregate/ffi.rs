//! Aggregation FFI; keeps Lean marshalling outside the native controller.

use crate::aiur::protocol::{
  AIUR_PROOF_CLASS, build_g_array, build_query_counts_array,
};
use crate::aiur::{
  lean_unbox_g, lean_unbox_nat_as_usize, toplevel::decode_toplevel,
};
use crate::lean::LeanAiurToplevel;
use aiur::synthesis::AiurSystem;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanExcept, LeanExternal, LeanNat,
  LeanOwned, LeanProd,
};

use super::{RunConfig, expected_from_manifest, panic_text, run};
use crate::lean::LeanAiurAggregateExpected;
use aiur::execute::IOBuffer;
use ix_kernel::shard::ShardManifest;
use ixvm_codegen::env_handle::EnvHandle;
use lean_ffi::object::LeanString;
use std::{fs, path::Path};

/// Native manifest/environment binding for `ix verify --aggregate --ixes`.
/// The returned claim comes from the exact statement builder used by Stage 2,
/// after a full constant/shard/assumption audit.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_aggregate_expected(
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let manifest_bytes =
      fs::read(Path::new(manifest_path.as_str())).map_err(|error| {
        format!("read manifest {}: {error}", manifest_path.as_str())
      })?;
    let manifest = ShardManifest::from_bytes(&manifest_bytes)
      .map_err(|error| format!("manifest parse failed: {error}"))?;
    expected_from_manifest(
      &env_handle.get().env,
      &manifest,
      lean_unbox_nat_as_usize(structural_above.inner()),
    )
  }));
  match result {
    Ok(Ok((statement, constant_count))) => {
      let expected = LeanAiurAggregateExpected::alloc(0);
      expected.set_obj(0, LeanByteArray::from_bytes(&statement.claim_bytes));
      expected.set_obj(1, LeanOwned::box_usize(constant_count));
      LeanExcept::ok(expected)
    },
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "native aggregate verification setup panicked: {}",
      panic_text(&payload)
    )),
  }
}

/// Production FFI called once after Lean has compiled the IxVM and ixAggr
/// systems. Proof addresses are newline-separated to keep the ABI flat.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_stage2_aggregate(
  ixvm_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  proof_hexes: LeanString<LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  jobs: LeanNat<LeanBorrowed<'_>>,
  ram_budget_bytes: LeanNat<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
  reprove_slot_code: LeanNat<LeanBorrowed<'_>>,
  direct_joins: bool,
  plan_only: bool,
  cache_fri_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_cache: bool,
  write_outputs: bool,
) -> LeanExcept<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let reprove_slot =
      lean_unbox_nat_as_usize(reprove_slot_code.inner()).checked_sub(1);
    run(RunConfig {
      ixvm_system: ixvm_system.get(),
      aggr_system: aggr_system.get(),
      env_handle: env_handle.get(),
      manifest_path: Path::new(manifest_path.as_str()),
      proof_hexes: proof_hexes.as_str(),
      verify_idx: lean_unbox_nat_as_usize(verify_idx.inner()),
      aggr_idx: lean_unbox_nat_as_usize(aggr_idx.inner()),
      jobs: lean_unbox_nat_as_usize(jobs.inner()),
      ram_budget_bytes: lean_unbox_nat_as_usize(ram_budget_bytes.inner()),
      structural_above: lean_unbox_nat_as_usize(structural_above.inner()),
      reprove_slot,
      direct_joins,
      plan_only,
      cache_fri_bytes: cache_fri_bytes.as_bytes(),
      use_cache,
      write_outputs,
    })
  }));
  match result {
    Ok(Ok(address)) => LeanExcept::ok(LeanString::new(&address)),
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "native Stage 2 orchestration panicked: {}",
      panic_text(&payload)
    )),
  }
}

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
