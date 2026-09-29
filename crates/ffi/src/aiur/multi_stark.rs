//! Generic Multi-STARK verifier FFI.

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

use super::protocol::ffi_catch_unwind;

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
