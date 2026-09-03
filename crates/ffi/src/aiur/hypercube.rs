//! The SP1 Hypercube proving backend over KoalaBear, as a Lean FFI surface.
//!
//! Mirrors `protocol.rs`'s multi-stark surface at the minimum the
//! benchmark/pipeline needs: build a [`HypercubeSystem`] from a (KoalaBear-
//! profile) bytecode toplevel and an entry function, prove a call, verify a
//! proof blob. Proof blobs carry `(vk, shard proofs)` bincoded together, so
//! verification needs only the system and the expected claim.

use std::sync::LazyLock;

use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExcept,
  LeanExternal, LeanNat, LeanOwned, LeanProd,
};
use multi_stark::p3_field::PrimeField64;
use rustc_hash::{FxBuildHasher, FxHashMap};

use aiur::{
  bytecode::Toplevel,
  execute::{IOBuffer, IOKeyInfo},
};
use aiur_hypercube::{
  AiurProof, AiurVerifyingKey, FrontendField as KB, ProverParams,
  ShardingParams, ToplevelMachine, verify,
};

use crate::{
  aiur::{
    lean_unbox_field_in, lean_unbox_nat_as_usize,
    protocol::ffi_catch_unwind_except, toplevel::decode_toplevel_in,
  },
  lean::LeanAiurToplevel,
};

/// A Hypercube proving system: the KoalaBear bytecode toplevel and the
/// machine built for one entry function.
pub struct HypercubeSystem {
  toplevel: Toplevel<KB>,
  machine: ToplevelMachine,
  params: ProverParams,
  sharding: ShardingParams,
}

static HYPERCUBE_SYSTEM_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<HypercubeSystem>);

fn decode_io_buffer_kb(
  io_data_arr: &LeanArray<LeanBorrowed<'_>>,
  io_map_arr: &LeanArray<LeanBorrowed<'_>>,
) -> IOBuffer<KB> {
  let mut data =
    FxHashMap::with_capacity_and_hasher(io_data_arr.len(), FxBuildHasher);
  for elt in io_data_arr.iter() {
    let pair = elt.as_ctor();
    let channel = lean_unbox_field_in::<KB>(&pair.get(0));
    let arena = pair.get(1).as_array().map(|x| lean_unbox_field_in::<KB>(&x));
    data.insert(channel, arena);
  }
  let mut map =
    FxHashMap::with_capacity_and_hasher(io_map_arr.len(), FxBuildHasher);
  for elt in io_map_arr.iter() {
    let pair = elt.as_ctor();
    let channel_key = pair.get(0).as_ctor();
    let channel = lean_unbox_field_in::<KB>(&channel_key.get(0));
    let key =
      channel_key.get(1).as_array().map(|x| lean_unbox_field_in::<KB>(&x));
    let info_ctor = pair.get(1).as_ctor();
    let info = IOKeyInfo {
      idx: lean_unbox_nat_as_usize(&info_ctor.get(0)),
      len: lean_unbox_nat_as_usize(&info_ctor.get(1)),
    };
    map.insert((channel, key), info);
  }
  IOBuffer { data, map }
}

/// Build a Lean `Array G` from KoalaBear values (canonical `u64`s; every
/// KoalaBear canonical value is below the Goldilocks modulus, so the Lean
/// `Aiur.G` subtype holds them).
fn build_kb_array(values: &[KB]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(values.len());
  for (i, v) in values.iter().enumerate() {
    arr.set(i, LeanOwned::box_u64(v.as_canonical_u64()));
  }
  arr
}

fn bincode_config() -> bincode::config::Configuration {
  bincode::config::standard()
}

/// `ProverParams`, overridable per process for benchmarks: `IX_HC_LOG_BLOWUP`,
/// `IX_HC_LOG_STACKING`, `IX_HC_MAX_LOG_ROWS`.
fn prover_params_from_env() -> ProverParams {
  let mut p = ProverParams::default();
  let get = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<u32>().ok());
  if let Some(v) = get("IX_HC_LOG_BLOWUP") {
    p.log_blowup = v as usize;
  }
  if let Some(v) = get("IX_HC_LOG_STACKING") {
    p.log_stacking_height = v;
  }
  if let Some(v) = get("IX_HC_MAX_LOG_ROWS") {
    p.max_log_row_count = v as usize;
  }
  p
}

/// `ShardingParams` from the environment: `IX_HC_SHARD_CELLS` caps a shard's
/// splittable main-trace cells (default: everything in one shard), and the
/// row cap follows `IX_HC_MAX_LOG_ROWS`.
fn sharding_params_from_env(prover: &ProverParams) -> ShardingParams {
  let mut s = ShardingParams {
    max_rows: 1 << prover.max_log_row_count,
    ..ShardingParams::default()
  };
  if let Some(v) = std::env::var("IX_HC_SHARD_CELLS")
    .ok()
    .and_then(|v| v.parse::<usize>().ok())
  {
    s.max_cells = v;
  }
  s
}

/// `Aiur.Hypercube.build : @& Bytecode.Toplevel → @& Bytecode.FunIdx →
/// Except String HypercubeSystem`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_hypercube_build(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("Hypercube.build", || {
    let toplevel: Toplevel<KB> = decode_toplevel_in::<KB>(&toplevel);
    let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
    let machine = match ToplevelMachine::build(&toplevel, fun_idx) {
      Ok(m) => m,
      Err(e) => {
        return LeanExcept::error_string(&format!("machine build: {e}"));
      },
    };
    let params = prover_params_from_env();
    let sharding = sharding_params_from_env(&params);
    let system = HypercubeSystem { toplevel, machine, params, sharding };
    LeanExcept::ok(LeanExternal::alloc(&HYPERCUBE_SYSTEM_CLASS, system))
  })
}

/// `Aiur.Hypercube.prove` : executes the entry function and proves the
/// execution. Returns `(claim, proofBlob)`; the blob is `(vk, proof)`
/// bincoded.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_hypercube_prove(
  system_obj: LeanExternal<HypercubeSystem, LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("Hypercube.prove", || {
    let system = system_obj.get();
    let args = args.map(|x| lean_unbox_field_in::<KB>(&x));
    let mut io_buffer = decode_io_buffer_kb(&io_data_arr, &io_map_arr);
    let (claim, vk, proof) = match system.machine.execute_and_prove(
      &system.toplevel,
      &args,
      &mut io_buffer,
      system.params,
      system.sharding,
    ) {
      Ok(t) => t,
      Err(e) => return LeanExcept::error_string(&e.to_string()),
    };
    if std::env::var_os("IX_HC_DEBUG").is_some() {
      eprintln!("hypercube: proved {} shard(s)", proof.shard_proofs.len());
    }
    let blob =
      match bincode::serde::encode_to_vec(&(vk, proof), bincode_config()) {
        Ok(b) => b,
        Err(e) => {
          return LeanExcept::error_string(&format!("proof encode: {e}"));
        },
      };
    LeanExcept::ok(LeanProd::new(
      build_kb_array(&claim),
      LeanByteArray::from_bytes(&blob),
    ))
  })
}

/// `Aiur.Hypercube.verify` : verifies a proof blob against the system and
/// the expected claim (checked as the proof's public-value prefix).
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_hypercube_verify(
  system_obj: LeanExternal<HypercubeSystem, LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  blob: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  ffi_catch_unwind_except("Hypercube.verify", || {
    let system = system_obj.get();
    let claim = claim.map(|x| lean_unbox_field_in::<KB>(&x));
    let (vk, proof): (AiurVerifyingKey, AiurProof) =
      match bincode::serde::decode_from_slice(blob.as_bytes(), bincode_config())
      {
        Ok((t, _)) => t,
        Err(e) => {
          return LeanExcept::error_string(&format!("proof decode: {e}"));
        },
      };
    // Verification returns the claim-shard's verified claim; it must match
    // the expected one.
    match verify(system.machine.machine(), system.params, &vk, &proof) {
      Ok(verified) => {
        let expected: Vec<_> = claim
          .iter()
          .map(|c| aiur_hypercube::expr::convert_element(*c))
          .collect();
        if verified == expected {
          LeanExcept::ok(LeanOwned::box_usize(0))
        } else {
          LeanExcept::error_string("claim does not match the verified claim")
        }
      },
      Err(e) => LeanExcept::error_string(&format!("{e}")),
    }
  })
}
