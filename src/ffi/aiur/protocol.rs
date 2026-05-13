use multi_stark::{
  p3_field::{Field, PrimeField64},
  prover::Proof,
  types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::sync::LazyLock;

use lean_ffi::object::{
  ExternalClass, LeanArray, LeanBorrowed, LeanByteArray, LeanExcept,
  LeanExternal, LeanNat, LeanOwned, LeanProd, LeanRef,
};

use crate::{
  aiur::{
    G,
    execute::{IOBuffer, IOKeyInfo},
    synthesis::AiurSystem,
  },
  ffi::aiur::{
    lean_unbox_g, lean_unbox_nat_as_usize, toplevel::decode_toplevel,
  },
  lean::{
    LeanAiurCommitmentParameters, LeanAiurFriParameters, LeanAiurToplevel,
  },
};

// =============================================================================
// External class registration
// =============================================================================

static AIUR_PROOF_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<Proof>);
static AIUR_SYSTEM_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<AiurSystem>);

// =============================================================================
// Lean FFI functions
// =============================================================================

/// `Aiur.Proof.toBytes : @& Proof → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_bytes(
  proof_obj: LeanExternal<Proof, LeanBorrowed<'_>>,
) -> LeanByteArray<LeanOwned> {
  let bytes = proof_obj.get().to_bytes().expect("Serialization error");
  LeanByteArray::from_bytes(&bytes)
}

/// `Aiur.Proof.ofBytes : @& ByteArray → Proof`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_of_bytes(
  byte_array: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<Proof, LeanOwned> {
  let proof =
    Proof::from_bytes(byte_array.as_bytes()).expect("Deserialization error");
  LeanExternal::alloc(&AIUR_PROOF_CLASS, proof)
}

/// `AiurSystem.build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_build(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  commitment_parameters: LeanAiurCommitmentParameters<LeanBorrowed<'_>>,
) -> LeanExternal<AiurSystem, LeanOwned> {
  let system = AiurSystem::build(
    decode_toplevel(&toplevel),
    decode_commitment_parameters(&commitment_parameters),
  );
  LeanExternal::alloc(&AIUR_SYSTEM_CLASS, system)
}

/// `AiurSystem.verify : @& AiurSystem → @& FriParameters → @& Array G → @& Proof → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_verify(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  claim: LeanArray<LeanBorrowed<'_>>,
  proof_obj: LeanExternal<Proof, LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let fri_parameters = decode_fri_parameters(&fri_parameters);
  let claim = claim.map(|x| lean_unbox_g(&x));
  match aiur_system_obj.get().verify(fri_parameters, &claim, proof_obj.get()) {
    Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
    Err(err) => LeanExcept::error_string(&format!("{err:?}")),
  }
}

/// `Bytecode.Toplevel.execute`: runs execution only (no proof) and returns
/// `Array G × Array G × Array (Array G × IOKeyInfo)`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_toplevel_execute(
  toplevel: LeanAiurToplevel<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanOwned {
  let toplevel = decode_toplevel(&toplevel);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (query_record, output) =
    toplevel.execute(fun_idx, args.map(|x| lean_unbox_g(&x)), &mut io_buffer);

  // Build query counts: one per function, then one per memory size
  let mut query_counts: Vec<usize> = Vec::with_capacity(
    query_record.function_queries.len() + toplevel.memory_sizes.len(),
  );
  for queries in &query_record.function_queries {
    let count =
      queries.iter().filter(|(_, res)| !res.multiplicity.is_zero()).count();
    query_counts.push(count);
  }
  for size in &toplevel.memory_sizes {
    let count = query_record.memory_queries.get(size).map_or(0, |q| {
      q.iter().filter(|(_, res)| !res.multiplicity.is_zero()).count()
    });
    query_counts.push(count);
  }
  let lean_query_counts = {
    let arr = LeanArray::alloc(query_counts.len());
    for (i, &count) in query_counts.iter().enumerate() {
      arr.set(i, LeanOwned::box_usize(count));
    }
    arr
  };

  let lean_io = build_lean_io_buffer(&io_buffer);
  // (Array G, (Array G × Array (Array G × IOKeyInfo), Array Nat))
  let io_counts = LeanProd::new(lean_io, lean_query_counts);
  let result = LeanProd::new(build_g_array(&output), io_counts);
  result.into()
}

/// `AiurSystem.prove`: runs the prover and returns
/// `Array G × Proof × Array G × Array (Array G × IOKeyInfo)`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
  aiur_system_obj: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  fri_parameters: LeanAiurFriParameters<LeanBorrowed<'_>>,
  fun_idx: LeanNat<LeanBorrowed<'_>>,
  args: LeanArray<LeanBorrowed<'_>>,
  io_data_arr: LeanArray<LeanBorrowed<'_>>,
  io_map_arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanOwned {
  let fri_parameters = decode_fri_parameters(&fri_parameters);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx.inner());
  let args = args.map(|x| lean_unbox_g(&x));
  let mut io_buffer = decode_io_buffer(&io_data_arr, &io_map_arr);

  let (claim, proof) =
    aiur_system_obj.get().prove(fri_parameters, fun_idx, &args, &mut io_buffer);

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
  let data = io_data_arr.map(|x| lean_unbox_g(&x));
  let map = decode_io_buffer_map(io_map_arr);
  IOBuffer { data, map }
}

/// Build a Lean `Array G × Array (Array G × IOKeyInfo)` from an `IOBuffer`.
fn build_lean_io_buffer(io_buffer: &IOBuffer) -> LeanOwned {
  let lean_io_data = build_g_array(&io_buffer.data);
  let lean_io_map = {
    let arr = LeanArray::alloc(io_buffer.map.len());
    for (i, (key, info)) in io_buffer.map.iter().enumerate() {
      let key_arr = build_g_array(key);
      let key_info = LeanProd::new(
        LeanOwned::box_usize(info.idx),
        LeanOwned::box_usize(info.len),
      );
      let map_elt = LeanProd::new(key_arr, key_info);
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

fn decode_io_buffer_map(
  arr: &LeanArray<LeanBorrowed<'_>>,
) -> FxHashMap<Vec<G>, IOKeyInfo> {
  let mut map = FxHashMap::with_capacity_and_hasher(arr.len(), FxBuildHasher);
  for elt in arr.iter() {
    let pair = elt.as_ctor();
    let key = pair.get(0).as_array().map(|x| lean_unbox_g(&x));
    let info_ctor = pair.get(1).as_ctor();
    let info = IOKeyInfo {
      idx: lean_unbox_nat_as_usize(&info_ctor.get(0)),
      len: lean_unbox_nat_as_usize(&info_ctor.get(1)),
    };
    map.insert(key, info);
  }
  map
}
