use multi_stark::{
  p3_field::PrimeField64,
  prover::Proof,
  types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::sync::OnceLock;

use lean_ffi::object::{
  ExternalClass, LeanArray, LeanByteArray, LeanCtor, LeanExcept, LeanExternal,
  LeanObject,
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
};

// =============================================================================
// External class registration (OnceLock pattern)
// =============================================================================

static AIUR_PROOF_CLASS: OnceLock<ExternalClass> = OnceLock::new();
static AIUR_SYSTEM_CLASS: OnceLock<ExternalClass> = OnceLock::new();

fn proof_class() -> &'static ExternalClass {
  AIUR_PROOF_CLASS.get_or_init(ExternalClass::register_with_drop::<Proof>)
}

fn system_class() -> &'static ExternalClass {
  AIUR_SYSTEM_CLASS.get_or_init(ExternalClass::register_with_drop::<AiurSystem>)
}

// =============================================================================
// Lean FFI functions
// =============================================================================

/// `Aiur.Proof.toBytes : @& Proof → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_bytes(
  proof_obj: LeanExternal<Proof>,
) -> LeanByteArray {
  let bytes = proof_obj.get().to_bytes().expect("Serialization error");
  LeanByteArray::from_bytes(&bytes)
}

/// `Aiur.Proof.ofBytes : @& ByteArray → Proof`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_of_bytes(
  byte_array: LeanByteArray,
) -> LeanExternal<Proof> {
  let proof =
    Proof::from_bytes(byte_array.as_bytes()).expect("Deserialization error");
  LeanExternal::alloc(proof_class(), proof)
}

/// `AiurSystem.build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_build(
  toplevel: LeanObject,
  commitment_parameters: LeanObject,
) -> LeanExternal<AiurSystem> {
  let system = AiurSystem::build(
    decode_toplevel(toplevel),
    lean_ptr_to_commitment_parameters(commitment_parameters),
  );
  LeanExternal::alloc(system_class(), system)
}

/// `AiurSystem.verify : @& AiurSystem → @& FriParameters → @& Array G → @& Proof → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_verify(
  aiur_system_obj: LeanExternal<AiurSystem>,
  fri_parameters: LeanObject,
  claim: LeanObject,
  proof_obj: LeanExternal<Proof>,
) -> LeanExcept {
  let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
  let claim = claim.as_array().map(lean_unbox_g);
  match aiur_system_obj.get().verify(fri_parameters, &claim, proof_obj.get()) {
    Ok(()) => LeanExcept::ok(LeanObject::box_usize(0)),
    Err(err) => LeanExcept::error_string(&format!("{err:?}")),
  }
}

/// `AiurSystem.prove`: runs the prover and returns
/// `Array G × Proof × Array G × Array (Array G × IOKeyInfo)`
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
  aiur_system_obj: LeanExternal<AiurSystem>,
  fri_parameters: LeanObject,
  fun_idx: LeanObject,
  args: LeanObject,
  io_data_arr: LeanObject,
  io_map_arr: LeanObject,
) -> LeanObject {
  let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx);
  let args = args.as_array().map(lean_unbox_g);
  let io_data = io_data_arr.as_array().map(lean_unbox_g);
  let io_map = lean_array_to_io_buffer_map(io_map_arr);
  let mut io_buffer = IOBuffer { data: io_data, map: io_map };

  let (claim, proof) =
    aiur_system_obj.get().prove(fri_parameters, fun_idx, &args, &mut io_buffer);

  // claim: Array G
  let lean_claim = build_g_array(&claim);

  // proof: Proof (external object)
  let lean_proof = *LeanExternal::alloc(proof_class(), proof);

  // io_data: Array G
  let lean_io_data = build_g_array(&io_buffer.data);

  // io_map: Array (Array G × IOKeyInfo)
  let lean_io_map = {
    let arr = LeanArray::alloc(io_buffer.map.len());
    for (i, (key, info)) in io_buffer.map.iter().enumerate() {
      let key_arr = build_g_array(key);
      // IOKeyInfo ctor (tag 0, 2 object fields)
      let key_info = LeanCtor::alloc(0, 2, 0);
      key_info.set(0, LeanObject::box_usize(info.idx));
      key_info.set(1, LeanObject::box_usize(info.len));
      // (Array G × IOKeyInfo) tuple
      let map_elt = LeanCtor::alloc(0, 2, 0);
      map_elt.set(0, key_arr);
      map_elt.set(1, *key_info);
      arr.set(i, *map_elt);
    }
    *arr
  };

  // Build nested tuple:
  // Array G × Array (Array G × IOKeyInfo)
  let io_tuple = LeanCtor::alloc(0, 2, 0);
  io_tuple.set(0, lean_io_data);
  io_tuple.set(1, lean_io_map);
  // Proof × Array G × Array (Array G × IOKeyInfo)
  let proof_io_tuple = LeanCtor::alloc(0, 2, 0);
  proof_io_tuple.set(0, lean_proof);
  proof_io_tuple.set(1, *io_tuple);
  // Array G × Proof × Array G × Array (Array G × IOKeyInfo)
  let result = LeanCtor::alloc(0, 2, 0);
  result.set(0, lean_claim);
  result.set(1, *proof_io_tuple);
  *result
}

// =============================================================================
// Helpers
// =============================================================================

/// Build a Lean `Array G` from a slice of field elements.
fn build_g_array(values: &[G]) -> LeanObject {
  let arr = LeanArray::alloc(values.len());
  for (i, g) in values.iter().enumerate() {
    arr.set(i, LeanObject::box_u64(g.as_canonical_u64()));
  }
  *arr
}

fn lean_ptr_to_commitment_parameters(obj: LeanObject) -> CommitmentParameters {
  CommitmentParameters { log_blowup: lean_unbox_nat_as_usize(obj) }
}

fn lean_ctor_to_fri_parameters(obj: LeanObject) -> FriParameters {
  let ctor = obj.as_ctor();
  FriParameters {
    log_final_poly_len: lean_unbox_nat_as_usize(ctor.get(0)),
    num_queries: lean_unbox_nat_as_usize(ctor.get(1)),
    commit_proof_of_work_bits: lean_unbox_nat_as_usize(ctor.get(2)),
    query_proof_of_work_bits: lean_unbox_nat_as_usize(ctor.get(3)),
  }
}

fn lean_array_to_io_buffer_map(
  obj: LeanObject,
) -> FxHashMap<Vec<G>, IOKeyInfo> {
  let arr = obj.as_array();
  let mut map = FxHashMap::with_capacity_and_hasher(arr.len(), FxBuildHasher);
  for elt in arr.iter() {
    let pair = elt.as_ctor();
    let key = pair.get(0).as_array().map(lean_unbox_g);
    let info_ctor = pair.get(1).as_ctor();
    let info = IOKeyInfo {
      idx: lean_unbox_nat_as_usize(info_ctor.get(0)),
      len: lean_unbox_nat_as_usize(info_ctor.get(1)),
    };
    map.insert(key, info);
  }
  map
}
