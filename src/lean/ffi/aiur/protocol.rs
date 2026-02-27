use multi_stark::{
  p3_field::PrimeField64,
  prover::Proof,
  types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::ffi::c_void;
use std::sync::OnceLock;

use crate::{
  aiur::{
    G,
    execute::{IOBuffer, IOKeyInfo},
    synthesis::AiurSystem,
  },
  lean::{
    array::LeanArrayObject,
    as_mut_unsafe, as_ref_unsafe,
    ctor::LeanCtorObject,
    external::LeanExternalObject,
    ffi::{
      ExternalClassPtr,
      aiur::{
        lean_unbox_g, lean_unbox_nat_as_usize, toplevel::lean_ctor_to_toplevel,
      },
      drop_raw, to_raw,
    },
    lean_alloc_array, lean_alloc_ctor, lean_alloc_external, lean_alloc_sarray,
    lean_array_set_core, lean_box_fn, lean_box_u64, lean_ctor_set,
    lean_except_error_string, lean_except_ok, lean_register_external_class,
    noop_foreach,
    sarray::LeanSArrayObject,
  },
};

// =============================================================================
// External class registration (OnceLock pattern)
// =============================================================================

static AIUR_PROOF_CLASS: OnceLock<ExternalClassPtr> = OnceLock::new();
static AIUR_SYSTEM_CLASS: OnceLock<ExternalClassPtr> = OnceLock::new();

fn get_aiur_proof_class() -> *mut c_void {
  AIUR_PROOF_CLASS
    .get_or_init(|| {
      ExternalClassPtr(unsafe {
        lean_register_external_class(aiur_proof_finalizer, noop_foreach)
      })
    })
    .0
}

fn get_aiur_system_class() -> *mut c_void {
  AIUR_SYSTEM_CLASS
    .get_or_init(|| {
      ExternalClassPtr(unsafe {
        lean_register_external_class(aiur_system_finalizer, noop_foreach)
      })
    })
    .0
}

extern "C" fn aiur_proof_finalizer(ptr: *mut c_void) {
  drop_raw(ptr as *mut Proof);
}

extern "C" fn aiur_system_finalizer(ptr: *mut c_void) {
  drop_raw(ptr as *mut AiurSystem);
}

// =============================================================================
// Lean FFI functions
// =============================================================================

/// `Aiur.Proof.toBytes : @& Proof → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn c_rs_aiur_proof_to_bytes(
  proof_obj: *const c_void,
) -> *mut c_void {
  let external: &LeanExternalObject = as_ref_unsafe(proof_obj.cast());
  let proof: &Proof = as_ref_unsafe(external.cast_data());
  let bytes = proof.to_bytes().expect("Serialization error");
  let len = bytes.len();
  let arr_ptr = unsafe { lean_alloc_sarray(1, len, len) };
  let arr: &mut LeanSArrayObject = as_mut_unsafe(arr_ptr.cast());
  arr.set_data(&bytes);
  arr_ptr
}

/// `Aiur.Proof.ofBytes : @& ByteArray → Proof`
#[unsafe(no_mangle)]
extern "C" fn c_rs_aiur_proof_of_bytes(
  byte_array: &LeanSArrayObject,
) -> *mut c_void {
  let proof =
    Proof::from_bytes(byte_array.data()).expect("Deserialization error");
  let ptr = to_raw(proof) as *mut c_void;
  unsafe { lean_alloc_external(get_aiur_proof_class(), ptr) }
}

/// `AiurSystem.build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem`
#[unsafe(no_mangle)]
extern "C" fn c_rs_aiur_system_build(
  toplevel: &LeanCtorObject,
  commitment_parameters: *const c_void,
) -> *mut c_void {
  let system = AiurSystem::build(
    lean_ctor_to_toplevel(toplevel),
    lean_ptr_to_commitment_parameters(commitment_parameters),
  );
  let ptr = to_raw(system) as *mut c_void;
  unsafe { lean_alloc_external(get_aiur_system_class(), ptr) }
}

/// `AiurSystem.verify : @& AiurSystem → @& FriParameters → @& Array G → @& Proof → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn c_rs_aiur_system_verify(
  aiur_system_obj: *const c_void,
  fri_parameters: &LeanCtorObject,
  claim: &LeanArrayObject,
  proof_obj: *const c_void,
) -> *mut c_void {
  let aiur_external: &LeanExternalObject =
    as_ref_unsafe(aiur_system_obj.cast());
  let aiur_system: &AiurSystem = as_ref_unsafe(aiur_external.cast_data());

  let proof_external: &LeanExternalObject = as_ref_unsafe(proof_obj.cast());
  let proof: &Proof = as_ref_unsafe(proof_external.cast_data());

  let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
  let claim = claim.to_vec(lean_unbox_g);
  match aiur_system.verify(fri_parameters, &claim, proof) {
    Ok(()) => lean_except_ok(lean_box_fn(0)),
    Err(err) => lean_except_error_string(&format!("{err:?}")),
  }
}

/// `AiurSystem.prove`: runs the prover and returns
/// `Array G × Proof × Array G × Array (Array G × IOKeyInfo)`
#[unsafe(no_mangle)]
extern "C" fn c_rs_aiur_system_prove(
  aiur_system_obj: *const c_void,
  fri_parameters: &LeanCtorObject,
  fun_idx: *const c_void,
  args: &LeanArrayObject,
  io_data_arr: &LeanArrayObject,
  io_map_arr: &LeanArrayObject,
) -> *mut c_void {
  let aiur_external: &LeanExternalObject =
    as_ref_unsafe(aiur_system_obj.cast());
  let aiur_system: &AiurSystem = as_ref_unsafe(aiur_external.cast_data());

  let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
  let fun_idx = lean_unbox_nat_as_usize(fun_idx);
  let args = args.to_vec(lean_unbox_g);
  let io_data = io_data_arr.to_vec(lean_unbox_g);
  let io_map = lean_array_to_io_buffer_map(io_map_arr);
  let mut io_buffer = IOBuffer { data: io_data, map: io_map };

  let (claim, proof) =
    aiur_system.prove(fri_parameters, fun_idx, &args, &mut io_buffer);

  // Build Lean objects directly from the results.

  // claim: Array G
  let lean_claim = build_g_array(&claim);

  // proof: Proof (external object)
  let lean_proof = unsafe {
    lean_alloc_external(get_aiur_proof_class(), to_raw(proof) as *mut c_void)
  };

  // io_data: Array G
  let lean_io_data = build_g_array(&io_buffer.data);

  // io_map: Array (Array G × IOKeyInfo)
  let lean_io_map = unsafe {
    let arr = lean_alloc_array(io_buffer.map.len(), io_buffer.map.len());
    for (i, (key, info)) in io_buffer.map.iter().enumerate() {
      let key_arr = build_g_array(key);
      // IOKeyInfo ctor (tag 0, 2 object fields)
      let key_info = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(key_info, 0, lean_box_fn(info.idx));
      lean_ctor_set(key_info, 1, lean_box_fn(info.len));
      // (Array G × IOKeyInfo) tuple
      let map_elt = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(map_elt, 0, key_arr);
      lean_ctor_set(map_elt, 1, key_info);
      lean_array_set_core(arr, i, map_elt);
    }
    arr
  };

  // Build nested tuple:
  // Array G × Array (Array G × IOKeyInfo)
  let io_tuple = unsafe {
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, lean_io_data);
    lean_ctor_set(obj, 1, lean_io_map);
    obj
  };
  // Proof × Array G × Array (Array G × IOKeyInfo)
  let proof_io_tuple = unsafe {
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, lean_proof);
    lean_ctor_set(obj, 1, io_tuple);
    obj
  };
  // Array G × Proof × Array G × Array (Array G × IOKeyInfo)
  unsafe {
    let obj = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(obj, 0, lean_claim);
    lean_ctor_set(obj, 1, proof_io_tuple);
    obj
  }
}

// =============================================================================
// Helpers
// =============================================================================

/// Build a Lean `Array G` from a slice of field elements.
fn build_g_array(values: &[G]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(values.len(), values.len());
    for (i, g) in values.iter().enumerate() {
      lean_array_set_core(arr, i, lean_box_u64(g.as_canonical_u64()));
    }
    arr
  }
}

fn lean_ptr_to_commitment_parameters(
  commitment_parameters_ptr: *const c_void,
) -> CommitmentParameters {
  CommitmentParameters {
    log_blowup: lean_unbox_nat_as_usize(commitment_parameters_ptr),
  }
}

fn lean_ctor_to_fri_parameters(ctor: &LeanCtorObject) -> FriParameters {
  let [
    log_final_poly_len_ptr,
    num_queries_ptr,
    commit_proof_of_work_bits,
    query_proof_of_work_bits,
  ] = ctor.objs();
  FriParameters {
    log_final_poly_len: lean_unbox_nat_as_usize(log_final_poly_len_ptr),
    num_queries: lean_unbox_nat_as_usize(num_queries_ptr),
    commit_proof_of_work_bits: lean_unbox_nat_as_usize(
      commit_proof_of_work_bits,
    ),
    query_proof_of_work_bits: lean_unbox_nat_as_usize(query_proof_of_work_bits),
  }
}

fn lean_array_to_io_buffer_map(
  array: &LeanArrayObject,
) -> FxHashMap<Vec<G>, IOKeyInfo> {
  let array_data = array.data();
  let mut map =
    FxHashMap::with_capacity_and_hasher(array_data.len(), FxBuildHasher);
  for ptr in array_data {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [key_ptr, info_ptr] = ctor.objs();
    let key_array: &LeanArrayObject = as_ref_unsafe(key_ptr.cast());
    let key = key_array.to_vec(lean_unbox_g);
    let info_ctor: &LeanCtorObject = as_ref_unsafe(info_ptr.cast());
    let [idx_ptr, len_ptr] = info_ctor.objs();
    let info = IOKeyInfo {
      idx: lean_unbox_nat_as_usize(idx_ptr),
      len: lean_unbox_nat_as_usize(len_ptr),
    };
    map.insert(key, info);
  }
  map
}
