use multi_stark::{
    p3_field::PrimeField64,
    prover::Proof,
    types::{CommitmentParameters, FriParameters},
};
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::{
    ffi::{CString, c_void},
    slice,
};

use crate::{
    aiur::{
        G,
        execute::{IOBuffer, IOKeyInfo},
        synthesis::AiurSystem,
    },
    lean::{
        array::LeanArrayObject,
        as_mut_unsafe, as_ref_unsafe,
        boxed::BoxedU64,
        ctor::LeanCtorObject,
        ffi::{
            BytesData, CResult,
            aiur::{lean_unbox_g, lean_unbox_nat_as_usize, toplevel::lean_ctor_to_toplevel},
            drop_raw, to_raw,
        },
        sarray::LeanSArrayObject,
    },
    lean_box,
};

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_to_bytes(proof: &Proof) -> *const BytesData {
    let bytes = proof.to_bytes().expect("Serialization error");
    let bytes_data = BytesData::from_vec(bytes);
    to_raw(bytes_data)
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_of_bytes(byte_array: &LeanSArrayObject) -> *const Proof {
    let proof = Proof::from_bytes(byte_array.data()).expect("Deserialization error");
    to_raw(proof)
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_free(ptr: *mut AiurSystem) {
    drop_raw(ptr);
}

fn lean_ptr_to_commitment_parameters(
    commitment_parameters_ptr: *const c_void,
) -> CommitmentParameters {
    // Single-attribute structure in Lean.
    CommitmentParameters {
        log_blowup: lean_unbox_nat_as_usize(commitment_parameters_ptr),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_build(
    toplevel: &LeanCtorObject,
    commitment_parameters: *const c_void,
) -> *const AiurSystem {
    to_raw(AiurSystem::build(
        lean_ctor_to_toplevel(toplevel),
        lean_ptr_to_commitment_parameters(commitment_parameters),
    ))
}

fn lean_ctor_to_fri_parameters(ctor: &LeanCtorObject) -> FriParameters {
    let [
        log_final_poly_len_ptr,
        num_queries_ptr,
        proof_of_work_bits_ptr,
    ] = ctor.objs();
    FriParameters {
        log_final_poly_len: lean_unbox_nat_as_usize(log_final_poly_len_ptr),
        num_queries: lean_unbox_nat_as_usize(num_queries_ptr),
        proof_of_work_bits: lean_unbox_nat_as_usize(proof_of_work_bits_ptr),
    }
}

#[repr(C)]
struct ProveData {
    claim_size: usize,
    claim: *const Vec<G>,
    proof: *const Proof,
    io_buffer: *const IOBuffer,
    io_data_size: usize,
    io_map_size: usize,
    io_keys_sizes: *const usize,
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_claim_free(ptr: *mut Vec<G>) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_proof_free(ptr: *mut Proof) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_prove_data_io_buffer_free(prove_data: &ProveData) {
    let boxed_io_keys_sizes = unsafe {
        let slice = slice::from_raw_parts_mut(
            prove_data.io_keys_sizes as *mut usize,
            prove_data.io_map_size,
        );
        Box::from_raw(slice)
    };
    drop(boxed_io_keys_sizes);
    drop_raw(prove_data.io_buffer as *mut ProveData);
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_prove_data_free(ptr: *mut ProveData) {
    drop_raw(ptr);
}

fn lean_array_to_io_buffer_map(array: &LeanArrayObject) -> FxHashMap<Vec<G>, IOKeyInfo> {
    let array_data = array.data();
    let mut map = FxHashMap::with_capacity_and_hasher(array_data.len(), FxBuildHasher);
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

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
    aiur_system: &AiurSystem,
    fri_parameters: &LeanCtorObject,
    fun_idx: *const c_void,
    args: &LeanArrayObject,
    io_data: &LeanArrayObject,
    io_map: &LeanArrayObject,
) -> *const ProveData {
    let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
    let fun_idx = lean_unbox_nat_as_usize(fun_idx);
    let args = args.to_vec(lean_unbox_g);
    let io_data = io_data.to_vec(lean_unbox_g);
    let io_map = lean_array_to_io_buffer_map(io_map);
    let mut io_buffer = IOBuffer {
        data: io_data,
        map: io_map,
    };
    let (claim, proof) = aiur_system.prove(fri_parameters, fun_idx, &args, &mut io_buffer);
    let claim_size = claim.len();
    let io_keys_sizes_boxed: Box<[usize]> = io_buffer.map.keys().map(Vec::len).collect();
    let io_keys_sizes = io_keys_sizes_boxed.as_ptr();
    std::mem::forget(io_keys_sizes_boxed);
    let io_data_size = io_buffer.data.len();
    let io_map_size = io_buffer.map.len();
    let prove_data = ProveData {
        claim_size,
        claim: to_raw(claim),
        proof: to_raw(proof),
        io_buffer: to_raw(io_buffer),
        io_data_size,
        io_map_size,
        io_keys_sizes,
    };
    to_raw(prove_data)
}

#[unsafe(no_mangle)]
extern "C" fn rs_set_array_g_values(array: &LeanArrayObject, values: &Vec<G>) {
    let array_values = array.data();
    assert_eq!(array_values.len(), values.len());
    array_values.iter().zip(values).for_each(|(ptr, g)| {
        let boxed_u64 = as_mut_unsafe(*ptr as *mut BoxedU64);
        boxed_u64.value = g.as_canonical_u64();
    });
}

#[unsafe(no_mangle)]
extern "C" fn rs_set_aiur_io_data_values(io_data_array: &LeanArrayObject, io_buffer: &IOBuffer) {
    rs_set_array_g_values(io_data_array, &io_buffer.data);
}

#[unsafe(no_mangle)]
extern "C" fn rs_set_aiur_io_map_values(io_map_array: &LeanArrayObject, io_buffer: &IOBuffer) {
    let io_map_values = io_map_array.data();
    assert_eq!(io_map_values.len(), io_buffer.map.len());
    io_map_values
        .iter()
        .zip(&io_buffer.map)
        .for_each(|(ptr, (key, info))| {
            let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
            let [key_array, key_info] = ctor.objs();
            rs_set_array_g_values(as_mut_unsafe(key_array as *mut LeanArrayObject), key);

            let key_info_ctor: &mut LeanCtorObject = as_mut_unsafe(key_info as *mut _);
            key_info_ctor.set_objs(&[lean_box!(info.idx), lean_box!(info.len)]);
        });
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_verify(
    aiur_system: &AiurSystem,
    fri_parameters: &LeanCtorObject,
    claim: &LeanArrayObject,
    proof: &Proof,
) -> *const CResult {
    let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
    let claim = claim.to_vec(lean_unbox_g);
    let c_result = match aiur_system.verify(fri_parameters, &claim, proof) {
        Ok(()) => CResult {
            is_ok: true,
            data: std::ptr::null(),
        },
        Err(err) => {
            let msg = CString::new(format!("{err:?}")).expect("CString::new failure");
            CResult {
                is_ok: false,
                data: msg.into_raw().cast(),
            }
        }
    };
    to_raw(c_result)
}
