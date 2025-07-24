use multi_stark::{p3_field::PrimeField64, prover::Proof, types::FriParameters};
use std::ffi::{CString, c_void};

use crate::{
    aiur::{G, synthesis::AiurSystem},
    lean::{
        array::LeanArrayObject,
        as_mut_unsafe,
        boxed::BoxedU64,
        ctor::LeanCtorObject,
        ffi::{
            BytesData, CResult,
            aiur::{lean_unbox_g, lean_unbox_nat_as_usize, toplevel::lean_ctor_to_toplevel},
            drop_raw, to_raw,
        },
        sarray::LeanSArrayObject,
    },
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

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_build(toplevel: &LeanCtorObject) -> *const AiurSystem {
    to_raw(AiurSystem::build(lean_ctor_to_toplevel(toplevel)))
}

fn lean_ctor_to_fri_parameters(ctor: &LeanCtorObject) -> FriParameters {
    let [
        log_blowup_ptr,
        log_final_poly_len_ptr,
        num_queries_ptr,
        proof_of_work_bits_ptr,
    ] = ctor.objs();
    let log_blowup = lean_unbox_nat_as_usize(log_blowup_ptr);
    let log_final_poly_len = lean_unbox_nat_as_usize(log_final_poly_len_ptr);
    let num_queries = lean_unbox_nat_as_usize(num_queries_ptr);
    let proof_of_work_bits = lean_unbox_nat_as_usize(proof_of_work_bits_ptr);
    FriParameters {
        log_blowup,
        log_final_poly_len,
        num_queries,
        proof_of_work_bits,
    }
}

#[repr(C)]
struct ProveData {
    claim_size: usize,
    claim: *const Vec<G>,
    proof: *const Proof,
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
extern "C" fn rs_aiur_prove_data_free(ptr: *mut ProveData) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_prove(
    aiur_system: &AiurSystem,
    fri_parameters: &LeanCtorObject,
    fun_idx: *const c_void,
    args: &LeanArrayObject,
) -> *const ProveData {
    let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
    let fun_idx = lean_unbox_nat_as_usize(fun_idx);
    let args = args.to_vec(lean_unbox_g);
    let (claim, proof) = aiur_system.prove(&fri_parameters, fun_idx, &args);
    let claim_size = claim.len();
    let prove_data = ProveData {
        claim_size,
        claim: to_raw(claim),
        proof: to_raw(proof),
    };
    to_raw(prove_data)
}

#[unsafe(no_mangle)]
extern "C" fn rs_set_aiur_claim_args(claim_array: &mut LeanArrayObject, claim: &Vec<G>) {
    let claim_data = claim_array.data();
    assert_eq!(claim_data.len(), claim.len());
    claim_data.iter().zip(claim).for_each(|(ptr, g)| {
        let boxed_u64 = as_mut_unsafe(*ptr as *mut BoxedU64);
        boxed_u64.value = g.as_canonical_u64();
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
    let c_result = match aiur_system.verify(&fri_parameters, &claim, proof) {
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
