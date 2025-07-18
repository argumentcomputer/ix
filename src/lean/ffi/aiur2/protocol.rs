use multi_stark::{
    prover::{Claim, Proof},
    types::FriParameters,
};
use std::ffi::{CString, c_void};

use crate::{
    aiur2::synthesis::AiurSystem,
    lean::{
        array::LeanArrayObject,
        ctor::LeanCtorObject,
        ffi::{
            CResult,
            aiur2::{
                lean_unbox_g, lean_unbox_nat_as_usize, set_lean_array_data,
                toplevel::lean_ctor_to_toplevel,
            },
            as_ref_unsafe, drop_raw, to_raw,
        },
    },
    lean_unbox,
};

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
    claim_num_args: usize,
    claim_ptr: *const Claim,
    proof_ptr: *const Proof,
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_claim_free(ptr: *mut Claim) {
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
    fun_idx: *const c_void, // Already checked to be a scalar in the C code
    args: &LeanArrayObject,
) -> *const ProveData {
    let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
    let args = args.to_vec(lean_unbox_g);
    let (claim, proof) = aiur_system.prove(&fri_parameters, lean_unbox!(usize, fun_idx), &args);
    let claim_num_args = claim.args.len();
    let prove_data = ProveData {
        claim_num_args,
        claim_ptr: to_raw(claim),
        proof_ptr: to_raw(proof),
    };
    to_raw(prove_data)
}

#[unsafe(no_mangle)]
extern "C" fn rs_set_aiur_claim_args(claim_args: &mut LeanArrayObject, claim: &Claim) {
    set_lean_array_data(claim_args, &claim.args)
}

fn lean_ctor_to_claim(ctor: &LeanCtorObject) -> Claim {
    let [circuit_idx_ptr, args_ptr] = ctor.objs();
    let circuit_idx = lean_unbox_nat_as_usize(circuit_idx_ptr);
    let args_array: &LeanArrayObject = as_ref_unsafe(args_ptr.cast());
    let args = args_array.to_vec(lean_unbox_g);
    Claim { circuit_idx, args }
}

#[unsafe(no_mangle)]
extern "C" fn rs_aiur_system_verify(
    aiur_system: &AiurSystem,
    fri_parameters: &LeanCtorObject,
    claim: &LeanCtorObject,
    proof: &Proof,
) -> *const CResult {
    let fri_parameters = lean_ctor_to_fri_parameters(fri_parameters);
    let claim = lean_ctor_to_claim(claim);
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
