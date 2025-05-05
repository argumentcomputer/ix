use binius_hal::make_portable_backend;
use std::{ffi::CString, ptr};

use crate::{
    archon::{
        circuit::CircuitModule,
        protocol::{Proof, prove_core, validate_witness_core, verify_core},
    },
    lean::{
        CArray,
        array::LeanArrayObject,
        ffi::{
            CResult, archon::witness::WitnessWrap, binius::ctor_ptr_to_boundary, drop_raw, to_raw,
        },
    },
};

#[unsafe(no_mangle)]
extern "C" fn rs_validate_witness(
    num_modules: usize,
    circuit_modules: &CArray<&CircuitModule>,
    boundaries: &LeanArrayObject,
    witness_wrap: &WitnessWrap,
) -> *const CResult {
    let circuit_modules = circuit_modules.slice(num_modules);
    let boundaries = boundaries.to_vec(ctor_ptr_to_boundary);
    let WitnessWrap { witness, .. } = witness_wrap;
    let c_result = match validate_witness_core(circuit_modules, &boundaries, witness) {
        Ok(_) => CResult {
            is_ok: true,
            data: ptr::null(),
        },
        Err(err) => {
            let msg = CString::new(err.to_string()).expect("CString::new failure");
            CResult {
                is_ok: false,
                data: msg.into_raw().cast(),
            }
        }
    };
    to_raw(c_result)
}

#[unsafe(no_mangle)]
extern "C" fn rs_proof_free(ptr: *mut Proof) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_prove(
    num_modules: usize,
    circuit_modules: &CArray<&CircuitModule>,
    boundaries: &LeanArrayObject,
    log_inv_rate: usize,
    security_bits: usize,
    witness_wrap: &mut WitnessWrap,
) -> *const Proof {
    let circuit_modules = circuit_modules.slice(num_modules);
    let boundaries = boundaries.to_vec(ctor_ptr_to_boundary);
    let witness = std::mem::take(&mut witness_wrap.witness);
    let proof = prove_core(
        circuit_modules,
        &boundaries,
        log_inv_rate,
        security_bits,
        witness,
        &make_portable_backend(),
    )
    .expect("protocol::prove_core failure");
    to_raw(proof)
}

#[unsafe(no_mangle)]
extern "C" fn rs_verify(
    num_modules: usize,
    circuit_modules: &CArray<&CircuitModule>,
    boundaries: &LeanArrayObject,
    log_inv_rate: usize,
    security_bits: usize,
    proof: &mut Proof,
) -> *const CResult {
    let circuit_modules = circuit_modules.slice(num_modules);
    let boundaries = boundaries.to_vec(ctor_ptr_to_boundary);
    let proof = std::mem::take(proof);
    let c_result = match verify_core(
        circuit_modules,
        &boundaries,
        proof,
        log_inv_rate,
        security_bits,
    ) {
        Ok(_) => CResult {
            is_ok: true,
            data: ptr::null(),
        },
        Err(err) => {
            let msg = CString::new(err.to_string()).expect("CString::new failure");
            CResult {
                is_ok: false,
                data: msg.into_raw().cast(),
            }
        }
    };
    to_raw(c_result)
}
