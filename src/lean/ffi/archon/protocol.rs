use binius_core::constraint_system::Proof as ProofCore;
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
        sarray::LeanSArrayObject,
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

#[unsafe(no_mangle)]
extern "C" fn rs_proof_size(proof: &Proof) -> usize {
    size_of::<u16>() // An `u16` is enough to indicate the number of modules
        + proof.modules_heights.len() * size_of::<u64>()
        + proof.proof_core.get_proof_size()
}

#[unsafe(no_mangle)]
extern "C" fn rs_proof_to_bytes(proof: &Proof, proof_size: usize, bytes: &mut CArray<u8>) {
    let mut buffer = Vec::with_capacity(proof_size);
    let num_modules: u16 = proof
        .modules_heights
        .len()
        .try_into()
        .expect("Too many modules");
    buffer.extend(num_modules.to_le_bytes());
    for module_height in &proof.modules_heights {
        buffer.extend(module_height.to_le_bytes());
    }
    buffer.extend(&proof.proof_core.transcript);
    bytes.copy_from_slice(&buffer);
}

#[unsafe(no_mangle)]
extern "C" fn rs_proof_of_bytes(bytes: &LeanSArrayObject) -> *const Proof {
    let bytes = bytes.data();
    let mut num_modules_bytes = [0; 2];
    num_modules_bytes.copy_from_slice(&bytes[..2]);
    let num_modules = u16::from_le_bytes(num_modules_bytes) as usize;
    let mut modules_heights = Vec::with_capacity(num_modules);
    for i in 0..num_modules {
        let mut module_height_bytes = [0; size_of::<u64>()];
        let u64_start = 2 + i * size_of::<u64>();
        module_height_bytes.copy_from_slice(&bytes[u64_start..u64_start + size_of::<u64>()]);
        modules_heights.push(u64::from_le_bytes(module_height_bytes));
    }
    let transcript_start = 2 + num_modules * size_of::<u64>();
    let transcript = bytes[transcript_start..].to_vec();
    let proof_core = ProofCore { transcript };
    let proof = Proof {
        modules_heights,
        proof_core,
    };
    to_raw(proof)
}
