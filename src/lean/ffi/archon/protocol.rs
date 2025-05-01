use std::{ffi::CString, ptr};

use crate::{
    archon::{circuit::CircuitModule, protocol::validate_witness_core},
    lean::{
        CArray,
        array::LeanArrayObject,
        ffi::{CResult, archon::witness::WitnessWrap, binius::ctor_ptr_to_boundary, to_raw},
    },
};

#[unsafe(no_mangle)]
extern "C" fn rs_validate_witness(
    circuit_modules: &CArray<&CircuitModule>,
    num_modules: usize,
    witness: &WitnessWrap,
    boundaries: &LeanArrayObject,
) -> *const CResult {
    let circuit_modules = circuit_modules.slice(num_modules);
    let boundaries = boundaries.to_vec(ctor_ptr_to_boundary);
    let WitnessWrap { witness, .. } = witness;
    let c_result = match validate_witness_core(circuit_modules, witness, &boundaries) {
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
