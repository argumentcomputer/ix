use binius_core::constraint_system::Proof as ProofCore;
use binius_hal::make_portable_backend;
use std::{ffi::CString, ptr};

use crate::{
    archon::{
        ModuleMode,
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

/// Just a byte flag with value 0.
const INACTIVE_MODE_SIZE: usize = 1;

/// Byte flag with value 0, the `log_height: u8` and the `depth: u64`.
const ACTIVE_MODE_SIZE: usize = 1 + size_of::<u8>() + size_of::<u64>();

#[unsafe(no_mangle)]
extern "C" fn rs_proof_size(proof: &Proof) -> usize {
    let modes_size: usize = proof
        .modes
        .iter()
        .map(|mode| match mode {
            ModuleMode::Inactive => INACTIVE_MODE_SIZE,
            ModuleMode::Active { .. } => ACTIVE_MODE_SIZE,
        })
        .sum();
    size_of::<u16>() // An `u16` is enough to indicate the number of modules
        + modes_size
        + proof.proof_core.get_proof_size()
}

#[unsafe(no_mangle)]
extern "C" fn rs_proof_to_bytes(proof: &Proof, proof_size: usize, bytes: &mut CArray<u8>) {
    let mut buffer = Vec::with_capacity(proof_size);
    let num_modules: u16 = proof.modes.len().try_into().expect("Too many modules");
    buffer.extend(num_modules.to_le_bytes());
    for mode in &proof.modes {
        match mode {
            ModuleMode::Inactive => buffer.push(0),
            ModuleMode::Active { log_height, depth } => {
                buffer.push(1);
                buffer.extend(log_height.to_le_bytes());
                buffer.extend(depth.to_le_bytes());
            }
        }
    }
    buffer.extend(&proof.proof_core.transcript);
    bytes.copy_from_slice(&buffer);
}

#[unsafe(no_mangle)]
extern "C" fn rs_proof_of_bytes(bytes: &LeanSArrayObject) -> *const Proof {
    let bytes = bytes.data();

    // Deserialize the number of modules
    let num_modules = bytes[0] as usize + 256 * (bytes[1] as usize);

    // Deserialize `modes`
    let mut modes = Vec::with_capacity(num_modules);
    let mut modes_size = 0;
    let modes_start = 2; // Skip the 2 bytes for `num_modules`
    for _ in 0..num_modules {
        match bytes[modes_start + modes_size] {
            0 => {
                modes.push(ModuleMode::Inactive);
                modes_size += INACTIVE_MODE_SIZE;
            }
            1 => {
                let log_height_idx = modes_start + modes_size + 1;
                let log_height = bytes[log_height_idx];
                let mut depth_bytes = [0; size_of::<u64>()];
                let depth_start = log_height_idx + 1;
                depth_bytes.copy_from_slice(&bytes[depth_start..depth_start + size_of::<u64>()]);
                let depth = u64::from_le_bytes(depth_bytes);
                modes.push(ModuleMode::active(log_height, depth));
                modes_size += ACTIVE_MODE_SIZE;
            }
            _ => panic!("Invalid ModuleMode flag"),
        }
    }

    // Deserialize `transcript`
    let transcript_start = modes_start + modes_size;
    let transcript = bytes[transcript_start..].to_vec();
    let proof_core = ProofCore { transcript };
    to_raw(Proof { modes, proof_core })
}
