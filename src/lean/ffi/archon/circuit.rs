use binius_core::{constraint_system::channel::FlushDirection, oracle::ShiftVariant};
use binius_field::{
    BinaryField1b as B1, BinaryField2b as B2, BinaryField4b as B4, BinaryField8b as B8,
    BinaryField16b as B16, BinaryField32b as B32, BinaryField64b as B64, BinaryField128b as B128,
};
use std::ffi::c_char;

use crate::{
    archon::{
        ModuleId, OracleIdx, canonical::Canonical, circuit::CircuitModule, witness::WitnessModule,
    },
    lean::{
        CArray,
        array::LeanArrayObject,
        ctor::LeanCtorObject,
        ffi::{
            archon::{
                arith_expr::lean_ctor_to_arith_expr, boxed_usize_ptr_to_oracle_idx,
                ctor_ptr_to_lc_factor, transparent::lean_ctor_ptr_to_transparent,
            },
            drop_raw, raw_to_str, to_raw,
        },
    },
};

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_new(module_id: ModuleId) -> *const CircuitModule {
    to_raw(CircuitModule::new(module_id))
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_free(ptr: *mut CircuitModule) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_freeze_oracles(circuit_module: &mut CircuitModule) {
    circuit_module.freeze_oracles();
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_init_witness_module(
    circuit_module: &CircuitModule,
) -> *const WitnessModule {
    to_raw(
        circuit_module
            .init_witness_module()
            .expect("CircuitModule::init_witness_module failure"),
    )
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_flush(
    circuit_module: &mut CircuitModule,
    direction_pull: bool,
    channel_idx: usize,
    oracle_id: OracleIdx,
    oracle_idxs: &LeanArrayObject,
    multiplicity: u64,
) {
    let oracle_idxs = oracle_idxs.to_vec(boxed_usize_ptr_to_oracle_idx);
    use FlushDirection::{Pull, Push};
    let direction = if direction_pull { Pull } else { Push };
    let channel_id = channel_idx;
    circuit_module.flush(direction, channel_id, oracle_id, oracle_idxs, multiplicity);
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_assert_zero(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    oracle_idxs: &LeanArrayObject,
    composition: &LeanCtorObject,
) {
    let oracle_idxs = oracle_idxs.to_vec(boxed_usize_ptr_to_oracle_idx);
    let composition = lean_ctor_to_arith_expr(composition);
    circuit_module.assert_zero(raw_to_str(name), oracle_idxs, composition);
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_assert_not_zero(
    circuit_module: &mut CircuitModule,
    oracle_idx: OracleIdx,
) {
    circuit_module.assert_not_zero(oracle_idx);
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_add_committed(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    tower_level: u8,
) -> OracleIdx {
    let name = raw_to_str(name);
    match tower_level {
        0 => circuit_module.add_committed::<B1>(name),
        1 => circuit_module.add_committed::<B2>(name),
        2 => circuit_module.add_committed::<B4>(name),
        3 => circuit_module.add_committed::<B8>(name),
        4 => circuit_module.add_committed::<B16>(name),
        5 => circuit_module.add_committed::<B32>(name),
        6 => circuit_module.add_committed::<B64>(name),
        7 => circuit_module.add_committed::<B128>(name),
        _ => unreachable!(),
    }
    .expect("CircuitModule::add_committed failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_add_transparent(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    transparent_ptr: *const LeanCtorObject,
) -> OracleIdx {
    let name = raw_to_str(name);
    let transparent = lean_ctor_ptr_to_transparent(transparent_ptr);
    circuit_module
        .add_transparent(name, transparent)
        .expect("CircuitModule::add_transparent failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_add_linear_combination(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    offset: &u128,
    inner: &LeanArrayObject,
) -> OracleIdx {
    let inner = inner.to_vec(ctor_ptr_to_lc_factor);
    let offset = B128::new(*offset);
    circuit_module
        .add_linear_combination(raw_to_str(name), offset, inner)
        .expect("CircuitModule::add_linear_combination failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_add_packed(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    inner: OracleIdx,
    log_degree: usize,
) -> OracleIdx {
    circuit_module
        .add_packed(raw_to_str(name), inner, log_degree)
        .expect("CircuitModule::add_packed failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_add_shifted(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    inner: OracleIdx,
    shift_offset: u32,
    block_bits: usize,
    shift_variant: u8,
) -> OracleIdx {
    let shift_variant = match shift_variant {
        0 => ShiftVariant::CircularLeft,
        1 => ShiftVariant::LogicalLeft,
        2 => ShiftVariant::LogicalRight,
        _ => unreachable!(),
    };
    circuit_module
        .add_shifted(
            raw_to_str(name),
            inner,
            shift_offset,
            block_bits,
            shift_variant,
        )
        .expect("CircuitModule::add_shifted failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_add_projected(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
    inner: OracleIdx,
    mask: u64,
    unprojected_size: usize,
    start_index: usize,
) -> OracleIdx {
    circuit_module
        .add_projected(raw_to_str(name), inner, mask, unprojected_size, start_index)
        .expect("CircuitModule::add_projected failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_push_namespace(
    circuit_module: &mut CircuitModule,
    name: *const c_char,
) {
    circuit_module.push_namespace(raw_to_str(name));
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_pop_namespace(circuit_module: &mut CircuitModule) {
    circuit_module.pop_namespace();
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_canonical_bytes_size(circuit_module: &CircuitModule) -> usize {
    Canonical::size(circuit_module)
}

#[unsafe(no_mangle)]
extern "C" fn rs_circuit_module_canonical_bytes(
    circuit_module: &CircuitModule,
    size: usize,
    bytes: &mut CArray<u8>,
) {
    let mut buffer = Vec::with_capacity(size);
    Canonical::write(circuit_module, &mut buffer);
    bytes.copy_from_slice(&buffer);
}
