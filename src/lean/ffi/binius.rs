use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::{
    constraint_system::{
        channel::{ChannelId, FlushDirection},
        ConstraintSystem,
    },
    oracle::OracleId,
};
use binius_field::BinaryField128b;
use std::ffi::{c_char, c_void};

use crate::lean::{
    array::LeanArrayObject,
    boxed::BoxedUSize,
    ctor::LeanCtorObject,
    external::LeanExternalObject,
    ffi::{binius_arith_expr::lean_ctor_to_arith_expr, drop_raw, raw_to_str, to_raw},
};

fn boxed_usize_ptr_to_usize(ptr: *const c_void) -> usize {
    let boxed_usize_ptr = ptr.cast::<BoxedUSize>();
    let boxed_usize = unsafe { boxed_usize_ptr.as_ref().expect("null ptr") };
    boxed_usize.value
}

fn ctor_ptr_to_lc_factor(ptr: *const c_void) -> (OracleId, BinaryField128b) {
    let ctor_ptr = ptr as *const LeanCtorObject;
    let ctor = unsafe { &*ctor_ptr };
    let objs = ctor.m_objs.slice(2);
    let (oracle_id_ptr, u128_external_ptr) = (objs[0], objs[1]);
    let oracle_id = boxed_usize_ptr_to_usize(oracle_id_ptr);
    let u128_external = unsafe { &*(u128_external_ptr as *const LeanExternalObject) };
    let u128_ptr = u128_external.m_data as *const u128;
    let u128 = unsafe { *u128_ptr };
    (oracle_id, BinaryField128b::new(u128))
}

/* --- ConstraintSystem --- */

#[no_mangle]
extern "C" fn rs_constraint_system_free(ptr: *mut ConstraintSystem<BinaryField128b>) {
    drop_raw(ptr);
}

/* --- ConstraintSystemBuilder --- */

#[no_mangle]
extern "C" fn rs_constraint_system_builder_new<'a>() -> *const ConstraintSystemBuilder<'a> {
    to_raw(ConstraintSystemBuilder::new())
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_free(ptr: *mut ConstraintSystemBuilder) {
    drop_raw(ptr);
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_build(
    builder: &mut ConstraintSystemBuilder,
) -> *const ConstraintSystem<BinaryField128b> {
    let builder = std::mem::take(builder);
    to_raw(
        builder
            .build()
            .expect("ConstraintSystemBuilder::build failure"),
    )
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_flush_with_multiplicity(
    builder: &mut ConstraintSystemBuilder,
    direction_pull: bool,
    channel_id: ChannelId,
    count: usize,
    oracle_ids: &LeanArrayObject,
    multiplicity: u64,
) {
    let oracle_ids = oracle_ids.to_vec(boxed_usize_ptr_to_usize);
    use FlushDirection::*;
    let direction = if direction_pull { Pull } else { Push };
    builder
        .flush_with_multiplicity(direction, channel_id, count, oracle_ids, multiplicity)
        .expect("ConstraintSystemBuilder::flush_with_multiplicity failure");
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_flush_custom(
    builder: &mut ConstraintSystemBuilder,
    direction_pull: bool,
    channel_id: ChannelId,
    selector: OracleId,
    oracle_ids: &LeanArrayObject,
    multiplicity: u64,
) {
    let oracle_ids = oracle_ids.to_vec(boxed_usize_ptr_to_usize);
    use FlushDirection::*;
    let direction = if direction_pull { Pull } else { Push };
    builder
        .flush_custom(direction, channel_id, selector, oracle_ids, multiplicity)
        .expect("ConstraintSystemBuilder::flush_custom failure");
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_assert_zero(
    builder: &mut ConstraintSystemBuilder,
    name: *const c_char,
    oracle_ids: &LeanArrayObject,
    composition: &LeanCtorObject,
) {
    let oracle_ids = oracle_ids.to_vec(boxed_usize_ptr_to_usize);
    let composition = lean_ctor_to_arith_expr(composition);
    builder.assert_zero(raw_to_str(name), oracle_ids, composition);
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_assert_not_zero(
    builder: &mut ConstraintSystemBuilder,
    oracle_id: OracleId,
) {
    builder.assert_not_zero(oracle_id);
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_add_channel(
    builder: &mut ConstraintSystemBuilder,
) -> ChannelId {
    builder.add_channel()
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_add_committed(
    builder: &mut ConstraintSystemBuilder,
    name: *const c_char,
    n_vars: usize,
    tower_level: usize,
) -> OracleId {
    builder.add_committed(raw_to_str(name), n_vars, tower_level)
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_add_linear_combination(
    builder: &mut ConstraintSystemBuilder,
    name: *const c_char,
    n_vars: usize,
    inner: &LeanArrayObject,
) -> OracleId {
    let inner = inner.to_vec(ctor_ptr_to_lc_factor);
    builder
        .add_linear_combination(raw_to_str(name), n_vars, inner)
        .expect("ConstraintSystemBuilder::add_linear_combination failure")
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_add_linear_combination_with_offset(
    builder: &mut ConstraintSystemBuilder,
    name: *const c_char,
    n_vars: usize,
    offset: &u128,
    inner: &LeanArrayObject,
) -> OracleId {
    let inner = inner.to_vec(ctor_ptr_to_lc_factor);
    let offset = BinaryField128b::new(*offset);
    builder
        .add_linear_combination_with_offset(raw_to_str(name), n_vars, offset, inner)
        .expect("ConstraintSystemBuilder::add_linear_combination failure")
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_add_packed(
    builder: &mut ConstraintSystemBuilder,
    name: *const c_char,
    oracle_id: OracleId,
    log_degree: usize,
) -> OracleId {
    builder
        .add_packed(raw_to_str(name), oracle_id, log_degree)
        .expect("ConstraintSystemBuilder::add_packed failure")
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_push_namespace(
    builder: &mut ConstraintSystemBuilder,
    name: *const c_char,
) {
    builder.push_namespace(raw_to_str(name));
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_pop_namespace(builder: &mut ConstraintSystemBuilder) {
    builder.pop_namespace();
}

#[no_mangle]
extern "C" fn rs_constraint_system_builder_log_rows(
    builder: &ConstraintSystemBuilder,
    oracle_ids: &LeanArrayObject,
) -> usize {
    builder
        .log_rows(oracle_ids.to_vec(boxed_usize_ptr_to_usize))
        .expect("ConstraintSystemBuilder::log_rows failure")
}
