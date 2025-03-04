use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::{
    constraint_system::{
        channel::{ChannelId, FlushDirection},
        ConstraintSystem,
    },
    oracle::OracleId,
};
use binius_field::BinaryField128b;
use std::ffi::c_char;

use crate::lean::{
    array::LeanArrayUSize,
    ctor::LeanCtorObject,
    ffi::{drop_raw, raw_to_str, to_raw},
    object::LeanObject,
};

use super::binius_arith_expr::lean_ctor_to_arith_expr;

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
    oracle_ids: &LeanArrayUSize,
    multiplicity: u64,
) {
    let oracle_ids = oracle_ids.to_vec();
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
    oracle_ids: &LeanArrayUSize,
    multiplicity: u64,
) {
    let oracle_ids = oracle_ids.to_vec();
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
    oracle_ids: &LeanArrayUSize,
    composition: &LeanCtorObject<LeanObject>,
) {
    let oracle_ids = oracle_ids.to_vec();
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
    oracle_ids: &LeanArrayUSize,
) -> usize {
    builder
        .log_rows(oracle_ids.to_vec())
        .expect("ConstraintSystemBuilder::log_rows failure")
}
