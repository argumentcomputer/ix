use binius_circuits::builder::ConstraintSystemBuilder;
use binius_core::{
    constraint_system::{
        channel::{ChannelId, FlushDirection},
        ConstraintSystem,
    },
    oracle::OracleId,
};
use binius_field::BinaryField128b;
use binius_math::ArithExpr;
use std::ffi::c_char;

use crate::lean::{
    array::LeanArrayUSize,
    boxed::BoxedUSize,
    ctor::LeanCtorObject,
    external::LeanExternalObject,
    ffi::{drop_raw, raw_to_str, to_raw},
    object::LeanObject,
};

/* --- ConstraintSystem --- */

#[no_mangle]
extern "C" fn rs_constraint_system_free(ptr: *mut ConstraintSystem<BinaryField128b>) {
    drop_raw(ptr);
}

/* --- ConstraintSystemBuilder --- */

#[no_mangle]
extern "C" fn rs_constraint_system_builder_init<'a>() -> *const ConstraintSystemBuilder<'a> {
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

fn lean_ctor_to_arith_expr<T>(ctor_ptr: *const LeanCtorObject<T>) -> ArithExpr<BinaryField128b> {
    let ctor = unsafe { &*ctor_ptr };
    match ctor.m_header.m_tag() {
        0 => {
            // Const
            let external_object = ctor.m_objs.slice(1)[0] as *const LeanExternalObject;
            let u128_ptr = unsafe { (*external_object).m_data } as *const u128;
            ArithExpr::Const(BinaryField128b::new(unsafe { *u128_ptr }))
        }
        1 => {
            // Var
            let boxed_usize_ptr = ctor_ptr as *const BoxedUSize; // Lean optimizes to boxed usize
            let boxed_usize = unsafe { &*boxed_usize_ptr };
            ArithExpr::Var(boxed_usize.value)
        }
        2 => {
            // Add
            let ctors = ctor.m_objs.slice(2);
            let (x, y) = (ctors[0], ctors[1]);
            let x = lean_ctor_to_arith_expr(x as *const LeanCtorObject<T>);
            let y = lean_ctor_to_arith_expr(y as *const LeanCtorObject<T>);
            ArithExpr::Add(Box::new(x), Box::new(y))
        }
        3 => {
            // Mul
            let ctors = ctor.m_objs.slice(2);
            let (x, y) = (ctors[0], ctors[1]);
            let x = lean_ctor_to_arith_expr(x as *const LeanCtorObject<T>);
            let y = lean_ctor_to_arith_expr(y as *const LeanCtorObject<T>);
            ArithExpr::Mul(Box::new(x), Box::new(y))
        }
        4 => {
            // Pow
            let objs = ctor.m_objs.slice(2);
            let (x, e) = (objs[0], objs[1] as u64);
            let x = lean_ctor_to_arith_expr(x as *const LeanCtorObject<T>);
            ArithExpr::Pow(Box::new(x), e)
        }
        _ => panic!("Invalid ctor tag"),
    }
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
