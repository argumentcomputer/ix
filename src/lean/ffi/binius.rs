use binius_circuits::builder::{ConstraintSystemBuilder, witness};
use binius_core::{
    constraint_system::{
        ConstraintSystem,
        channel::{ChannelId, FlushDirection},
        validate::validate_witness,
    },
    oracle::OracleId,
    witness::MultilinearExtensionIndex,
};
use binius_field::{BinaryField8b, BinaryField128b, arch::OptimalUnderlier};
use bumpalo::Bump;
use std::{
    cell::RefCell,
    ffi::{c_char, c_void},
    rc::Rc,
};

use crate::lean::{
    array::LeanArrayObject,
    boxed::BoxedUSize,
    ctor::LeanCtorObject,
    external::LeanExternalObject,
    ffi::{
        as_ref_unsafe, binius_arith_expr::lean_ctor_to_arith_expr,
        binius_boundary::ctor_ptr_to_boundary, drop_raw, raw_to_str, to_raw,
    },
    sarray::LeanSArrayObject,
};

pub(super) fn boxed_usize_ptr_to_usize(ptr: *const c_void) -> usize {
    let boxed_usize_ptr = ptr.cast::<BoxedUSize>();
    let boxed_usize = as_ref_unsafe(boxed_usize_ptr);
    boxed_usize.value
}

pub(super) fn external_ptr_to_u128(ptr: *const c_void) -> u128 {
    let u128_external = as_ref_unsafe(ptr.cast::<LeanExternalObject>());
    *as_ref_unsafe(u128_external.cast_data())
}

fn ctor_ptr_to_lc_factor(ptr: *const c_void) -> (OracleId, BinaryField128b) {
    let ctor_ptr = ptr.cast::<LeanCtorObject>();
    let ctor = as_ref_unsafe(ctor_ptr);
    let [oracle_id_ptr, u128_external_ptr] = ctor.objs();
    let oracle_id = boxed_usize_ptr_to_usize(oracle_id_ptr);
    let u128 = external_ptr_to_u128(u128_external_ptr);
    (oracle_id, BinaryField128b::new(u128))
}

/* --- Witness --- */

type Witness<'a> = MultilinearExtensionIndex<'a, OptimalUnderlier, BinaryField128b>;

#[unsafe(no_mangle)]
extern "C" fn rs_witness_free(ptr: *mut Witness<'_>) {
    drop_raw(ptr);
}

/* --- WitnessBuilder --- */

/// Also holds a reference to the allocator, which lives in the heap and needs
/// to be deallocated manually.
struct WitnessBuilder<'a> {
    allocator: &'a Bump,
    builder: witness::Builder<'a>,
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_builder_new<'a>(
    cs: &ConstraintSystem<BinaryField128b>,
) -> *const WitnessBuilder<'a> {
    let allocator = Box::leak(Box::new(Bump::new()));
    // The following clone is cheap because `MultilinearOracleSet` is a wrapper
    // around `Vec<Arc<_>>`.
    let builder = witness::Builder::new(allocator, Rc::new(RefCell::new(cs.oracles.clone())));
    to_raw(WitnessBuilder { allocator, builder })
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_builder_free(ptr: *mut WitnessBuilder<'_>) {
    let builder = unsafe { Box::from_raw(ptr) };
    let allocator = builder.allocator as *const Bump as *mut Bump;
    drop_raw(allocator);
    drop(builder);
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_builder_with_column(
    witness_builder: &WitnessBuilder<'_>,
    oracle_id: OracleId,
    bytes: &LeanSArrayObject,
) {
    witness_builder
        .builder
        .new_column::<BinaryField8b>(oracle_id)
        .as_mut_slice()
        .copy_from_slice(bytes.data());
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_builder_build<'a>(
    witness_builder: &'a mut WitnessBuilder<'_>,
) -> *const Witness<'a> {
    let allocator = witness_builder.allocator;
    let builder = witness::Builder::new(allocator, Rc::new(RefCell::new(Default::default())));
    let witness_builder = std::mem::replace(witness_builder, WitnessBuilder { allocator, builder });
    to_raw(
        witness_builder
            .builder
            .build()
            .expect("witness::Builder::build failure"),
    )
}

/* --- ConstraintSystem --- */

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_free(ptr: *mut ConstraintSystem<BinaryField128b>) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_validate_witness(
    constraint_system: &ConstraintSystem<BinaryField128b>,
    boundaries: &LeanArrayObject,
    witness: &Witness<'_>,
) -> bool {
    let boundaries = boundaries.to_vec(ctor_ptr_to_boundary);
    validate_witness(constraint_system, &boundaries, witness).is_ok()
}

/* --- ConstraintSystemBuilder --- */

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_new<'a>() -> *const ConstraintSystemBuilder<'a> {
    to_raw(ConstraintSystemBuilder::new())
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_free(ptr: *mut ConstraintSystemBuilder<'_>) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_build(
    builder: &mut ConstraintSystemBuilder<'_>,
) -> *const ConstraintSystem<BinaryField128b> {
    let builder = std::mem::take(builder);
    to_raw(
        builder
            .build()
            .expect("ConstraintSystemBuilder::build failure"),
    )
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_flush_with_multiplicity(
    builder: &mut ConstraintSystemBuilder<'_>,
    direction_pull: bool,
    channel_id: ChannelId,
    count: usize,
    oracle_ids: &LeanArrayObject,
    multiplicity: u64,
) {
    let oracle_ids = oracle_ids.to_vec(boxed_usize_ptr_to_usize);
    use FlushDirection::{Pull, Push};
    let direction = if direction_pull { Pull } else { Push };
    builder
        .flush_with_multiplicity(direction, channel_id, count, oracle_ids, multiplicity)
        .expect("ConstraintSystemBuilder::flush_with_multiplicity failure");
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_flush_custom(
    builder: &mut ConstraintSystemBuilder<'_>,
    direction_pull: bool,
    channel_id: ChannelId,
    selector: OracleId,
    oracle_ids: &LeanArrayObject,
    multiplicity: u64,
) {
    let oracle_ids = oracle_ids.to_vec(boxed_usize_ptr_to_usize);
    use FlushDirection::{Pull, Push};
    let direction = if direction_pull { Pull } else { Push };
    builder
        .flush_custom(direction, channel_id, selector, oracle_ids, multiplicity)
        .expect("ConstraintSystemBuilder::flush_custom failure");
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_assert_zero(
    builder: &mut ConstraintSystemBuilder<'_>,
    name: *const c_char,
    oracle_ids: &LeanArrayObject,
    composition: &LeanCtorObject,
) {
    let oracle_ids = oracle_ids.to_vec(boxed_usize_ptr_to_usize);
    let composition = lean_ctor_to_arith_expr(composition);
    builder.assert_zero(raw_to_str(name), oracle_ids, composition);
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_assert_not_zero(
    builder: &mut ConstraintSystemBuilder<'_>,
    oracle_id: OracleId,
) {
    builder.assert_not_zero(oracle_id);
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_add_channel(
    builder: &mut ConstraintSystemBuilder<'_>,
) -> ChannelId {
    builder.add_channel()
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_add_committed(
    builder: &mut ConstraintSystemBuilder<'_>,
    name: *const c_char,
    n_vars: usize,
    tower_level: usize,
) -> OracleId {
    builder.add_committed(raw_to_str(name), n_vars, tower_level)
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_add_linear_combination(
    builder: &mut ConstraintSystemBuilder<'_>,
    name: *const c_char,
    n_vars: usize,
    inner: &LeanArrayObject,
) -> OracleId {
    let inner = inner.to_vec(ctor_ptr_to_lc_factor);
    builder
        .add_linear_combination(raw_to_str(name), n_vars, inner)
        .expect("ConstraintSystemBuilder::add_linear_combination failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_add_linear_combination_with_offset(
    builder: &mut ConstraintSystemBuilder<'_>,
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

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_add_packed(
    builder: &mut ConstraintSystemBuilder<'_>,
    name: *const c_char,
    oracle_id: OracleId,
    log_degree: usize,
) -> OracleId {
    builder
        .add_packed(raw_to_str(name), oracle_id, log_degree)
        .expect("ConstraintSystemBuilder::add_packed failure")
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_push_namespace(
    builder: &mut ConstraintSystemBuilder<'_>,
    name: *const c_char,
) {
    builder.push_namespace(raw_to_str(name));
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_pop_namespace(
    builder: &mut ConstraintSystemBuilder<'_>,
) {
    builder.pop_namespace();
}

#[unsafe(no_mangle)]
extern "C" fn rs_constraint_system_builder_log_rows(
    builder: &ConstraintSystemBuilder<'_>,
    oracle_ids: &LeanArrayObject,
) -> usize {
    builder
        .log_rows(oracle_ids.to_vec(boxed_usize_ptr_to_usize))
        .expect("ConstraintSystemBuilder::log_rows failure")
}
