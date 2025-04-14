use binius_circuits::builder::{ConstraintSystemBuilder, witness};
use binius_core::{
    constraint_system::{
        ConstraintSystem,
        channel::{ChannelId, FlushDirection},
        validate::validate_witness,
    },
    oracle::OracleId,
    transparent::constant::Constant,
    witness::MultilinearExtensionIndex,
};
use binius_field::{
    BinaryField8b, BinaryField16b, BinaryField32b, BinaryField64b, BinaryField128b,
    arch::OptimalUnderlier,
};
use bumpalo::Bump;
use std::{
    cell::RefCell,
    ffi::{CString, c_char, c_void},
    ptr,
    rc::Rc,
};

use crate::{
    lean::{
        array::LeanArrayObject,
        boxed::BoxedUSize,
        ctor::LeanCtorObject,
        external::LeanExternalObject,
        ffi::{
            CResult, as_ref_unsafe, binius_arith_expr::lean_ctor_to_arith_expr,
            binius_boundary::ctor_ptr_to_boundary, drop_raw, raw_to_str, to_raw,
        },
        sarray::LeanSArrayObject,
    },
    lean_unbox,
};

use super::{lean_unbox_u32, lean_unbox_u64};

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
    column_data: &LeanCtorObject,
) {
    macro_rules! populate {
        ($bf:ident, $t:ident, $f:expr) => {{
            let [array_ptr] = column_data.objs();
            let inner: &LeanArrayObject = as_ref_unsafe(array_ptr.cast());
            witness_builder
                .builder
                .new_column::<$bf>(oracle_id)
                .as_mut_slice::<$t>()
                .iter_mut()
                .zip(inner.data())
                .for_each(|(u, &boxed)| *u = $f(boxed));
        }};
    }
    match column_data.tag() {
        0 => {
            // raw
            let [bytes_ptr] = column_data.objs();
            let bytes: &LeanSArrayObject = as_ref_unsafe(bytes_ptr.cast());
            witness_builder
                .builder
                .new_column::<BinaryField8b>(oracle_id)
                .as_mut_slice()
                .copy_from_slice(bytes.data());
        }
        1 => populate!(BinaryField8b, u8, |boxed| lean_unbox!(u8, boxed)),
        2 => populate!(BinaryField16b, u16, |boxed| lean_unbox!(u16, boxed)),
        3 => populate!(BinaryField32b, u32, lean_unbox_u32),
        4 => populate!(BinaryField64b, u64, lean_unbox_u64),
        5 => populate!(BinaryField128b, u128, external_ptr_to_u128),
        _ => panic!("Invalid tag for ColumnData"),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_witness_builder_with_column_default(
    witness_builder: &WitnessBuilder<'_>,
    oracle_id: OracleId,
    value: &LeanCtorObject,
) {
    macro_rules! populate {
        ($t:ident, $f:expr) => {{
            let [ptr] = value.objs();
            witness_builder
                .builder
                .new_column_with_default::<$t>(oracle_id, $t::new($f(ptr)));
        }};
    }
    match value.tag() {
        0 => populate!(BinaryField8b, |ptr| ptr as u8),
        1 => populate!(BinaryField16b, |ptr| ptr as u16),
        2 => populate!(BinaryField32b, |ptr| ptr as u32),
        3 => populate!(BinaryField64b, |ptr| ptr as u64),
        4 => populate!(BinaryField128b, external_ptr_to_u128),
        _ => panic!("Invalid tag for BinaryFieldValue"),
    }
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
) -> *const CResult {
    let boundaries = boundaries.to_vec(ctor_ptr_to_boundary);
    let c_result = match validate_witness(constraint_system, &boundaries, witness) {
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
    tower_level: u8,
) -> OracleId {
    builder.add_committed(raw_to_str(name), n_vars, tower_level as usize)
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
extern "C" fn rs_constraint_system_builder_add_transparent(
    builder: &mut ConstraintSystemBuilder<'_>,
    name: *const c_char,
    transparent: &LeanCtorObject,
) -> OracleId {
    match transparent.tag() {
        0 => {
            // constant
            let [value_ptr, n_vars_ptr] = transparent.objs();
            let n_vars = n_vars_ptr as usize;
            let value: &LeanCtorObject = as_ref_unsafe(value_ptr.cast());
            let [value_ptr] = value.objs();
            let constant = match value.tag() {
                0 => Constant::new(n_vars, BinaryField8b::new(value_ptr as u8)),
                1 => Constant::new(n_vars, BinaryField16b::new(value_ptr as u16)),
                2 => Constant::new(n_vars, BinaryField32b::new(value_ptr as u32)),
                3 => Constant::new(n_vars, BinaryField64b::new(value_ptr as u64)),
                4 => Constant::new(
                    n_vars,
                    BinaryField128b::new(external_ptr_to_u128(value_ptr)),
                ),
                _ => panic!("Invalid tag for BinaryFieldValue"),
            };
            builder.add_transparent(raw_to_str(name), constant).unwrap()
        }
        _ => panic!("Invalid tag for Transparent"),
    }
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
