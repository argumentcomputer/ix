use binius_core::constraint_system::channel::{Boundary, FlushDirection};
use binius_field::{BinaryField64b as B64, BinaryField128b as B128, Field};
use std::ffi::c_void;

use crate::lean::{
    array::LeanArrayObject,
    ctor::LeanCtorObject,
    ffi::{as_ref_unsafe, boxed_usize_ptr_to_usize, external_ptr_to_u128, to_raw},
    sarray::LeanSArrayObject,
};

pub(super) fn ctor_ptr_to_boundary(ptr: *const c_void) -> Boundary<B128> {
    let ctor = as_ref_unsafe(ptr.cast::<LeanCtorObject>());
    let [values_ptr, channel_id_ptr, multiplicity_ptr, direction_ptr] = ctor.objs();
    let values = as_ref_unsafe(values_ptr.cast::<LeanArrayObject>()).to_vec(external_ptr_to_u128);
    let values = values.into_iter().map(B128::new).collect();
    let channel_id = boxed_usize_ptr_to_usize(channel_id_ptr);
    let multiplicity = multiplicity_ptr as u64;
    let direction_pull = direction_ptr as usize == 1;
    use FlushDirection::{Pull, Push};
    let direction = if direction_pull { Pull } else { Push };
    Boundary {
        values,
        channel_id,
        direction,
        multiplicity,
    }
}

fn boundary_from_bytes(bytes: &[u8]) -> Boundary<B128> {
    let mut usize_bytes = [0; size_of::<usize>()];
    usize_bytes.copy_from_slice(&bytes[..size_of::<usize>()]);
    let num_values = usize::from_le_bytes(usize_bytes);
    let mut values = Vec::with_capacity(num_values);
    let values_start = size_of::<usize>();
    let mut u128_bytes = [0; size_of::<u128>()];
    for i in 0..num_values {
        let u128_start = values_start + i * size_of::<u128>();
        u128_bytes.copy_from_slice(&bytes[u128_start..u128_start + size_of::<u128>()]);
        values.push(B128::new(u128::from_le_bytes(u128_bytes)));
    }
    let channel_start = values_start + num_values * size_of::<u128>();
    usize_bytes.copy_from_slice(&bytes[channel_start..channel_start + size_of::<usize>()]);
    let channel_id = usize::from_le_bytes(usize_bytes);
    let direction_idx = channel_start + size_of::<usize>();
    let direction_byte = bytes[direction_idx];
    use FlushDirection::{Pull, Push};
    let direction = if direction_byte == 0 { Push } else { Pull };
    let multiplicity_start = direction_idx + size_of::<u8>();
    let mut u64_bytes = [0; size_of::<u64>()];
    u64_bytes.copy_from_slice(&bytes[multiplicity_start..]);
    let multiplicity = u64::from_le_bytes(u64_bytes);
    Boundary {
        values,
        channel_id,
        direction,
        multiplicity,
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_binius_boundary_is_equivalent_to_bytes(
    boundary_ptr: *const c_void,
    bytes: &LeanSArrayObject,
) -> bool {
    ctor_ptr_to_boundary(boundary_ptr) == boundary_from_bytes(bytes.data())
}

#[unsafe(no_mangle)]
extern "C" fn rs_add_u128_in_binary_field(a: &u128, b: &u128) -> *const u128 {
    let a = B128::new(*a);
    let b = B128::new(*b);
    let c = a + b;
    to_raw(c.val())
}

#[unsafe(no_mangle)]
extern "C" fn rs_mul_u128_in_binary_field(a: &u128, b: &u128) -> *const u128 {
    let a = B128::new(*a);
    let b = B128::new(*b);
    let c = a * b;
    to_raw(c.val())
}

#[unsafe(no_mangle)]
extern "C" fn rs_mul_u64_in_binary_field(a: u64, b: u64) -> u64 {
    let a = B64::new(a);
    let b = B64::new(b);
    let c = a * b;
    c.val()
}

#[unsafe(no_mangle)]
extern "C" fn rs_pow_u64_in_binary_field(a: u64, b: u64) -> u64 {
    let a = B64::new(a);
    let c = a.pow([b]);
    c.val()
}

#[unsafe(no_mangle)]
extern "C" fn rs_pow_u128_in_binary_field(a: &u128, b: u64) -> *const u128 {
    let a = B128::new(*a);
    let c = a.pow([b]);
    to_raw(c.val())
}

#[unsafe(no_mangle)]
extern "C" fn rs_inv_u64_in_binary_field(a: u64) -> u64 {
    let a = B64::new(a);
    let c = a.invert().unwrap_or(B64::new(0));
    c.val()
}
