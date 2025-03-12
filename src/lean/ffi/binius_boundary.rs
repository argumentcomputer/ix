use binius_core::constraint_system::channel::{Boundary, FlushDirection};
use binius_field::BinaryField128b;
use std::ffi::c_void;

use crate::lean::{
    array::LeanArrayObject,
    ctor::LeanCtorObject,
    ffi::{
        as_ref_unsafe,
        binius::{boxed_usize_ptr_to_usize, external_ptr_to_u128},
    },
    sarray::LeanSArrayObject,
};

pub(super) fn ctor_ptr_to_boundary(ptr: *const c_void) -> Boundary<BinaryField128b> {
    let ctor = as_ref_unsafe(ptr.cast::<LeanCtorObject>());
    let [values_ptr, channel_id_ptr, multiplicity_ptr, direction_ptr] = ctor.objs();
    let values = as_ref_unsafe(values_ptr.cast::<LeanArrayObject>()).to_vec(external_ptr_to_u128);
    let values = values.into_iter().map(BinaryField128b::new).collect();
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

fn boundary_from_bytes(bytes: &[u8]) -> Boundary<BinaryField128b> {
    let mut usize_bytes = [0; size_of::<usize>()];
    usize_bytes.copy_from_slice(&bytes[..size_of::<usize>()]);
    let num_values = usize::from_le_bytes(usize_bytes);
    let mut values = Vec::with_capacity(num_values);
    let values_start = size_of::<usize>();
    let mut u128_bytes = [0; size_of::<u128>()];
    for i in 0..num_values {
        let u128_start = values_start + i * size_of::<u128>();
        u128_bytes.copy_from_slice(&bytes[u128_start..u128_start + size_of::<u128>()]);
        values.push(BinaryField128b::new(u128::from_le_bytes(u128_bytes)));
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
