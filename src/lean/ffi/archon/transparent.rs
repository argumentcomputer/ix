use binius_field::BinaryField128b as B128;

use crate::{
    archon::transparent::Transparent,
    lean::{
        ctor::LeanCtorObject,
        ffi::{as_ref_unsafe, external_ptr_to_u128, lean_is_scalar},
        sarray::LeanSArrayObject,
    },
    lean_unbox,
};

pub(super) fn lean_ctor_ptr_to_transparent(ctor: *const LeanCtorObject) -> Transparent {
    if lean_is_scalar(ctor) {
        match lean_unbox!(usize, ctor) {
            1 => Transparent::Incremental,
            _ => unreachable!(),
        }
    } else {
        let transparent = as_ref_unsafe(ctor);
        match transparent.tag() {
            0 => {
                let [value_ptr] = transparent.objs();
                Transparent::Constant(B128::new(external_ptr_to_u128(value_ptr)))
            }
            _ => unreachable!(),
        }
    }
}

fn transparent_from_bytes(bytes: &[u8]) -> Transparent {
    match bytes[0] {
        0 => {
            let mut slice = [0; size_of::<u128>()];
            slice.copy_from_slice(&bytes[1..size_of::<u128>() + 1]);
            let u = u128::from_le_bytes(slice);
            Transparent::Constant(B128::new(u))
        }
        1 => Transparent::Incremental,
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_transparent_is_equivalent_to_bytes(
    transparent_ptr: *const LeanCtorObject,
    bytes: &LeanSArrayObject,
) -> bool {
    lean_ctor_ptr_to_transparent(transparent_ptr) == transparent_from_bytes(bytes.data())
}
