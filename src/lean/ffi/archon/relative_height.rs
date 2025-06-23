use crate::{
    archon::RelativeHeight,
    lean::{
        ctor::LeanCtorObject,
        ffi::{as_ref_unsafe, lean_is_scalar},
        sarray::LeanSArrayObject,
    },
    lean_unbox,
};

pub(super) fn lean_ctor_ptr_to_relative_height(ctor: *const LeanCtorObject) -> RelativeHeight {
    if lean_is_scalar(ctor) {
        match lean_unbox!(usize, ctor) {
            0 => RelativeHeight::Base,
            _ => unreachable!(),
        }
    } else {
        let relative_height = as_ref_unsafe(ctor);
        match relative_height.tag() {
            1 => {
                let [n_ptr] = relative_height.objs();
                RelativeHeight::Div2(n_ptr as u8)
            }
            2 => {
                let [n_ptr] = relative_height.objs();
                RelativeHeight::Mul2(n_ptr as u8)
            }
            _ => unreachable!(),
        }
    }
}

fn relative_height_from_bytes(bytes: &[u8]) -> RelativeHeight {
    match bytes[0] {
        0 => RelativeHeight::Base,
        1 => RelativeHeight::Div2(bytes[1]),
        2 => RelativeHeight::Mul2(bytes[1]),
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_relative_height_is_equivalent_to_bytes(
    relative_height_ptr: *const LeanCtorObject,
    bytes: &LeanSArrayObject,
) -> bool {
    lean_ctor_ptr_to_relative_height(relative_height_ptr)
        == relative_height_from_bytes(bytes.data())
}
