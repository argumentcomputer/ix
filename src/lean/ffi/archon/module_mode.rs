use crate::{
    archon::ModuleMode,
    lean::{
        ctor::LeanCtorObject,
        ffi::{as_ref_unsafe, lean_is_scalar},
        sarray::LeanSArrayObject,
    },
    lean_unbox,
};

pub(super) fn lean_ctor_ptr_to_module_mode(ctor: *const LeanCtorObject) -> ModuleMode {
    if lean_is_scalar(ctor) {
        match lean_unbox!(usize, ctor) {
            0 => ModuleMode::Inactive,
            _ => unreachable!(),
        }
    } else {
        let mode = as_ref_unsafe(ctor);
        match mode.tag() {
            1 => {
                let [depth_ptr, log_height_ptr] = mode.objs();
                ModuleMode::active(log_height_ptr as u8, depth_ptr as u64)
            }
            _ => unreachable!(),
        }
    }
}

fn module_mode_from_bytes(bytes: &[u8]) -> ModuleMode {
    match bytes[0] {
        0 => ModuleMode::Inactive,
        1 => {
            let log_height = bytes[1];
            let mut depth_bytes = [0; size_of::<u64>()];
            depth_bytes.copy_from_slice(&bytes[2..2 + size_of::<u64>()]);
            let depth = u64::from_le_bytes(depth_bytes);
            ModuleMode::active(log_height, depth)
        }
        _ => unreachable!(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_module_mode_is_equivalent_to_bytes(
    module_mode_ptr: *const LeanCtorObject,
    bytes: &LeanSArrayObject,
) -> bool {
    lean_ctor_ptr_to_module_mode(module_mode_ptr) == module_mode_from_bytes(bytes.data())
}
