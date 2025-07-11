use crate::{
    aiur2::bytecode::Toplevel,
    lean::{array::LeanArrayObject, ctor::LeanCtorObject, ffi::as_ref_unsafe},
    lean_unbox,
};

fn lean_ctor_to_toplevel(ctor: &LeanCtorObject) -> Toplevel {
    let [functions_ptr, memory_widths_ptr] = ctor.objs();
    let memory_widths_array: &LeanArrayObject = as_ref_unsafe(memory_widths_ptr.cast());
    let memory_widths = memory_widths_array.to_vec(|ptr| lean_unbox!(usize, ptr));
    Toplevel {
        functions: vec![],
        memory_widths,
    }
}
