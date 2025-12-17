#include "lean/lean.h"
#include "rust.h"

extern lean_obj_res c_rs_compile_consts(b_lean_obj_arg name, b_lean_obj_arg env) {
    lean_object *const_addr_bytes = lean_alloc_sarray(1, 32, 32);
    compiled_consts_data *ced = rs_compile_consts(name, env, const_addr_bytes);
    size_t size = ced->size;
    size_t *ser_sizes = ced->ser_sizes;
    lean_object *array = lean_alloc_array(size, size);
    lean_object **array_values = lean_array_cptr(array);
    for (size_t i = 0; i < size; i++) {
        lean_object *pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, lean_alloc_sarray(1, 32, 32));
        lean_ctor_set(pair, 1, lean_alloc_sarray(1, ser_sizes[i], ser_sizes[i]));
        array_values[i] = pair;
    }
    rs_move_compiled_consts(array, ced);

    lean_object *res = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(res, 0, const_addr_bytes);
    lean_ctor_set(res, 1, array);
    return res;
}
