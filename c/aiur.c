#include "lean/lean.h"
#include "rust.h"

extern lean_obj_res c_rs_toplevel_execute_test(
    b_lean_obj_arg toplevel,
    b_lean_obj_arg fun_idx,
    b_lean_obj_arg args,
    size_t output_size
) {
    lean_obj_res output = lean_alloc_array(output_size, output_size);
    rs_toplevel_execute_test(toplevel, fun_idx, args, output);
    return output;
}
