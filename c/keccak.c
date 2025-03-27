#include "lean/lean.h"
#include "common.h"
#include "linear.h"
#include "rust.h"

extern lean_obj_res c_rs_keccak256_hash(b_lean_obj_arg input) {
    lean_object *output = lean_alloc_sarray(1, 0, 32);
    rs_keccak256_hash(input, output);

    return output;
}
