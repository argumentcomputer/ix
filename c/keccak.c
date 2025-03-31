#include "lean/lean.h"
#include "common.h"
#include "linear.h"
#include "rust.h"

static lean_external_class *g_keccak256_hasher_class = NULL;

static lean_external_class *get_keccak256_hasher_class() {
    if (g_keccak256_hasher_class == NULL) {
        g_keccak256_hasher_class = lean_register_external_class(
            &rs_keccak256_hasher_free,
            &noop_foreach
        );
    }
    return g_keccak256_hasher_class;
}

extern lean_obj_res c_rs_keccak256_hasher_init() {
    void *hasher = rs_keccak256_hasher_init();
    return lean_alloc_external(get_keccak256_hasher_class(), hasher);
}

extern lean_obj_res c_rs_keccak256_hasher_update(
    lean_obj_arg hasher,
    b_lean_obj_arg input
) {
    void* hasher_cloned = rs_keccak256_hasher_update(lean_get_external_data(hasher), input);
    return lean_alloc_external(get_keccak256_hasher_class(), hasher_cloned);
}

extern lean_obj_res c_rs_keccak256_hasher_finalize(lean_obj_arg hasher) {
    lean_object *buffer = lean_alloc_sarray(1, 0, 32);
    rs_keccak256_hasher_finalize(lean_get_external_data(hasher), buffer);
    return buffer;
}
