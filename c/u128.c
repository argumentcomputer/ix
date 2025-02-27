#include "lean/lean.h"
#include "common.h"
#include "rust.h"

static lean_external_class *g_u128_class = NULL;

static lean_external_class *get_u128_class() {
    if (g_u128_class == NULL) {
        g_u128_class = lean_register_external_class(
            &rs_u128_free,
            &noop_foreach
        );
    }
    return g_u128_class;
}

extern lean_obj_res c_rs_u128_of_hi_lo(uint64_t hi, uint64_t lo) {
    return lean_alloc_external(get_u128_class(), rs_u128_of_hi_lo(hi, lo));
}
