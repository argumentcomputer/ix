#include "lean/lean.h"
#include "rust.h"

static void noop_foreach(void *mod, b_lean_obj_arg fn) {}

static void constraint_system_builder_finalizer(void *rs_csb) {
    rs_constraint_system_builder_free(rs_csb);
    rs_csb = NULL;
}

static lean_external_class *g_constraint_system_builder_class = NULL;

static lean_external_class *get_constraint_system_builder_class() {
    if (g_constraint_system_builder_class == NULL) {
        g_constraint_system_builder_class = lean_register_external_class(
            &constraint_system_builder_finalizer,
            &noop_foreach
        );
    }
    return g_constraint_system_builder_class;
}

extern lean_obj_res c_constraint_system_builder_init() {
    void *rs_csb = rs_constraint_system_builder_init();
    return lean_alloc_external(get_constraint_system_builder_class(), rs_csb);
}

extern lean_obj_res c_constraint_system_builder_add_channel(lean_obj_arg l_csb) {
    void *rs_csb = lean_get_external_data(l_csb);
    size_t channel_id = rs_constraint_system_builder_add_channel(rs_csb);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(channel_id));
    lean_ctor_set(tuple, 1, l_csb);
    return tuple;
}
