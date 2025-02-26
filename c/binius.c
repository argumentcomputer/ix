#include "lean/lean.h"
#include "common.h"
#include "linear.h"
#include "rust.h"

/* --- ConstraintSystem --- */

static lean_external_class *g_constraint_system_class = NULL;

static lean_external_class *get_constraint_system_class() {
    if (g_constraint_system_class == NULL) {
        g_constraint_system_class = lean_register_external_class(
            &rs_constraint_system_free,
            &noop_foreach
        );
    }
    return g_linear_object_class;
}

/* --- ConstraintSystemBuilder --- */

extern lean_obj_res c_constraint_system_builder_init() {
    linear_object *linear = linear_object_init(
        rs_constraint_system_builder_init(),
        &rs_constraint_system_builder_free
    );
    return alloc_lean_linear_object(linear);
}

extern lean_obj_res c_constraint_system_builder_build(lean_obj_arg l_csb) {
    linear_object *linear = validated_linear(l_csb);

    void *constraint_system = rs_constraint_system_builder_build(get_object_ref(linear));
    mark_outdated(linear);

    return lean_alloc_external(get_constraint_system_class(), constraint_system);
}

extern lean_obj_res c_constraint_system_builder_flush_custom(
    lean_obj_arg l_csb,
    bool direction_pull,
    size_t channel_id,
    size_t selector,
    b_lean_obj_arg oracle_ids,
    uint64_t multiplicity
) {
    linear_object *linear = validated_linear(l_csb);

    rs_constraint_system_builder_flush_custom(
        get_object_ref(linear),
        direction_pull,
        channel_id,
        selector,
        oracle_ids,
        multiplicity
    );
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_constraint_system_builder_assert_zero(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    b_lean_obj_arg oracle_ids,
    b_lean_obj_arg composition
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    rs_constraint_system_builder_assert_zero(
        get_object_ref(linear),
        chars,
        oracle_ids,
        composition
    );
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_constraint_system_builder_assert_not_zero(
    lean_obj_arg l_csb,
    size_t oracle_id
) {
    linear_object *linear = validated_linear(l_csb);

    rs_constraint_system_builder_assert_not_zero(get_object_ref(linear), oracle_id);
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_constraint_system_builder_add_channel(lean_obj_arg l_csb) {
    linear_object *linear = validated_linear(l_csb);

    size_t channel_id = rs_constraint_system_builder_add_channel(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(channel_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_constraint_system_builder_add_committed(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    size_t n_vars,
    size_t tower_level
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    size_t oracle_id = rs_constraint_system_builder_add_committed(
        get_object_ref(linear),
        chars,
        n_vars,
        tower_level
    );
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_constraint_system_builder_push_namespace(
    lean_obj_arg l_csb,
    b_lean_obj_arg name
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    rs_constraint_system_builder_push_namespace(get_object_ref(linear), chars);
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_constraint_system_builder_pop_namespace(lean_obj_arg l_csb) {
    linear_object *linear = validated_linear(l_csb);

    rs_constraint_system_builder_pop_namespace(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern size_t c_constraint_system_builder_log_rows(
    b_lean_obj_arg l_csb,
    b_lean_obj_arg oracle_ids
) {
    linear_object *linear = validated_linear(l_csb);
    size_t log_rows = rs_constraint_system_builder_log_rows(
        get_object_ref(linear),
        oracle_ids
    );
    return log_rows;
}
