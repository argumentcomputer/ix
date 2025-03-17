#include "lean/lean.h"
#include "common.h"
#include "linear.h"
#include "rust.h"

/* --- Witness --- */

static lean_external_class *g_witness_class = NULL;

static lean_external_class *get_witness_class() {
    if (g_witness_class == NULL) {
        g_witness_class = lean_register_external_class(
            &rs_witness_free,
            &noop_foreach
        );
    }
    return g_witness_class;
}

/* --- WitnessBuilder --- */

extern lean_obj_res c_rs_witness_builder_new(b_lean_obj_arg l_cs) {
    linear_object *linear = linear_object_init(
        rs_witness_builder_new(lean_get_external_data(l_cs)),
        &rs_witness_builder_free
    );
    return alloc_lean_linear_object(linear);
}

extern lean_obj_res c_rs_witness_builder_with_column(
    lean_obj_arg l_wb,
    size_t oracle_id,
    b_lean_obj_arg column_data
) {
    linear_object *linear = validated_linear(l_wb);

    rs_witness_builder_with_column(
        get_object_ref(linear),
        oracle_id,
        column_data
    );
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_witness_builder_with_column_default(
    lean_obj_arg l_wb,
    size_t oracle_id,
    b_lean_obj_arg value
) {
    linear_object *linear = validated_linear(l_wb);

    rs_witness_builder_with_column_default(
        get_object_ref(linear),
        oracle_id,
        value
    );
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_witness_builder_build(lean_obj_arg l_wb) {
    linear_object *linear = validated_linear(l_wb);

    void *witness = rs_witness_builder_build(get_object_ref(linear));
    ditch_linear(linear);

    return lean_alloc_external(get_witness_class(), witness);
}

/* --- ConstraintSystem --- */

static lean_external_class *g_constraint_system_class = NULL;

static lean_external_class *get_constraint_system_class() {
    if (g_constraint_system_class == NULL) {
        g_constraint_system_class = lean_register_external_class(
            &rs_constraint_system_free,
            &noop_foreach
        );
    }
    return g_constraint_system_class;
}

extern lean_obj_res c_rs_constraint_system_validate_witness(
    b_lean_obj_arg l_cs,
    b_lean_obj_arg boundaries,
    b_lean_obj_arg witness
) {
    c_result *result = rs_constraint_system_validate_witness(
        lean_get_external_data(l_cs),
        boundaries,
        lean_get_external_data(witness)
    );

    lean_object *except;
    if (result->is_ok) {
        except = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(except, 0, lean_box(0));
    } else {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }
    rs_constraint_system_validate_witness_result_free(result);

    return except;
}

/* --- ConstraintSystemBuilder --- */

extern lean_obj_res c_rs_constraint_system_builder_new() {
    linear_object *linear = linear_object_init(
        rs_constraint_system_builder_new(),
        &rs_constraint_system_builder_free
    );
    return alloc_lean_linear_object(linear);
}

extern lean_obj_res c_rs_constraint_system_builder_build(lean_obj_arg l_csb) {
    linear_object *linear = validated_linear(l_csb);

    void *constraint_system = rs_constraint_system_builder_build(get_object_ref(linear));
    ditch_linear(linear);

    return lean_alloc_external(get_constraint_system_class(), constraint_system);
}

extern lean_obj_res c_rs_constraint_system_builder_flush_with_multiplicity(
    lean_obj_arg l_csb,
    bool direction_pull,
    size_t channel_id,
    size_t count,
    b_lean_obj_arg oracle_ids,
    uint64_t multiplicity
) {
    linear_object *linear = validated_linear(l_csb);

    rs_constraint_system_builder_flush_with_multiplicity(
        get_object_ref(linear),
        direction_pull,
        channel_id,
        count,
        oracle_ids,
        multiplicity
    );
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_constraint_system_builder_flush_custom(
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

extern lean_obj_res c_rs_constraint_system_builder_assert_zero(
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

extern lean_obj_res c_rs_constraint_system_builder_assert_not_zero(
    lean_obj_arg l_csb,
    size_t oracle_id
) {
    linear_object *linear = validated_linear(l_csb);

    rs_constraint_system_builder_assert_not_zero(get_object_ref(linear), oracle_id);
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_constraint_system_builder_add_channel(lean_obj_arg l_csb) {
    linear_object *linear = validated_linear(l_csb);

    size_t channel_id = rs_constraint_system_builder_add_channel(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(channel_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_constraint_system_builder_add_committed(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    size_t n_vars,
    uint8_t tower_level
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

extern lean_obj_res c_rs_constraint_system_builder_add_linear_combination(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    size_t n_vars,
    b_lean_obj_arg inner
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    size_t oracle_id = rs_constraint_system_builder_add_linear_combination(
        get_object_ref(linear),
        chars,
        n_vars,
        inner
    );
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_constraint_system_builder_add_linear_combination_with_offset(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    size_t n_vars,
    b_lean_obj_arg offset,
    b_lean_obj_arg inner
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    size_t oracle_id = rs_constraint_system_builder_add_linear_combination_with_offset(
        get_object_ref(linear),
        chars,
        n_vars,
        lean_get_external_data(offset),
        inner
    );
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_constraint_system_builder_add_packed(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    size_t oracle_id,
    size_t log_degree
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    size_t oracle_id2 = rs_constraint_system_builder_add_packed(
        get_object_ref(linear),
        chars,
        oracle_id,
        log_degree
    );
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id2));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_constraint_system_builder_add_transparent(
    lean_obj_arg l_csb,
    b_lean_obj_arg name,
    b_lean_obj_arg transparent
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    size_t oracle_id = rs_constraint_system_builder_add_transparent(
        get_object_ref(linear),
        chars,
        transparent
    );
    linear_object *new_linear = linear_bump(linear);

    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_constraint_system_builder_push_namespace(
    lean_obj_arg l_csb,
    b_lean_obj_arg name
) {
    linear_object *linear = validated_linear(l_csb);
    char const *chars = lean_string_cstr(name);

    rs_constraint_system_builder_push_namespace(get_object_ref(linear), chars);
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_constraint_system_builder_pop_namespace(lean_obj_arg l_csb) {
    linear_object *linear = validated_linear(l_csb);

    rs_constraint_system_builder_pop_namespace(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);

    return alloc_lean_linear_object(new_linear);
}

extern size_t c_rs_constraint_system_builder_log_rows(
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
