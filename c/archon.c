#include "lean/lean.h"
#include "linear.h"
#include "rust.h"

/* --- WitnessModule --- */

extern lean_obj_res c_rs_witness_module_add_entry(lean_obj_arg l_witness) {
    linear_object *linear = validated_linear(l_witness);
    size_t entry_id = rs_witness_module_add_entry(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(entry_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_witness_module_add_entry_with_capacity(
    lean_obj_arg l_witness,
    uint8_t log_bits
) {
    linear_object *linear = validated_linear(l_witness);
    size_t entry_id = rs_witness_module_add_entry_with_capacity(
        get_object_ref(linear),
        log_bits
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(entry_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_witness_module_bind_oracle_to(
    lean_obj_arg l_witness,
    size_t oracle_id,
    size_t entry_id,
    uint8_t tower_level
) {
    linear_object *linear = validated_linear(l_witness);
    rs_witness_module_bind_oracle_to(
        get_object_ref(linear),
        oracle_id,
        entry_id,
        tower_level
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_witness_module_push_u128_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg u128,
    size_t entry_id
) {
    linear_object *linear = validated_linear(l_witness);
    rs_witness_module_push_u128_to(
        get_object_ref(linear),
        lean_get_external_data(u128),
        entry_id
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_witness_module_populate(lean_obj_arg l_witness, uint64_t height) {
    linear_object *linear = validated_linear(l_witness);
    rs_witness_module_populate(get_object_ref(linear), height);
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_compile_witness_modules(
    lean_obj_arg l_witnesses,
    b_lean_obj_arg heights
) {
    size_t size = lean_array_size(l_witnesses);
    lean_object **witnesses_cptrs = lean_array_cptr(l_witnesses);
    void *witnesses_ptrs[size];
    for (size_t i = 0; i < size; i++) {
        linear_object *linear = validated_linear(witnesses_cptrs[i]);
        witnesses_ptrs[i] = get_object_ref(linear);
        ditch_linear(linear);
    }
    void *witness = rs_compile_witness_modules(witnesses_ptrs, heights);
    linear_object *new_linear = linear_object_init(
        witness,
        &rs_witness_free
    );
    return alloc_lean_linear_object(new_linear);
}

/* --- CircuitModule --- */

extern lean_obj_res c_rs_circuit_module_new(size_t module_id) {
    linear_object *linear = linear_object_init(
        rs_circuit_module_new(module_id),
        &rs_circuit_module_free
    );
    return alloc_lean_linear_object(linear);
}

extern lean_obj_res c_rs_circuit_module_freeze_oracles(lean_obj_arg l_circuit) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_freeze_oracles(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_init_witness_module(b_lean_obj_arg l_circuit) {
    linear_object *linear = validated_linear(l_circuit);
    void *witness_module = rs_circuit_module_init_witness_module(get_object_ref(linear));
    linear_object *new_linear = linear_object_init(
        witness_module,
        &rs_witness_module_free
    );
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_flush(
    lean_obj_arg l_circuit,
    bool direction_pull,
    size_t channel_id,
    b_lean_obj_arg oracle_ids,
    uint64_t multiplicity
) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_flush(
        get_object_ref(linear),
        direction_pull,
        channel_id,
        oracle_ids,
        multiplicity
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_assert_zero(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    b_lean_obj_arg oracle_ids,
    b_lean_obj_arg composition
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    rs_circuit_module_assert_zero(
        get_object_ref(linear),
        chars,
        oracle_ids,
        composition
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_assert_not_zero(
    lean_obj_arg l_circuit,
    size_t oracle_id
) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_assert_not_zero(get_object_ref(linear), oracle_id);
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_add_committed(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    uint8_t tower_level
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_id = rs_circuit_module_add_committed(
        get_object_ref(linear),
        chars,
        tower_level
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_transparent(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    b_lean_obj_arg transparent
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_id = rs_circuit_module_add_transparent(
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

extern lean_obj_res c_rs_circuit_module_add_linear_combination(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    b_lean_obj_arg offset,
    b_lean_obj_arg inner
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_id = rs_circuit_module_add_linear_combination(
        get_object_ref(linear),
        chars,
        lean_get_external_data(offset),
        inner
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_id));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_packed(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    size_t oracle_id,
    size_t log_degree
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_id2 = rs_circuit_module_add_packed(
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

extern lean_obj_res c_rs_circuit_module_push_namespace(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    rs_circuit_module_push_namespace(get_object_ref(linear), chars);
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_pop_namespace(lean_obj_arg l_circuit) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_pop_namespace(get_object_ref(linear));
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

/* --- Protocol --- */

extern lean_obj_res c_rs_validate_witness(
    b_lean_obj_arg l_circuit_modules,
    b_lean_obj_arg l_witness,
    b_lean_obj_arg boundaries
) {
    linear_object *witness_linear = validated_linear(l_witness);

    size_t num_modules = lean_array_size(l_circuit_modules);
    lean_object **modules_cptrs = lean_array_cptr(l_circuit_modules);
    void *modules_ptrs[num_modules];
    for (size_t i = 0; i < num_modules; i++) {
        linear_object *linear = validated_linear(modules_cptrs[i]);
        modules_ptrs[i] = get_object_ref(linear);
    }

    c_result *result = rs_validate_witness(
        modules_ptrs,
        num_modules,
        get_object_ref(witness_linear),
        boundaries
    );

    lean_object *except;
    if (result->is_ok) {
        except = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(except, 0, lean_box(0));
    } else {
        except = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(except, 0, lean_mk_string(result->data));
    }
    rs__c_result_unit_string_free(result);

    return except;
}
