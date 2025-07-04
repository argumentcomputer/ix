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
    size_t oracle_idx,
    size_t entry_id,
    uint8_t tower_level
) {
    linear_object *linear = validated_linear(l_witness);
    rs_witness_module_bind_oracle_to(
        get_object_ref(linear),
        oracle_idx,
        entry_id,
        tower_level
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

static inline lean_obj_res c_rs_witness_module_push_data_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg data,
    size_t entry_id,
    void (*rs_fn)(void*, b_lean_obj_arg, size_t)
) {
    linear_object *linear = validated_linear(l_witness);
    rs_fn(get_object_ref(linear), data, entry_id);
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_witness_module_push_u8s_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg u8s,
    size_t entry_id
) {
    return c_rs_witness_module_push_data_to(
        l_witness,
        u8s,
        entry_id,
        rs_witness_module_push_u8s_to
    );
}

extern lean_obj_res c_rs_witness_module_push_u16s_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg u16s,
    size_t entry_id
) {
    return c_rs_witness_module_push_data_to(
        l_witness,
        u16s,
        entry_id,
        rs_witness_module_push_u16s_to
    );
}

extern lean_obj_res c_rs_witness_module_push_u32s_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg u32s,
    size_t entry_id
) {
    return c_rs_witness_module_push_data_to(
        l_witness,
        u32s,
        entry_id,
        rs_witness_module_push_u32s_to
    );
}

extern lean_obj_res c_rs_witness_module_push_u64s_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg u64s,
    size_t entry_id
) {
    return c_rs_witness_module_push_data_to(
        l_witness,
        u64s,
        entry_id,
        rs_witness_module_push_u64s_to
    );
}

extern lean_obj_res c_rs_witness_module_push_u128s_to(
    lean_obj_arg l_witness,
    b_lean_obj_arg u128s,
    size_t entry_id
) {
    return c_rs_witness_module_push_data_to(
        l_witness,
        u128s,
        entry_id,
        rs_witness_module_push_u128s_to
    );
}

extern lean_obj_res c_rs_witness_module_populate(
    lean_obj_arg l_witness,
    b_lean_obj_arg mode
) {
    linear_object *linear = validated_linear(l_witness);
    rs_witness_module_populate(get_object_ref(linear), mode);
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_witness_module_par_populate(
    lean_obj_arg l_witnesses,
    b_lean_obj_arg modes
) {
    size_t size = lean_array_size(l_witnesses);
    lean_object **witnesses_cptrs = lean_array_cptr(l_witnesses);
    void *witnesses_ptrs[size];
    lean_object *new_l_witnesses = lean_alloc_array(size, size);
    lean_object **new_witnesses_cptrs = lean_array_cptr(new_l_witnesses);
    for (size_t i = 0; i < size; i++) {
        linear_object *linear = validated_linear(witnesses_cptrs[i]);
        witnesses_ptrs[i] = get_object_ref(linear);
        new_witnesses_cptrs[i] = alloc_lean_linear_object(linear_bump(linear));
    }
    rs_witness_module_par_populate(witnesses_ptrs, modes);
    return new_l_witnesses;
}

extern lean_obj_res c_rs_witness_module_get_data(
    b_lean_obj_arg l_witness,
    size_t oracle_idx
) {
    linear_object *linear = validated_linear(l_witness);
    lean_object *witness_module = get_object_ref(linear);
    size_t size = rs_witness_module_get_data_num_bytes(witness_module, oracle_idx);
    lean_object *byte_array = lean_alloc_sarray(1, size, size);
    rs_witness_module_get_data(witness_module, oracle_idx, byte_array);
    return byte_array;
}

extern lean_obj_res c_rs_compile_witness_modules(
    lean_obj_arg l_witnesses,
    b_lean_obj_arg modes
) {
    size_t size = lean_array_size(l_witnesses);
    lean_object **witnesses_cptrs = lean_array_cptr(l_witnesses);
    void *witnesses_ptrs[size];
    for (size_t i = 0; i < size; i++) {
        linear_object *linear = validated_linear(witnesses_cptrs[i]);
        witnesses_ptrs[i] = get_object_ref(linear);
        ditch_linear(linear);
    }
    void *witness = rs_compile_witness_modules(witnesses_ptrs, modes);
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
    size_t selector,
    b_lean_obj_arg values,
    uint64_t multiplicity
) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_flush(
        get_object_ref(linear),
        direction_pull,
        channel_id,
        selector,
        values,
        multiplicity
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_assert_zero(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    b_lean_obj_arg oracle_idxs,
    b_lean_obj_arg composition
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    rs_circuit_module_assert_zero(
        get_object_ref(linear),
        chars,
        oracle_idxs,
        composition
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_assert_not_zero(
    lean_obj_arg l_circuit,
    size_t oracle_idx
) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_assert_not_zero(get_object_ref(linear), oracle_idx);
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_assert_exp(
    lean_obj_arg l_circuit,
    b_lean_obj_arg exp_bits,
    size_t result,
    b_lean_obj_arg base
) {
    linear_object *linear = validated_linear(l_circuit);
    rs_circuit_module_assert_exp(
        get_object_ref(linear),
        exp_bits,
        result,
        base
    );
    linear_object *new_linear = linear_bump(linear);
    return alloc_lean_linear_object(new_linear);
}

extern lean_obj_res c_rs_circuit_module_add_committed(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    uint8_t tower_level,
    b_lean_obj_arg relative_height
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_idx = rs_circuit_module_add_committed(
        get_object_ref(linear),
        chars,
        tower_level,
        relative_height
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_idx));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_transparent(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    b_lean_obj_arg transparent,
    b_lean_obj_arg relative_height
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_idx = rs_circuit_module_add_transparent(
        get_object_ref(linear),
        chars,
        transparent,
        relative_height
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_idx));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_linear_combination(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    b_lean_obj_arg offset,
    b_lean_obj_arg inner,
    b_lean_obj_arg relative_height
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_idx = rs_circuit_module_add_linear_combination(
        get_object_ref(linear),
        chars,
        lean_get_external_data(offset),
        inner,
        relative_height
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_idx));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_packed(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    size_t inner,
    size_t log_degree
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_idx = rs_circuit_module_add_packed(
        get_object_ref(linear),
        chars,
        inner,
        log_degree
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_idx));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_shifted(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    size_t inner,
    uint32_t shift_offset,
    size_t block_bits,
    uint8_t shift_variant
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_idx = rs_circuit_module_add_shifted(
        get_object_ref(linear),
        chars,
        inner,
        shift_offset,
        block_bits,
        shift_variant
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_idx));
    lean_ctor_set(tuple, 1, alloc_lean_linear_object(new_linear));
    return tuple;
}

extern lean_obj_res c_rs_circuit_module_add_projected(
    lean_obj_arg l_circuit,
    b_lean_obj_arg name,
    size_t inner,
    uint64_t selection,
    size_t chunk_size
) {
    linear_object *linear = validated_linear(l_circuit);
    char const *chars = lean_string_cstr(name);
    size_t oracle_idx = rs_circuit_module_add_projected(
        get_object_ref(linear),
        chars,
        inner,
        selection,
        chunk_size
    );
    linear_object *new_linear = linear_bump(linear);
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_usize(oracle_idx));
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

extern lean_obj_res c_rs_circuit_module_canonical_bytes(b_lean_obj_arg l_circuit) {
    linear_object *linear = validated_linear(l_circuit);
    void *circuit = get_object_ref(linear);
    size_t size = rs_circuit_module_canonical_bytes_size(circuit);
    lean_object *byte_array = lean_alloc_sarray(1, size, size);
    rs_circuit_module_canonical_bytes(circuit, size, lean_sarray_cptr(byte_array));
    return byte_array;
}

/* --- Protocol --- */

extern lean_obj_res c_rs_validate_witness(
    b_lean_obj_arg l_circuit_modules,
    b_lean_obj_arg boundaries,
    b_lean_obj_arg l_witness
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
        num_modules,
        modules_ptrs,
        boundaries,
        get_object_ref(witness_linear)
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

extern lean_obj_res c_rs_prove(
    b_lean_obj_arg l_circuit_modules,
    b_lean_obj_arg boundaries,
    size_t log_inv_rate,
    size_t security_bits,
    lean_obj_arg l_witness
) {
    linear_object *witness_linear = validated_linear(l_witness);

    size_t num_modules = lean_array_size(l_circuit_modules);
    lean_object **modules_cptrs = lean_array_cptr(l_circuit_modules);
    void *modules_ptrs[num_modules];
    for (size_t i = 0; i < num_modules; i++) {
        linear_object *linear = validated_linear(modules_cptrs[i]);
        modules_ptrs[i] = get_object_ref(linear);
    }

    void *proof = rs_prove(
        num_modules,
        modules_ptrs,
        boundaries,
        log_inv_rate,
        security_bits,
        get_object_ref(witness_linear)
    );
    ditch_linear(witness_linear);

    linear_object *proof_linear = linear_object_init(proof, &rs_proof_free);
    return alloc_lean_linear_object(proof_linear);
}

extern lean_obj_res c_rs_verify(
    b_lean_obj_arg l_circuit_modules,
    b_lean_obj_arg boundaries,
    size_t log_inv_rate,
    size_t security_bits,
    lean_obj_arg l_proof
) {
    linear_object *proof_linear = validated_linear(l_proof);

    size_t num_modules = lean_array_size(l_circuit_modules);
    lean_object **modules_cptrs = lean_array_cptr(l_circuit_modules);
    void *modules_ptrs[num_modules];
    for (size_t i = 0; i < num_modules; i++) {
        linear_object *linear = validated_linear(modules_cptrs[i]);
        modules_ptrs[i] = get_object_ref(linear);
    }

    c_result *result = rs_verify(
        num_modules,
        modules_ptrs,
        boundaries,
        log_inv_rate,
        security_bits,
        get_object_ref(proof_linear)
    );

    ditch_linear(proof_linear);

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

extern lean_obj_res c_rs_proof_to_bytes(b_lean_obj_arg l_proof) {
    linear_object *proof_linear = validated_linear(l_proof);
    void *proof = get_object_ref(proof_linear);
    size_t proof_size = rs_proof_size(proof);
    lean_object *byte_array = lean_alloc_sarray(1, proof_size, proof_size);
    rs_proof_to_bytes(proof, proof_size, lean_sarray_cptr(byte_array));
    return byte_array;
}

extern lean_obj_res c_rs_proof_of_bytes(b_lean_obj_arg byte_array) {
    void *proof = rs_proof_of_bytes(byte_array);
    linear_object *proof_linear = linear_object_init(proof, &rs_proof_free);
    return alloc_lean_linear_object(proof_linear);
}
