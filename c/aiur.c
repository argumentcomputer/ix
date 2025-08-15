#include "lean/lean.h"
#include "common.h"
#include "rust.h"

static lean_external_class *g_aiur_proof_class = NULL;

static lean_external_class *get_aiur_proof_class() {
    if (g_aiur_proof_class == NULL) {
        g_aiur_proof_class = lean_register_external_class(
            &rs_aiur_proof_free,
            &noop_foreach
        );
    }
    return g_aiur_proof_class;
}

extern lean_obj_res c_rs_aiur_proof_to_bytes(b_lean_obj_arg proof) {
    bytes_data *proof_bytes = rs_aiur_proof_to_bytes(lean_get_external_data(proof));
    size_t proof_size = proof_bytes->size;
    lean_object *byte_array = lean_alloc_sarray(1, proof_size, proof_size);
    rs_move_bytes(proof_bytes, byte_array);
    return byte_array;
}

extern lean_obj_res c_rs_aiur_proof_of_bytes(b_lean_obj_arg bytes) {
    void *proof = rs_aiur_proof_of_bytes(bytes);
    return lean_alloc_external(get_aiur_proof_class(), proof);
}

static lean_external_class *g_aiur_system_class = NULL;

static lean_external_class *get_aiur_system_class() {
    if (g_aiur_system_class == NULL) {
        g_aiur_system_class = lean_register_external_class(
            &rs_aiur_system_free,
            &noop_foreach
        );
    }
    return g_aiur_system_class;
}

extern lean_obj_res c_rs_aiur_system_build(b_lean_obj_arg toplevel) {
    void *aiur_system = rs_aiur_system_build(toplevel);
    return lean_alloc_external(get_aiur_system_class(), aiur_system);
}

extern lean_obj_res c_rs_aiur_system_prove(
    b_lean_obj_arg aiur_system,
    b_lean_obj_arg fri_parameters,
    b_lean_obj_arg fun_idx,
    b_lean_obj_arg args,
    b_lean_obj_arg input_io_data,
    b_lean_obj_arg input_io_map
) {
    assert(lean_is_scalar(fun_idx));
    prove_data *pd = rs_aiur_system_prove(
        lean_get_external_data(aiur_system),
        fri_parameters,
        fun_idx,
        args,
        input_io_data,
        input_io_map
    );

    // Build the claim object
    size_t claim_size = pd->claim_size;
    lean_object *claim = lean_alloc_array(claim_size, claim_size);
    lean_object **claim_values = lean_array_cptr(claim);
    for (size_t i = 0; i < claim_size; i++) {
        claim_values[i] = lean_box_uint64(0);
    }
    rs_set_array_g_values(claim, pd->claim);
    rs_aiur_claim_free(pd->claim);

    // Build the io_data
    size_t io_data_size = pd->io_data_size;
    lean_object *io_data = lean_alloc_array(io_data_size, io_data_size);
    lean_object **io_data_values = lean_array_cptr(io_data);
    for (size_t i = 0; i < io_data_size; i++) {
        io_data_values[i] = lean_box_uint64(0);
    }
    rs_set_aiur_io_data_values(io_data, pd->io_buffer);

    // Build io_map
    size_t io_map_size = pd->io_map_size;
    lean_object *io_map = lean_alloc_array(io_map_size, io_map_size);
    lean_object **io_map_values = lean_array_cptr(io_map);
    for (size_t i = 0; i < io_map_size; i++) {
        // Array G
        size_t key_size = pd->io_keys_sizes[i];
        lean_object *key = lean_alloc_array(key_size, key_size);
        lean_object **key_values = lean_array_cptr(key);
        for (size_t j = 0; j < key_size; j++) {
            key_values[j] = lean_box_uint64(0);
        }

        // IOKeyInfo
        lean_object *key_info = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(key_info, 0, lean_box(0));
        lean_ctor_set(key_info, 1, lean_box(0));

        // Array G × IOKeyInfo
        lean_object *map_elt = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(map_elt, 0, key);
        lean_ctor_set(map_elt, 1, key_info);
        io_map_values[i] = map_elt;
    }
    rs_set_aiur_io_map_values(io_map, pd->io_buffer);

    // Free data regarding the io buffer
    rs_aiur_prove_data_io_buffer_free(pd);

    // Array G × Array (Array G × IOKeyInfo)
    lean_object *io_tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(io_tuple, 0, io_data);
    lean_ctor_set(io_tuple, 1, io_map);

    // Proof × Array G × Array (Array G × IOKeyInfo)
    lean_object *proof_io_tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(proof_io_tuple, 0, lean_alloc_external(get_aiur_proof_class(), pd->proof));
    lean_ctor_set(proof_io_tuple, 1, io_tuple);

    // Array G × Proof × Array G × Array (Array G × IOKeyInfo)
    lean_object *claim_proof_io_tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(claim_proof_io_tuple, 0, claim);
    lean_ctor_set(claim_proof_io_tuple, 1, proof_io_tuple);

    // Free the outer ProveData struct (note: the proof object still lives!)
    rs_aiur_prove_data_free(pd);

    return claim_proof_io_tuple;
}

extern lean_obj_res c_rs_aiur_system_verify(
    b_lean_obj_arg aiur_system,
    b_lean_obj_arg fri_parameters,
    b_lean_obj_arg claim,
    b_lean_obj_arg proof
) {
    c_result *result = rs_aiur_system_verify(
        lean_get_external_data(aiur_system),
        fri_parameters,
        claim,
        lean_get_external_data(proof)
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
