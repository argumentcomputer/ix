#include "lean/lean.h"
#include "common.h"
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

extern lean_obj_res c_rs_aiur_system_prove(
    b_lean_obj_arg aiur_system,
    b_lean_obj_arg fri_parameters,
    b_lean_obj_arg fun_idx,
    b_lean_obj_arg args
) {
    assert(lean_is_scalar(fun_idx));
    prove_data *pd = rs_aiur_system_prove(
        lean_get_external_data(aiur_system),
        fri_parameters,
        fun_idx,
        args
    );

    // Build the claim object
    lean_object *claim_args = lean_alloc_array(pd->claim_num_args, pd->claim_num_args);
    rs_set_aiur_claim_args(claim_args, pd->claim_ptr);
    lean_object *claim = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(claim, 0, fun_idx);
    lean_ctor_set(claim, 1, claim_args);

    // Build the tuple for return
    lean_object *tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, claim);
    lean_ctor_set(tuple, 1, lean_alloc_external(get_aiur_proof_class(), pd->proof_ptr));

    // Free the Rust `Claim` and `ProveData` objects
    rs_aiur_claim_free(pd->claim_ptr);
    rs_aiur_prove_data_free(pd);

    return tuple;
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
