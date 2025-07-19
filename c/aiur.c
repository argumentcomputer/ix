#include "lean/lean.h"
#include "common.h"
#include "rust.h"

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
    size_t claim_size = pd->claim_size;
    lean_object *claim = lean_alloc_array(claim_size, claim_size);
    lean_object **claim_data = lean_array_cptr(claim);
    for (size_t i = 0; i < claim_size; i++) {
        claim_data[i] = lean_box_uint64(0);
    }
    rs_set_aiur_claim_args(claim, pd->claim);
    rs_aiur_claim_free(pd->claim);

    // Build the tuple for return
    lean_object *tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, claim);
    lean_ctor_set(tuple, 1, lean_alloc_external(get_aiur_proof_class(), pd->proof));

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
