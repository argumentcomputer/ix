#pragma once

#include "lean/lean.h"

typedef struct {
    bool is_ok;
    void *data;
} c_result;

/* --- Witness --- */

void rs_witness_free(void*);

/* --- WitnessBuilder --- */

void *rs_witness_builder_new(void*);
void rs_witness_builder_free(void*);
void rs_witness_builder_with_column(void*, size_t, b_lean_obj_arg);
void rs_witness_builder_with_column_default(void*, size_t, b_lean_obj_arg);
void *rs_witness_builder_build(void*);

/* --- ConstraintSystem --- */

void rs_constraint_system_free(void*);
c_result *rs_constraint_system_validate_witness(void*, b_lean_obj_arg, void*);

/* --- ConstraintSystemBuilder --- */

void *rs_constraint_system_builder_new();
void *rs_constraint_system_builder_build(void*);
void rs_constraint_system_builder_free(void*);
void rs_constraint_system_builder_flush_with_multiplicity(
    void*, bool, size_t, size_t, b_lean_obj_arg, uint64_t
);
void rs_constraint_system_builder_flush_custom(
    void*, bool, size_t, size_t, b_lean_obj_arg, uint64_t
);
void rs_constraint_system_builder_assert_zero(
    void*, char const*, b_lean_obj_arg, b_lean_obj_arg
);
void rs_constraint_system_builder_assert_not_zero(void*, size_t);
size_t rs_constraint_system_builder_add_channel(void*);
size_t rs_constraint_system_builder_add_committed(
    void*, char const *, size_t, uint8_t
);
size_t rs_constraint_system_builder_add_linear_combination(
    void*, char const *, size_t, b_lean_obj_arg
);
size_t rs_constraint_system_builder_add_linear_combination_with_offset(
    void*, char const *, size_t, b_lean_obj_arg, b_lean_obj_arg
);
size_t rs_constraint_system_builder_add_packed(
    void*, char const *, size_t, size_t
);
size_t rs_constraint_system_builder_add_transparent(
    void*, char const *, b_lean_obj_arg
);
void rs_constraint_system_builder_push_namespace(void*, char const *);
void rs_constraint_system_builder_pop_namespace(void*);
size_t rs_constraint_system_builder_log_rows(void*, b_lean_obj_arg);

c_result *rs_iroh_send(b_lean_obj_arg);
c_result *rs_iroh_recv(char const *, b_lean_obj_arg, size_t);

void rs__c_result_unit_string_free(c_result *);

void rs_keccak256_hash(void*, void*);
void *rs_keccak256_hasher_init(void);
void rs_keccak256_hasher_free(void*);
void *rs_keccak256_hasher_update(void*, void*);
void *rs_keccak256_hasher_finalize(void*, void*);
