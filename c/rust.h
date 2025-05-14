#pragma once

#include "lean/lean.h"

typedef struct {
    bool is_ok;
    void *data;
} c_result;

/* --- WitnessModule --- */

void rs_witness_module_free(void*);
size_t rs_witness_module_add_entry(void*);
size_t rs_witness_module_add_entry_with_capacity(void*, uint8_t);
void rs_witness_module_bind_oracle_to(void*, size_t, size_t, uint8_t);
void rs_witness_module_push_u128_to(void*, void*, size_t);
void rs_witness_module_populate(void*, uint64_t);
void *rs_compile_witness_modules(void**, b_lean_obj_arg);

void rs_witness_free(void*);

/* --- CircuitModule --- */

void *rs_circuit_module_new(size_t);
void rs_circuit_module_free(void*);
void rs_circuit_module_freeze_oracles(void*);
void *rs_circuit_module_init_witness_module(void*);
void rs_circuit_module_flush(void*, bool, size_t, b_lean_obj_arg, uint64_t);
void rs_circuit_module_assert_zero(
    void*, char const*, b_lean_obj_arg, b_lean_obj_arg
);
void rs_circuit_module_assert_not_zero(void*, size_t);
size_t rs_circuit_module_add_committed(void*, char const *, uint8_t);
size_t rs_circuit_module_add_transparent(void*, char const *, b_lean_obj_arg);
size_t rs_circuit_module_add_linear_combination(
    void*, char const *, b_lean_obj_arg, b_lean_obj_arg
);
size_t rs_circuit_module_add_packed(void*, char const *, size_t, size_t);
size_t rs_circuit_module_add_shifted(
    void*, char const *, size_t, uint32_t, size_t, uint8_t
);
size_t rs_circuit_module_add_projected(void*, char const *, size_t, uint64_t, size_t, size_t);
void rs_circuit_module_push_namespace(void*, char const *);
void rs_circuit_module_pop_namespace(void*);
void rs_circuit_module_version(size_t, void**, uint8_t*);

/* --- Archon protocol --- */

c_result *rs_validate_witness(size_t, void**, b_lean_obj_arg, void*);
void rs_proof_free(void*);
void *rs_prove(size_t, void**, b_lean_obj_arg, size_t, size_t, void*);
c_result *rs_verify(size_t, void**, b_lean_obj_arg, size_t, size_t, void*);
size_t rs_proof_size(void*);
void rs_proof_to_bytes(void*, size_t, uint8_t*);
void *rs_proof_of_bytes(b_lean_obj_arg);

/* --- Iroh --- */

c_result *rs_iroh_send(b_lean_obj_arg);
c_result *rs_iroh_recv(char const *, b_lean_obj_arg, size_t);

void rs__c_result_unit_string_free(c_result *);

/* --- Keccak Hasher --- */

void *rs_keccak256_hasher_init(void);
void rs_keccak256_hasher_free(void*);
void *rs_keccak256_hasher_update(void*, void*);
void *rs_keccak256_hasher_finalize(void*, void*);
