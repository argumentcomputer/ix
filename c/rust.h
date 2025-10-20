#pragma once

#include "lean/lean.h"

typedef struct {
    bool is_ok;
    void *data;
} c_result;

/* --- Aiur -- */

typedef struct {
    size_t size;
    void *bytes_vec;
} bytes_data;

void rs_move_bytes(bytes_data*, lean_obj_arg);

bytes_data *rs_aiur_proof_to_bytes(void*);
void *rs_aiur_proof_of_bytes(b_lean_obj_arg);

void rs_aiur_system_free(void*);
void *rs_aiur_system_build(b_lean_obj_arg);

typedef struct {
    size_t claim_size;
    void *claim;
    void *proof;
    void *io_buffer;
    size_t io_data_size;
    size_t io_map_size;
    size_t *io_keys_sizes;
} prove_data;

void rs_aiur_claim_free(void*);
void rs_aiur_proof_free(void*);
void rs_aiur_prove_data_io_buffer_free(void*);
void rs_aiur_prove_data_free(prove_data*);

prove_data *rs_aiur_system_prove(
    void*, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg, b_lean_obj_arg
);
void rs_set_array_g_values(lean_obj_arg, void*);
void rs_set_aiur_io_data_values(lean_obj_arg, void*);
void rs_set_aiur_io_map_values(lean_obj_arg, void*);

c_result *rs_aiur_system_verify(void*, b_lean_obj_arg, b_lean_obj_arg, void*);

/* --- Iroh --- */

c_result *rs_iroh_put(char const *, b_lean_obj_arg, char const *, char const *);
c_result *rs_iroh_get(char const *, b_lean_obj_arg, char const *, char const *);


void rs__c_result_unit_string_free(c_result *);

/* --- Keccak Hasher --- */

void *rs_keccak256_hasher_init(void);
void rs_keccak256_hasher_free(void*);
void *rs_keccak256_hasher_update(void*, void*);
void *rs_keccak256_hasher_finalize(void*, void*);
