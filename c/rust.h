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

void rs__c_result_unit_string_free(c_result *);

/* --- Iroh --- */

c_result *rs_iroh_serve(void);
c_result *rs_iroh_put(char const *, b_lean_obj_arg, char const *, char const *);
c_result *rs_iroh_get(char const *, b_lean_obj_arg, char const *, char const *);

void rs__c_result_iroh_put_response_string_free(c_result *);
void rs__c_result_iroh_get_response_string_free(c_result *);

/* --- Keccak Hasher --- */

void *rs_keccak256_hasher_init(void);
void rs_keccak256_hasher_free(void*);
void *rs_keccak256_hasher_update(void*, void*);
void *rs_keccak256_hasher_finalize(void*, void*);

/* --- Ixon FFI (incremental block comparison) --- */

// Test FFI round-trip
uint64_t rs_test_ffi_roundtrip(b_lean_obj_arg name);

// Compile environment with Rust, returns opaque RustCompiledEnv*
void *rs_compile_env_rust_first(b_lean_obj_arg env_consts);

// Free a RustCompiledEnv
void rs_free_rust_env(void *rust_env);

// Get block count from RustCompiledEnv
uint64_t rs_get_rust_env_block_count(void const *rust_env);

// Compare a single block, returns packed result
uint64_t rs_compare_block(void const *rust_env, b_lean_obj_arg name, b_lean_obj_arg lean_bytes);

// Get the length of Rust's compiled bytes for a block
uint64_t rs_get_block_bytes_len(void const *rust_env, b_lean_obj_arg name);

// Copy Rust's compiled bytes into a pre-allocated ByteArray
void rs_copy_block_bytes(void const *rust_env, b_lean_obj_arg name, lean_obj_arg dest);

// Get Rust's sharing vector length for a block
uint64_t rs_get_block_sharing_len(void const *rust_env, b_lean_obj_arg name);

// Compare block with typed result (returns BlockCompareDetail)
lean_obj_res rs_compare_block_v2(void const *rust_env, b_lean_obj_arg name, b_lean_obj_arg lean_bytes, uint64_t lean_sharing_len);

// Get the buffer length needed for pre-sharing expressions
uint64_t rs_get_pre_sharing_exprs_len(void const *rust_env, b_lean_obj_arg name);

// Get pre-sharing root expressions for a constant
uint64_t rs_get_pre_sharing_exprs(void const *rust_env, b_lean_obj_arg name, lean_obj_arg out_buf);

// Look up a constant's compiled address (32-byte blake3 hash)
// Returns 1 on success, 0 if name not found
uint64_t rs_lookup_const_addr(void const *rust_env, b_lean_obj_arg name, lean_obj_arg out_addr);

// Get the total number of compiled constants
uint64_t rs_get_compiled_const_count(void const *rust_env);

/* --- Utility FFI --- */

// Read first 8 bytes of ByteArray as little-endian UInt64 (for Address.Hashable)
uint64_t rs_bytearray_to_u64_le(b_lean_obj_arg ba);

/* --- Ix Canonicalization FFI --- */

// Canonicalize environment and return Ix.Environment
// Takes: List (Lean.Name × Lean.ConstantInfo)
// Returns: IO Ix.Environment
lean_obj_res rs_canonicalize_env_to_ix(b_lean_obj_arg env_consts);

/* --- Round-trip FFI for testing Lean object construction --- */

// Round-trip basic types: Lean -> Rust -> Lean
lean_object *rs_roundtrip_nat(b_lean_obj_arg nat);
lean_object *rs_roundtrip_string(b_lean_obj_arg str);
lean_object *rs_roundtrip_list_nat(b_lean_obj_arg list);
lean_object *rs_roundtrip_array_nat(b_lean_obj_arg arr);
lean_object *rs_roundtrip_bytearray(b_lean_obj_arg ba);

// Round-trip Ix types: Lean -> Rust -> Lean
lean_object *rs_roundtrip_ix_address(b_lean_obj_arg addr);
lean_object *rs_roundtrip_ix_name(b_lean_obj_arg name);
lean_object *rs_roundtrip_ix_level(b_lean_obj_arg level);
lean_object *rs_roundtrip_ix_expr(b_lean_obj_arg expr);
lean_object *rs_roundtrip_ix_int(b_lean_obj_arg int_val);
lean_object *rs_roundtrip_ix_substring(b_lean_obj_arg sub);
lean_object *rs_roundtrip_ix_source_info(b_lean_obj_arg si);
lean_object *rs_roundtrip_ix_syntax_preresolved(b_lean_obj_arg sp);
lean_object *rs_roundtrip_ix_syntax(b_lean_obj_arg syn);
lean_object *rs_roundtrip_ix_data_value(b_lean_obj_arg dv);
lean_object *rs_roundtrip_bool(b_lean_obj_arg b);
lean_object *rs_roundtrip_ix_constant_info(b_lean_obj_arg info);
lean_object *rs_roundtrip_ix_environment(b_lean_obj_arg env);
lean_object *rs_roundtrip_ix_raw_environment(b_lean_obj_arg raw_env);

// Round-trip BlockCompareResult and BlockCompareDetail
lean_object *rs_roundtrip_block_compare_result(b_lean_obj_arg ptr);
lean_object *rs_roundtrip_block_compare_detail(b_lean_obj_arg ptr);

/* --- RawCompiledEnv FFI --- */

// Compile environment and return RawCompiledEnv
// Takes: List (Lean.Name × Lean.ConstantInfo)
// Returns: IO RawCompiledEnv
lean_obj_res rs_compile_env_to_raw(b_lean_obj_arg env_consts);

// Complete compilation pipeline - returns RustCompilationResult
// (rawEnv, condensed, compiled)
lean_obj_res rs_compile_env_full(b_lean_obj_arg env_consts);

// Compile environment to Ixon RawEnv (structured Lean objects)
// Takes: List (Lean.Name × Lean.ConstantInfo)
// Returns: IO RawEnv
lean_obj_res rs_compile_env_to_ixon(b_lean_obj_arg env_consts);

// Round-trip RawEnv for FFI testing
lean_object *rs_roundtrip_raw_env(b_lean_obj_arg raw_env);

// Round-trip RustCondensedBlocks for FFI testing
lean_object *rs_roundtrip_rust_condensed_blocks(b_lean_obj_arg condensed);

// Round-trip RustCompilePhases for FFI testing
lean_object *rs_roundtrip_rust_compile_phases(b_lean_obj_arg phases);

// Combined compilation phases - returns RustCompilePhases
// (rawEnv, condensed, compileEnv)
// Takes: List (Lean.Name × Lean.ConstantInfo)
// Returns: IO RustCompilePhases
lean_obj_res rs_compile_phases(b_lean_obj_arg env_consts);

/* --- Graph/SCC FFI --- */

// Build reference graph in Rust (returns Ix.Name-based graph)
// Takes: List (Lean.Name × Lean.ConstantInfo)
// Returns: IO (Array (Ix.Name × Array Ix.Name))
lean_obj_res rs_build_ref_graph(b_lean_obj_arg env_consts);

// Compute SCCs in Rust (returns Ix.Name-based CondensedBlocks)
// Takes: List (Lean.Name × Lean.ConstantInfo)
// Returns: IO RustCondensedBlocks
lean_obj_res rs_compute_sccs(b_lean_obj_arg env_consts);
