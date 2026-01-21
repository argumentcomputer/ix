#include "lean/lean.h"
#include <gmp.h>

// Lean's internal mpz allocation - takes ownership of the mpz_t value
// (declared in Lean's runtime but not exposed in public headers)
extern lean_object * lean_alloc_mpz(mpz_t v);
#include "common.h"
#include "rust.h"

// External class for RustCompiledEnv
static lean_external_class *g_rust_compiled_env_class = NULL;

static lean_external_class *get_rust_compiled_env_class() {
    if (g_rust_compiled_env_class == NULL) {
        g_rust_compiled_env_class = lean_register_external_class(
            &rs_free_rust_env,
            &noop_foreach
        );
    }
    return g_rust_compiled_env_class;
}

// FFI wrapper: Test round-trip (just pass through, returns scalar)
extern uint64_t c_rs_test_ffi_roundtrip(b_lean_obj_arg name) {
    return rs_test_ffi_roundtrip(name);
}

// FFI wrapper: Compile environment with Rust
// Returns: IO RustCompiledEnv (external object)
extern lean_obj_res c_rs_compile_env_rust_first(b_lean_obj_arg env_consts, lean_obj_arg world) {
    void *rust_env = rs_compile_env_rust_first(env_consts);
    if (rust_env == NULL) {
        // Return IO error
        lean_object *err = lean_mk_string("Rust compilation failed");
        lean_object *io_err = lean_io_result_mk_error(lean_mk_io_user_error(err));
        return io_err;
    }
    lean_object *external = lean_alloc_external(get_rust_compiled_env_class(), rust_env);
    return lean_io_result_mk_ok(external);
}

// FFI wrapper: Free RustCompiledEnv
// Returns: IO Unit
extern lean_obj_res c_rs_free_rust_env(lean_obj_arg rust_env_obj, lean_obj_arg world) {
    // The external object will be freed by Lean's GC when it's no longer referenced
    // We don't need to do anything here since we registered a finalizer
    lean_dec(rust_env_obj);
    return lean_io_result_mk_ok(lean_box(0));
}

// FFI wrapper: Get block count
extern uint64_t c_rs_get_rust_env_block_count(b_lean_obj_arg rust_env_obj) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    return rs_get_rust_env_block_count(rust_env);
}

// FFI wrapper: Compare a single block
extern uint64_t c_rs_compare_block(
    b_lean_obj_arg rust_env_obj,
    b_lean_obj_arg name,
    b_lean_obj_arg lean_bytes
) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    return rs_compare_block(rust_env, name, lean_bytes);
}

// FFI wrapper: Get Rust block bytes as ByteArray
// Returns: IO ByteArray
extern lean_obj_res c_rs_get_block_bytes(
    b_lean_obj_arg rust_env_obj,
    b_lean_obj_arg name,
    lean_obj_arg world
) {
    void *rust_env = lean_get_external_data(rust_env_obj);

    // Get the length first
    uint64_t len = rs_get_block_bytes_len(rust_env, name);

    // Allocate ByteArray
    lean_object *byte_array = lean_alloc_sarray(1, len, len);

    // Copy bytes into it
    if (len > 0) {
        rs_copy_block_bytes(rust_env, name, byte_array);
    }

    return lean_io_result_mk_ok(byte_array);
}

// FFI wrapper: Get Rust sharing vector length
extern uint64_t c_rs_get_block_sharing_len(
    b_lean_obj_arg rust_env_obj,
    b_lean_obj_arg name
) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    return rs_get_block_sharing_len(rust_env, name);
}

// FFI wrapper: Get pre-sharing expressions buffer length
extern uint64_t c_rs_get_pre_sharing_exprs_len(
    b_lean_obj_arg rust_env_obj,
    b_lean_obj_arg name
) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    return rs_get_pre_sharing_exprs_len(rust_env, name);
}

// FFI wrapper: Get pre-sharing expressions
// Returns: IO UInt64 (number of expressions)
extern lean_obj_res c_rs_get_pre_sharing_exprs(
    b_lean_obj_arg rust_env_obj,
    b_lean_obj_arg name,
    lean_obj_arg out_buf,
    lean_obj_arg world
) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    uint64_t n_exprs = rs_get_pre_sharing_exprs(rust_env, name, out_buf);
    return lean_io_result_mk_ok(lean_box_uint64(n_exprs));
}

// FFI wrapper: Look up a constant's compiled address
// Returns: IO Bool (true if found)
extern lean_obj_res c_rs_lookup_const_addr(
    b_lean_obj_arg rust_env_obj,
    b_lean_obj_arg name,
    lean_obj_arg out_addr,
    lean_obj_arg world
) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    uint64_t found = rs_lookup_const_addr(rust_env, name, out_addr);
    return lean_io_result_mk_ok(lean_box(found != 0));
}

// FFI wrapper: Get compiled constant count
extern uint64_t c_rs_get_compiled_const_count(b_lean_obj_arg rust_env_obj) {
    void *rust_env = lean_get_external_data(rust_env_obj);
    return rs_get_compiled_const_count(rust_env);
}

// =============================================================================
// Lean C API wrappers for Rust to call
// These wrap Lean's allocation functions so they can be linked from Rust
// =============================================================================

lean_object *c_lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz) {
    return lean_alloc_ctor(tag, num_objs, scalar_sz);
}

void c_lean_ctor_set(lean_object *o, unsigned i, lean_object *v) {
    lean_ctor_set(o, i, v);
}

lean_object *c_lean_ctor_get(lean_object *o, unsigned i) {
    return lean_ctor_get(o, i);
}

unsigned c_lean_obj_tag(lean_object *o) {
    return lean_obj_tag(o);
}

void c_lean_ctor_set_uint8(lean_object *o, unsigned offset, uint8_t v) {
    lean_ctor_set_uint8(o, offset, v);
}

void c_lean_ctor_set_uint64(lean_object *o, unsigned offset, uint64_t v) {
    lean_ctor_set_uint64(o, offset, v);
}

lean_object *c_lean_mk_string(char const *s) {
    return lean_mk_string(s);
}

lean_object *c_lean_alloc_sarray(unsigned elem_size, size_t size, size_t capacity) {
    return lean_alloc_sarray(elem_size, size, capacity);
}

uint8_t *c_lean_sarray_cptr(lean_object *o) {
    return lean_sarray_cptr(o);
}

lean_object *c_lean_alloc_array(size_t size, size_t capacity) {
    return lean_alloc_array(size, capacity);
}

void c_lean_array_set_core(lean_object *o, size_t i, lean_object *v) {
    lean_array_set_core(o, i, v);
}

lean_object *c_lean_array_get_core(lean_object *o, size_t i) {
    return lean_array_get_core(o, i);
}

void c_lean_inc(lean_object *o) {
    lean_inc(o);
}

void c_lean_inc_n(lean_object *o, size_t n) {
    lean_inc_n(o, n);
}

lean_object *c_lean_io_result_mk_ok(lean_object *v) {
    return lean_io_result_mk_ok(v);
}

lean_object *c_lean_uint64_to_nat(uint64_t n) {
    return lean_uint64_to_nat(n);
}

lean_object *c_lean_cstr_to_nat(char const *s) {
    return lean_cstr_to_nat(s);
}

// Create a big Nat from limbs (little-endian u64 array)
// This uses GMP's mpz_import and Lean's lean_alloc_mpz
lean_object *c_lean_nat_from_limbs(size_t num_limbs, uint64_t const *limbs) {
    if (num_limbs == 0) {
        return lean_box(0);
    }
    if (num_limbs == 1 && limbs[0] <= LEAN_MAX_SMALL_NAT) {
        return lean_box(limbs[0]);
    }
    if (num_limbs == 1) {
        return lean_uint64_to_nat(limbs[0]);
    }

    // For multi-limb values, use GMP
    mpz_t value;
    mpz_init(value);
    // Import limbs: little-endian order, native endian within limbs
    // order = -1 (least significant limb first)
    // size = 8 bytes per limb
    // endian = 0 (native)
    // nails = 0 (full limbs)
    mpz_import(value, num_limbs, -1, sizeof(uint64_t), 0, 0, limbs);

    lean_object *result = lean_alloc_mpz(value);
    // lean_alloc_mpz takes ownership, so we don't clear
    return result;
}
