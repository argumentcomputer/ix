#include "lean/lean.h"
#include "common.h"
#include "rust.h"

#define memcpy __builtin_memcpy // Avoids including `string.h`

static inline lean_obj_res mk_byte_array(size_t size, uint8_t *bytes) {
    lean_object *o = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(o), bytes, size);
    return o;
}

extern lean_obj_res c_u16_to_le_bytes(uint16_t u16) {
    return mk_byte_array(sizeof(uint16_t), (uint8_t*)&u16);
}

extern lean_obj_res c_u32_to_le_bytes(uint32_t u32) {
    return mk_byte_array(sizeof(uint32_t), (uint8_t*)&u32);
}

extern lean_obj_res c_u64_to_le_bytes(uint64_t u64) {
    return mk_byte_array(sizeof(uint64_t), (uint8_t*)&u64);
}

extern lean_obj_res c_usize_to_le_bytes(size_t usize) {
    return mk_byte_array(sizeof(size_t), (uint8_t*)&usize);
}

/* --- UInt128 --- */

static lean_external_class *g_u128_class = NULL;

static lean_external_class *get_u128_class() {
    if (g_u128_class == NULL) {
        g_u128_class = lean_register_external_class(
            &free,
            &noop_foreach
        );
    }
    return g_u128_class;
}

extern lean_obj_res c_u128_of_lo_hi(uint64_t lo, uint64_t hi) {
    uint8_t *bytes = (uint8_t*)malloc(2 * sizeof(uint64_t));
    memcpy(bytes, (uint8_t*)&lo, sizeof(uint64_t));
    memcpy(bytes + sizeof(uint64_t), (uint8_t*)&hi, sizeof(uint64_t));
    return lean_alloc_external(get_u128_class(), bytes);
}

extern lean_obj_res c_u128_to_lo_hi(b_lean_obj_arg u128) {
    uint8_t *bytes = lean_get_external_data(u128);
    uint64_t lo, hi;
    memcpy(&lo, bytes, sizeof(uint64_t));
    memcpy(&hi, bytes + sizeof(uint64_t), sizeof(uint64_t));
    lean_obj_res tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_box_uint64(lo));
    lean_ctor_set(tuple, 1, lean_box_uint64(hi));
    return tuple;
}

extern uint8_t c_u128_cmp(b_lean_obj_arg a, b_lean_obj_arg b) {
    uint8_t *a_bytes = lean_get_external_data(a);
    uint8_t *b_bytes = lean_get_external_data(b);

    uint64_t a_hi, b_hi;
    memcpy(&a_hi, a_bytes + sizeof(uint64_t), sizeof(uint64_t));
    memcpy(&b_hi, b_bytes + sizeof(uint64_t), sizeof(uint64_t));
    if (a_hi < b_hi) {
        return 0; // lt
    } else if (a_hi > b_hi) {
        return 2; // gt
    } else {
        uint64_t a_lo, b_lo;
        memcpy(&a_lo, a_bytes, sizeof(uint64_t));
        memcpy(&b_lo, b_bytes, sizeof(uint64_t));
        if (a_lo < b_lo) {
            return 0; // lt
        } else if (a_lo > b_lo) {
            return 2; // gt
        } else {
            return 1; // eq
        }
    }
}

extern lean_obj_res c_u128_to_le_bytes(b_lean_obj_arg u128) {
    return mk_byte_array(2 * sizeof(uint64_t), lean_get_external_data(u128));
}
