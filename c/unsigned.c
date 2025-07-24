#include "lean/lean.h"
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
