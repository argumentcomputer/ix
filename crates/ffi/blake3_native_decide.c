/*
 * Lean's native evaluator calls the boxed symbols generated for opaque
 * extern declarations, while the pinned Blake3 Rust cdylib exports the raw
 * rs_blake3_* ABI.  Normal executables get these tiny adapters from the
 * generated Blake3.Rust object.  Verification modules are elaborated before
 * executable linking, so Lake loads this equivalent shim for native_decide.
 */

#include <lean/lean.h>
#include <stdint.h>

extern lean_object *rs_blake3_init(lean_object *);
extern lean_object *rs_blake3_init_keyed(lean_object *);
extern lean_object *rs_blake3_init_derive_key(lean_object *);
extern lean_object *rs_blake3_hasher_update(lean_object *, lean_object *);
extern lean_object *rs_blake3_hasher_finalize(lean_object *, size_t);

LEAN_EXPORT lean_object *
lp_Blake3_Blake3_Rust_hasherInit___boxed(lean_object *unit) {
  return rs_blake3_init(unit);
}

LEAN_EXPORT lean_object *
lp_Blake3_Blake3_Rust_hasherInitKeyed___boxed(lean_object *key) {
  lean_object *result = rs_blake3_init_keyed(key);
  lean_dec_ref(key);
  return result;
}

LEAN_EXPORT lean_object *
lp_Blake3_Blake3_Rust_hasherInitDeriveKey___boxed(lean_object *context) {
  lean_object *result = rs_blake3_init_derive_key(context);
  lean_dec_ref(context);
  return result;
}

LEAN_EXPORT lean_object *
lp_Blake3_Blake3_Rust_hasherUpdate___boxed(lean_object *hasher,
                                           lean_object *bytes) {
  lean_object *result = rs_blake3_hasher_update(hasher, bytes);
  lean_dec_ref(bytes);
  return result;
}

LEAN_EXPORT lean_object *
lp_Blake3_Blake3_Rust_hasherFinalize___boxed(lean_object *hasher,
                                             lean_object *length) {
  size_t unboxed_length = lean_unbox_usize(length);
  lean_dec(length);
  return rs_blake3_hasher_finalize(hasher, unboxed_length);
}

/*
 * Ix.Unsigned normally receives these symbols from ix-ffi when a final Lean
 * executable is linked.  Library elaboration has no such executable, so
 * native_decide needs an equivalent implementation in this loaded adapter.
 * Keep the byte order explicit so this remains host-endianness independent.
 */
static lean_object *ix_alloc_le_bytes(uint64_t value, size_t width) {
  lean_object *bytes = lean_alloc_sarray(1, width, width);
  uint8_t *data = lean_sarray_cptr(bytes);
  for (size_t index = 0; index < width; ++index) {
    data[index] = (uint8_t)(value >> (8 * index));
  }
  return bytes;
}

LEAN_EXPORT lean_object *c_u16_to_le_bytes(uint16_t value) {
  return ix_alloc_le_bytes((uint64_t)value, sizeof(uint16_t));
}

LEAN_EXPORT lean_object *c_u32_to_le_bytes(uint32_t value) {
  return ix_alloc_le_bytes((uint64_t)value, sizeof(uint32_t));
}

LEAN_EXPORT lean_object *c_u64_to_le_bytes(uint64_t value) {
  return ix_alloc_le_bytes(value, sizeof(uint64_t));
}

LEAN_EXPORT lean_object *c_usize_to_le_bytes(size_t value) {
  return ix_alloc_le_bytes((uint64_t)value, sizeof(size_t));
}

LEAN_EXPORT lean_object *
lp_ix_UInt16_toLEBytes___boxed(lean_object *value) {
  return c_u16_to_le_bytes((uint16_t)lean_unbox(value));
}

LEAN_EXPORT lean_object *
lp_ix_UInt32_toLEBytes___boxed(lean_object *value) {
  uint32_t unboxed = lean_unbox_uint32(value);
  lean_dec(value);
  return c_u32_to_le_bytes(unboxed);
}

LEAN_EXPORT lean_object *
lp_ix_UInt64_toLEBytes___boxed(lean_object *value) {
  uint64_t unboxed = lean_unbox_uint64(value);
  lean_dec_ref(value);
  return c_u64_to_le_bytes(unboxed);
}

LEAN_EXPORT lean_object *
lp_ix_USize_toLEBytes___boxed(lean_object *value) {
  size_t unboxed = lean_unbox_usize(value);
  lean_dec(value);
  return c_usize_to_le_bytes(unboxed);
}
