#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

extern uint8_t *aiur_execute(const uint8_t *package, size_t package_length,
                             const uint8_t *hints, size_t hints_length,
                             const uint8_t *request, size_t request_length,
                             size_t *response_length);
extern void aiur_free_bytes(uint8_t *bytes, size_t length);

/* The only code depending on Lean's C object ABI. Rust borrows the Ixon
   package and hints and the JSON request for this call; its Ixon response is
   copied into a Lean ByteArray before Rust frees it. */
LEAN_EXPORT lean_obj_res aiur_lean_execute(b_lean_obj_arg package, b_lean_obj_arg hints,
                                           b_lean_obj_arg request, lean_obj_arg world) {
    (void)world;
    size_t length = 0;
    uint8_t *response = aiur_execute(lean_sarray_cptr(package), lean_sarray_size(package),
                                     lean_sarray_cptr(hints), lean_sarray_size(hints),
                                     (const uint8_t *)lean_string_cstr(request),
                                     lean_string_size(request) - 1, &length);
    lean_object *result = lean_alloc_sarray(1, length, length);
    memcpy(lean_sarray_cptr(result), response, length);
    aiur_free_bytes(response, length);
    return lean_io_result_mk_ok(result);
}
