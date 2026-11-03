#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

extern char *aiur_execute_json(const uint8_t *data, size_t length);
extern void aiur_free_string(char *string);

/* The only code depending on Lean's C object ABI. Rust borrows the request
   for this call; the response is copied into Lean before Rust frees it. */
LEAN_EXPORT lean_obj_res aiur_lean_execute(b_lean_obj_arg request, lean_obj_arg world) {
    (void)world;
    char *response = aiur_execute_json((const uint8_t *)lean_string_cstr(request),
                                     lean_string_size(request) - 1);
    lean_object *result = lean_mk_string(response);
    aiur_free_string(response);
    return lean_io_result_mk_ok(result);
}
