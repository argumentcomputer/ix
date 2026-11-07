#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

extern char *aiur_execute(const uint8_t *package, size_t package_length,
                          const uint8_t *hints, size_t hints_length,
                          const uint8_t *request, size_t request_length);
extern void aiur_free_string(char *string);

/* The only code depending on Lean's C object ABI. Rust borrows the Ixon
   package and hints and the JSON request for this call; the response is
   copied into Lean before Rust frees it. */
LEAN_EXPORT lean_obj_res aiur_lean_execute(b_lean_obj_arg package, b_lean_obj_arg hints,
                                           b_lean_obj_arg request, lean_obj_arg world) {
    (void)world;
    char *response = aiur_execute(lean_sarray_cptr(package), lean_sarray_size(package),
                                  lean_sarray_cptr(hints), lean_sarray_size(hints),
                                  (const uint8_t *)lean_string_cstr(request),
                                  lean_string_size(request) - 1);
    lean_object *result = lean_mk_string(response);
    aiur_free_string(response);
    return lean_io_result_mk_ok(result);
}
