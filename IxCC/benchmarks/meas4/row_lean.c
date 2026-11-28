/*
 * The early backend probe's adapter for the lean-clang row (untrusted measurement code): the
 * K1 definitions compiled by `lean -c` and `leanc -O3 -DNDEBUG` (K1Probe.lean),
 * called through their exported entries on boxed scalar Nats. Lean's runtime
 * and the module are initialised once, before timing. leanc's toolchain has
 * no libc headers beyond what lean.h needs, so errors go through Lean's panic.
 */
#include <lean/lean.h>

void lean_initialize_runtime_module(void);
extern lean_object *initialize_K1Probe(uint8_t builtin);
extern lean_object *meas4_fib(lean_object *n);
extern lean_object *meas4_sum_loop(lean_object *n);
extern lean_object *meas4_gcd(lean_object *a, lean_object *b);

void row_init(void) {
  lean_initialize_runtime_module();
  lean_set_panic_messages(false);
  lean_object *result = initialize_K1Probe(1);
  lean_set_panic_messages(true);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(result)) {
    lean_io_result_show_error(result);
    lean_internal_panic("K1Probe initialisation failed");
  }
  lean_dec_ref(result);
}

static uint64_t unbox(lean_object *r) {
  if (!lean_is_scalar(r)) lean_internal_panic("result is not a scalar Nat");
  return (uint64_t)lean_unbox(r);
}

uint64_t row_fib(uint64_t n) { return unbox(meas4_fib(lean_box(n))); }
uint64_t row_sum_loop(uint64_t n) { return unbox(meas4_sum_loop(lean_box(n))); }
uint64_t row_gcd(uint64_t a, uint64_t b) { return unbox(meas4_gcd(lean_box(a), lean_box(b))); }
