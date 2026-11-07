/*
 * The runner's adapter for the lean-clang row (untrusted measurement code).
 * The row's code is the fixture's Lean source compiled by `lean -c` and
 * `leanc -O3 -DNDEBUG` as the module BenchEntry, with one declaration
 * appended by the runner:
 *
 *     @[export bench_entry] def benchEntry (a0 ... : Nat) : Nat := entry a0 ...
 *
 * (and the fixture's `main` renamed, so the module has no C main). Lean's
 * runtime and the module are initialised once, in row_init. Each call boxes
 * the arguments as scalar Nats (below 2^63) and unboxes the result. ARITY
 * is the entry's parameter count. leanc's toolchain has no libc headers
 * beyond what lean.h needs, so errors go through Lean's panic.
 */
#include <lean/lean.h>

void lean_initialize_runtime_module(void);
extern lean_object *initialize_BenchEntry(uint8_t builtin);

#if ARITY == 1
extern lean_object *bench_entry(lean_object *);
#define CALL(a) bench_entry(lean_box(a[0]))
#elif ARITY == 2
extern lean_object *bench_entry(lean_object *, lean_object *);
#define CALL(a) bench_entry(lean_box(a[0]), lean_box(a[1]))
#elif ARITY == 3
extern lean_object *bench_entry(lean_object *, lean_object *, lean_object *);
#define CALL(a) bench_entry(lean_box(a[0]), lean_box(a[1]), lean_box(a[2]))
#elif ARITY == 4
extern lean_object *bench_entry(lean_object *, lean_object *, lean_object *, lean_object *);
#define CALL(a) bench_entry(lean_box(a[0]), lean_box(a[1]), lean_box(a[2]), lean_box(a[3]))
#elif ARITY == 5
extern lean_object *bench_entry(lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
#define CALL(a) bench_entry(lean_box(a[0]), lean_box(a[1]), lean_box(a[2]), lean_box(a[3]), lean_box(a[4]))
#else
#error "ARITY must be 1 to 5"
#endif

void row_init(void) {
  lean_initialize_runtime_module();
  lean_set_panic_messages(false);
  lean_object *result = initialize_BenchEntry(1);
  lean_set_panic_messages(true);
  lean_io_mark_end_initialization();
  if (!lean_io_result_is_ok(result)) {
    lean_io_result_show_error(result);
    lean_internal_panic("BenchEntry initialisation failed");
  }
  lean_dec_ref(result);
}

uint64_t row_entry(const uint64_t *a) {
  for (int i = 0; i < ARITY; i++)
    if (a[i] > LEAN_MAX_SMALL_NAT) lean_internal_panic("argument is not a scalar Nat");
  lean_object *r = CALL(a);
  if (!lean_is_scalar(r)) lean_internal_panic("result is not a scalar Nat");
  return (uint64_t)lean_unbox(r);
}

uint64_t row_heap(void) { return UINT64_MAX; }
