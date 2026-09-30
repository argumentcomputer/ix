/*
 * Tagged C twins of the K1 programs ackermann and tak (untrusted
 * measurement code), for the runner's diagnostic clang-tagged row. The
 * twins of fib, sum-loop and gcd are MEAS-4's (benchmarks/meas4/twins.c);
 * these follow the same rules, so the row measures what clang makes of the
 * K1 algorithms on compilatrix's value representation:
 *
 * - a Nat n < 2^63 is the word 2n + 1 (Rt.Layout's scalar encoding);
 * - n + 1 is a tagged + 2 whose carry out is natOverflow (the compiled
 *   code's `add r, 2; jc`), leaving through a cold, noreturn path;
 * - n - 1 truncates at zero (Nat subtraction);
 * - comparisons compare tagged words, which preserves order.
 *
 * They are the fixtures' algorithms (benchmarks/fixtures/{ackermann,tak}),
 * not the compiled programs' statement for statement: tak's `y < x` is one
 * comparison, where the compiled code evaluates Lean's `y + 1 ≤ x` with a
 * carry check (a middle-end difference the report attributes separately).
 * Compiled on its own at -O2, so the timing driver cannot inline it.
 */
#include <stdint.h>
#include <stdlib.h>

__attribute__((noreturn, cold, noinline)) static void nat_overflow(void) { abort(); }

static inline uint64_t succ(uint64_t n) {
  uint64_t s;
  if (__builtin_add_overflow(n, 2, &s)) nat_overflow();
  return s;
}

/* Truncating predecessor: tag 0 stays tag 0. */
static inline uint64_t pred(uint64_t n) { return n > 1 ? n - 2 : 1; }

/* ack 0 n = n + 1; ack (m + 1) 0 = ack m 1; ack (m + 1) (n + 1) = ack m (ack (m + 1) n). */
uint64_t twin_ack(uint64_t m, uint64_t n) {
  if (m == 1) return succ(n);
  if (n == 1) return twin_ack(m - 2, 3);
  return twin_ack(m - 2, twin_ack(m, n - 2));
}

/* tak 0 x y z = z; tak (f + 1) x y z = if y < x then tak f (tak f (x - 1) y z)
 * (tak f (y - 1) z x) (tak f (z - 1) x y) else z. */
uint64_t twin_tak(uint64_t f, uint64_t x, uint64_t y, uint64_t z) {
  if (f == 1) return z;
  if (y < x)
    return twin_tak(f - 2, twin_tak(f - 2, pred(x), y, z), twin_tak(f - 2, pred(y), z, x),
                    twin_tak(f - 2, pred(z), x, y));
  return z;
}
