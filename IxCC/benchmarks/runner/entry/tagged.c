/*
 * Tagged C twins of the K1 programs ackermann and tak, and of the four
 * scalar-corpus programs (collatz, prime-count, even-odd, sfib) (untrusted measurement
 * code), for the runner's diagnostic clang-tagged row. The
 * twins of fib, sum-loop and gcd are the early backend probe's (benchmarks/meas4/twins.c);
 * these follow the same rules, so the row measures what clang makes of the
 * K1 algorithms on ixcc's value representation:
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

/* The four from the scalar corpus (benchmarks/fixtures/{collatz,prime-count,even-odd,
 * sfib}), on the same rules. A tagged sum a + b is (a - 1) + b, a tagged
 * product a * b is (a - 1) * (b >> 1) + 1, each with its carry or overflow
 * out as natOverflow; Nat division and remainder untag their operands. Loop
 * bounds compare tagged words directly (`n < limit`), where the compiled
 * code evaluates Lean's `n + 1 ≤ limit`. */

static inline uint64_t tadd(uint64_t a, uint64_t b) {
  uint64_t s;
  if (__builtin_add_overflow(a - 1, b, &s)) nat_overflow();
  return s;
}

static inline uint64_t tmul(uint64_t a, uint64_t b) {
  uint64_t p;
  if (__builtin_mul_overflow(a - 1, b >> 1, &p)) nat_overflow();
  return p + 1;
}

#define T(n) (2 * (uint64_t)(n) + 1)

/* collatzGo fuel n s, with fuel 1000 per start: the steps to reach 1. */
static uint64_t collatz_steps(uint64_t n) {
  uint64_t s = T(0);
  for (uint64_t fuel = T(1000); fuel != T(0); fuel -= 2) {
    if (n <= T(1)) return s;
    n = ((n >> 1) & 1) == 0 ? (((n >> 2) << 1) | 1) : tadd(tmul(T(3), n), T(1));
    s = succ(s);
  }
  return s;
}

/* entry limit: the total steps of 1 ... limit - 1. */
uint64_t twin_collatz(uint64_t limit) {
  uint64_t s = T(0);
  for (uint64_t n = T(1); n < limit; n = succ(n)) s = tadd(s, collatz_steps(n));
  return s;
}

/* primeGo n fuel d: trial division by d while d * d <= n (fuel n). */
static int prime_go(uint64_t n, uint64_t fuel, uint64_t d) {
  for (; fuel != T(0); fuel -= 2, d = succ(d)) {
    if (tmul(d, d) > n) return 1;
    if ((n >> 1) % (d >> 1) == 0) return 0;
  }
  return 1;
}

/* primeCount n: the primes up to n. */
uint64_t twin_prime_count(uint64_t n) {
  uint64_t c = T(0);
  for (uint64_t i = T(2); i <= n; i = succ(i))
    if (prime_go(i, i, T(2))) c = succ(c);
  return c;
}

/* isEven / isOdd: mutual recursion kept out of line (sibling tail jumps). */
__attribute__((noinline)) int twin_is_odd(uint64_t n);
__attribute__((noinline)) int twin_is_even(uint64_t n) { return n == T(0) ? 1 : twin_is_odd(n - 2); }
__attribute__((noinline)) int twin_is_odd(uint64_t n) { return n == T(0) ? 0 : twin_is_even(n - 2); }

/* sfibGo n 1: x <- x * x + x + 2, restarted at 1 above 10^9. */
uint64_t twin_sfib(uint64_t n) {
  uint64_t x = T(1);
  for (; n != T(0); n -= 2) x = x > T(1000000000) ? T(1) : tadd(tadd(tmul(x, x), x), T(2));
  return x;
}
