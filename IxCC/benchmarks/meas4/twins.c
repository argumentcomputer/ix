/*
 * The early backend probe's C twins of the synthetic Lir kernels. Untrusted
 * measurement code, compiled on its own at -O2 so that the timing driver cannot inline or hoist it.
 *
 * Tagged twins (twin_*) use the object layout of the Lir kernels in
 * IxCCTests/Lir/Kernels.lean: a Nat n < 2^63 is the word 2n + 1,
 * and every Nat addition checks the carry of `(a - 1) + b`
 * (natOverflow), leaving through a cold, noreturn failure path. They are
 * the kernels' algorithms statement for statement, so they measure code
 * generation, not representation or algorithm.
 *
 * Natural twins (natural_*) are the benchmark fixtures' algorithms
 * (benchmarks/fixtures/{fib,sum-loop,gcd}) on plain uint64_t, for
 * reference. natural_sum_loop is folded to a closed form by clang at -O2
 * (benchmarks/fixtures/README.md); its row measures no loop.
 */
#include <stdint.h>
#include <stdlib.h>

__attribute__((noreturn, cold, noinline)) static void nat_overflow(void) { abort(); }

/* fib: n <= 1 iff 2n + 1 <= 3; fib (n - 2) + fib (n - 1) as
 * `lea t, [a - 1]; add t, b; jc`. */
uint64_t twin_fib(uint64_t n) {
  if (n <= 3) return n;
  uint64_t a = twin_fib(n - 4);
  uint64_t b = twin_fib(n - 2);
  uint64_t s;
  if (__builtin_add_overflow(a - 1, b, &s)) nat_overflow();
  return s;
}

/* sum-loop: i and s tagged, from tag 0; while i < n, s := s + i with the
 * carry check, i := i + 1 (a tagged + 2, which cannot overflow as i < n).
 * The overflow exit depends on s, so clang cannot replace the loop by a
 * closed form. */
uint64_t twin_sum_loop(uint64_t n) {
  uint64_t i = 1, s = 1;
  while (i < n) {
    if (__builtin_add_overflow(s - 1, i, &s)) nat_overflow();
    i += 2;
  }
  return s;
}

/* gcd: y = 0 iff y = tag 0; untag, x % y, retag. */
uint64_t twin_gcd(uint64_t x, uint64_t y) {
  while (y != 1) {
    uint64_t r = (((x >> 1) % (y >> 1)) << 1) | 1;
    x = y;
    y = r;
  }
  return x;
}

/* The fixtures' algorithms (fib.c, sum_loop.c, gcd.c), untagged. */
uint64_t natural_fib(uint64_t n) {
  if (n == 0) return 0;
  if (n == 1) return 1;
  return natural_fib(n - 2) + natural_fib(n - 1);
}

uint64_t natural_sum_loop(uint64_t n) {
  uint64_t s = 0;
  for (uint64_t i = 0; i < n; i++) s += i;
  return s;
}

uint64_t natural_gcd(uint64_t a, uint64_t b) {
  while (b != 0) {
    uint64_t r = a % b;
    a = b;
    b = r;
  }
  return a;
}
