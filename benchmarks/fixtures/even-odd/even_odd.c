/* MT.2 even-odd: C twin of MLton's even-odd mutual recursion (Scalar.isEven,
 * Scalar.isOdd). Both functions are kept out of line, so clang compiles the
 * sibling calls as tail jumps (one per step, as the Lean program's) instead
 * of folding the recursion to a parity test. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

__attribute__((noinline)) static int is_odd(uint64_t n);

__attribute__((noinline)) static int is_even(uint64_t n) { return n == 0 ? 1 : is_odd(n - 1); }

__attribute__((noinline)) static int is_odd(uint64_t n) { return n == 0 ? 0 : is_even(n - 1); }

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: even-odd N\n"); return 1; }
  printf("%d\n", is_even(strtoull(argv[1], NULL, 10)));
  return 0;
}
