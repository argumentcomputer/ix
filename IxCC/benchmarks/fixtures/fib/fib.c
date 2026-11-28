/* K1 fib: C twin of K1.fib (Nat is unsigned 64-bit; exact for n <= 93). */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t fib(uint64_t n) {
  if (n == 0) return 0;
  if (n == 1) return 1;
  return fib(n - 2) + fib(n - 1);
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: fib N\n"); return 1; }
  printf("%" PRIu64 "\n", fib(strtoull(argv[1], NULL, 10)));
  return 0;
}
