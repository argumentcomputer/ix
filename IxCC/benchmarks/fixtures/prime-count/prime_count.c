/* MT.2 prime-count: C twin of Scalar.primeCount, pi(n) by trial division
 * while d * d <= n (the Lean program's fuel n never runs out). Exact for
 * n < 2^32. clang cannot fold the trial divisions. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static int is_prime(uint64_t n) {
  if (n < 2) return 0;
  for (uint64_t d = 2; d * d <= n; d++)
    if (n % d == 0) return 0;
  return 1;
}

static uint64_t prime_count(uint64_t n) {
  uint64_t c = 0;
  for (uint64_t i = 2; i <= n; i++) c += is_prime(i);
  return c;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: prime-count N\n"); return 1; }
  printf("%" PRIu64 "\n", prime_count(strtoull(argv[1], NULL, 10)));
  return 0;
}
