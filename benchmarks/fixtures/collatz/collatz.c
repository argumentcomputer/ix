/* MT.2 collatz: C twin of the Lean entry, the total Collatz steps of
 * 1 ... limit - 1 with the Lean program's fuel of 1000 steps per start.
 * uint64_t is exact for limit <= 10^6 (no trajectory below 10^6 passes 2^63).
 * The trajectories are data-dependent, so clang cannot fold the loop. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t collatz(uint64_t n) {
  uint64_t s = 0;
  for (unsigned fuel = 1000; fuel > 0; fuel--) {
    if (n <= 1) return s;
    n = n % 2 == 0 ? n / 2 : 3 * n + 1;
    s++;
  }
  return s;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: collatz LIMIT\n"); return 1; }
  uint64_t limit = strtoull(argv[1], NULL, 10), s = 0;
  for (uint64_t n = 1; n < limit; n++) s += collatz(n);
  printf("%" PRIu64 "\n", s);
  return 0;
}
