/* K1 sum-loop: C twin of K1.sumLoop, the sum of 0 .. n-1 (exact below 2^64). */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t sum_loop(uint64_t n) {
  uint64_t s = 0;
  for (uint64_t i = 0; i < n; i++) s += i;
  return s;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: sum-loop N\n"); return 1; }
  printf("%" PRIu64 "\n", sum_loop(strtoull(argv[1], NULL, 10)));
  return 0;
}
