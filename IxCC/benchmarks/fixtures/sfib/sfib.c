/* MT.2 sfib: C twin of Koka's sfib-int loop (Scalar.sfib): x <- x^2 + x + 2,
 * restarted at 1 above 10^9, so every value stays below 2^63 (uint64_t is
 * exact). The recurrence is not affine, so clang cannot fold the loop. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t sfib(uint64_t n) {
  uint64_t x = 1;
  for (; n > 0; n--) x = x > 1000000000 ? 1 : x * x + x + 2;
  return x;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: sfib N\n"); return 1; }
  printf("%" PRIu64 "\n", sfib(strtoull(argv[1], NULL, 10)));
  return 0;
}
