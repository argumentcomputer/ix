/* K1 gcd: C twin of K1.gcd, Euclid's algorithm (operands below 2^64). */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t gcd(uint64_t a, uint64_t b) {
  while (b != 0) {
    uint64_t r = a % b;
    a = b;
    b = r;
  }
  return a;
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: gcd A B\n"); return 1; }
  printf("%" PRIu64 "\n", gcd(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10)));
  return 0;
}
