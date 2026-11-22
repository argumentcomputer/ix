/* K1 ackermann: C twin of K1.ack, the same recursion scheme. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t ack(uint64_t m, uint64_t n) {
  if (m == 0) return n + 1;
  if (n == 0) return ack(m - 1, 1);
  return ack(m - 1, ack(m, n - 1));
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: ackermann M N\n"); return 1; }
  printf("%" PRIu64 "\n", ack(strtoull(argv[1], NULL, 10), strtoull(argv[2], NULL, 10)));
  return 0;
}
