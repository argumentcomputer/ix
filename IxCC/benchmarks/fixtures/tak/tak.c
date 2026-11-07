/* K1 tak: C twin of K1.tak, Takeuchi's function with explicit fuel.
   Subtraction truncates at zero, as on Lean's Nat. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t pred(uint64_t a) { return a == 0 ? 0 : a - 1; }

static uint64_t tak(uint64_t f, uint64_t x, uint64_t y, uint64_t z) {
  if (f == 0) return z;
  if (y < x)
    return tak(f - 1, tak(f - 1, pred(x), y, z), tak(f - 1, pred(y), z, x), tak(f - 1, pred(z), x, y));
  return z;
}

int main(int argc, char **argv) {
  if (argc != 5) { fprintf(stderr, "usage: tak FUEL X Y Z\n"); return 1; }
  uint64_t a[4];
  for (int i = 0; i < 4; i++) a[i] = strtoull(argv[i + 1], NULL, 10);
  printf("%" PRIu64 "\n", tak(a[0], a[1], a[2], a[3]));
  return 0;
}
