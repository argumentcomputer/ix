/* K2 foldl: C twin of CakeML foldl.cml (via Foldl.lean). The outer list
   holds n references to one shared inner list, as `repeat (repeat 1 n) n`
   shares its argument. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct icell { uint64_t head; struct icell *tail; } icell;
typedef struct lcell { icell *head; struct lcell *tail; } lcell;

static uint64_t add(uint64_t x, uint64_t y) { return x + y; }

static uint64_t foldl_i(uint64_t (*f)(uint64_t, uint64_t), uint64_t e, icell *xs) {
  for (; xs; xs = xs->tail) e = f(e, xs->head);
  return e;
}

static uint64_t add_sum(uint64_t x, icell *y) { return x + foldl_i(add, 0, y); }

static uint64_t foldl_l(uint64_t (*f)(uint64_t, icell *), uint64_t e, lcell *xs) {
  for (; xs; xs = xs->tail) e = f(e, xs->head);
  return e;
}

static icell *repeat_i(uint64_t x, uint64_t n) {
  icell *l = NULL;
  while (n-- > 0) {
    icell *c = malloc(sizeof *c);
    if (!c) abort();
    c->head = x; c->tail = l; l = c;
  }
  return l;
}

static lcell *repeat_l(icell *x, uint64_t n) {
  lcell *l = NULL;
  while (n-- > 0) {
    lcell *c = malloc(sizeof *c);
    if (!c) abort();
    c->head = x; c->tail = l; l = c;
  }
  return l;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: foldl N\n"); return 1; }
  uint64_t n = strtoull(argv[1], NULL, 10);
  printf("%" PRIu64 "\n", foldl_l(add_sum, 0, repeat_l(repeat_i(1, n), n)));
  return 0;
}
