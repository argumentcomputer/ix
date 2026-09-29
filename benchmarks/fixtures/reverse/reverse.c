/* K2 reverse: C twin of CakeML reverse.cml (via Reverse.lean). Naive
   quadratic reverse over cons cells; append relinks its uniquely owned first
   argument in place, as Lean's reference counting reuses those cells. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct cell { uint64_t head; struct cell *tail; } cell;

static cell *cons(uint64_t x, cell *t) {
  cell *c = malloc(sizeof *c);
  if (!c) abort();
  c->head = x;
  c->tail = t;
  return c;
}

static cell *append(cell *xs, cell *ys) {
  if (!xs) return ys;
  xs->tail = append(xs->tail, ys);
  return xs;
}

static cell *rev(cell *xs) {
  if (!xs) return NULL;
  cell *rest = xs->tail;
  xs->tail = NULL; /* the cell of x :: xs becomes [x] */
  return append(rev(rest), xs);
}

static cell *mk_list(uint64_t n) {
  cell *l = NULL;
  for (uint64_t i = 1; i <= n; i++) l = cons(i, l);
  return l; /* [n, n-1, ..., 1] */
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: reverse N\n"); return 1; }
  cell *r = rev(mk_list(strtoull(argv[1], NULL, 10)));
  uint64_t len = 0, sum = 0;
  for (cell *c = r; c; c = c->tail) { len++; sum = (sum * 31 + c->head) % 1000000007; }
  printf("%" PRIu64 " %" PRIu64 "\n", len, sum);
  return 0;
}
