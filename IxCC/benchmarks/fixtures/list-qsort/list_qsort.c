/* K2 list-qsort: C twin of CakeML qsort.cml (via ListQsort.lean). Functional
   quicksort on cons cells with the head as pivot; partition and append relink
   uniquely owned cells in place, as Lean's reference counting reuses them. */
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

/* part p l (l1, l2): elements with p h are prepended to l1, the rest to l2. */
static void part(cell *l, uint64_t pivot, cell **l1, cell **l2) {
  while (l) {
    cell *next = l->tail;
    if (l->head <= pivot) { l->tail = *l1; *l1 = l; }
    else { l->tail = *l2; *l2 = l; }
    l = next;
  }
}

static cell *append(cell *xs, cell *ys) {
  if (!xs) return ys;
  xs->tail = append(xs->tail, ys);
  return xs;
}

static cell *qsort_list(cell *l) {
  if (!l) return NULL;
  cell *l1 = NULL, *l2 = NULL;
  part(l->tail, l->head, &l1, &l2);
  l->tail = NULL; /* the cell of h :: t becomes [h] */
  return append(qsort_list(l1), append(l, qsort_list(l2)));
}

static cell *mk_list(uint64_t n) {
  cell *l = NULL;
  for (uint64_t i = 1; i <= n; i++) l = cons(i, l);
  return l; /* [n, n-1, ..., 1] */
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: list-qsort N\n"); return 1; }
  uint64_t n = strtoull(argv[1], NULL, 10);
  cell *r = qsort_list(append(mk_list(n), mk_list(n)));
  uint64_t len = 0, sum = 0;
  for (cell *c = r; c; c = c->tail) { len++; sum = (sum * 31 + c->head) % 1000000007; }
  printf("%" PRIu64 " %" PRIu64 "\n", len, sum);
  return 0;
}
