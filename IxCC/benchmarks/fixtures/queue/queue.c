/* K2 queue: C twin of CakeML queue.cml (via Queue.lean). A two-list
   functional queue; cons cells are reversed in place and freed when popped,
   as Lean's reference counting reuses them. */
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct cell { uint64_t head; struct cell *tail; } cell;
typedef struct { cell *f, *r; } queue;

static cell *cons(uint64_t x, cell *t) {
  cell *c = malloc(sizeof *c);
  if (!c) abort();
  c->head = x;
  c->tail = t;
  return c;
}

static cell *reverse_aux(cell *l, cell *acc) {
  while (l) {
    cell *next = l->tail;
    l->tail = acc;
    acc = l;
    l = next;
  }
  return acc;
}

static queue checkf(queue q) {
  if (!q.f) { q.f = reverse_aux(q.r, NULL); q.r = NULL; }
  return q;
}

static queue snoc(queue q, uint64_t x) { q.r = cons(x, q.r); return checkf(q); }

/* CakeML's head and tail are partial; the empty cases are unreachable for n > 0. */
static uint64_t head(queue q) { return q.f ? q.f->head : 0; }

static queue tail(queue q) {
  if (!q.f) return q;
  cell *c = q.f;
  q.f = c->tail;
  free(c);
  return checkf(q);
}

static queue use_queue(uint64_t n, queue q) {
  while (n != 0) {
    q = tail(snoc(snoc(q, n - 1), n - 1));
    n--;
  }
  return q;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: queue N\n"); return 1; }
  queue q = use_queue(strtoull(argv[1], NULL, 10), (queue){NULL, NULL});
  printf("%" PRIu64 "\n", head(q));
  return 0;
}
