/*
 * The benchmark runner's timing driver (untrusted measurement code). One
 * executable per row and fixture: this file, the row's adapter
 * (row_<row>.c) and the row's code. The adapter provides
 *
 *     void row_init(void);                      once, before the first call
 *     uint64_t row_entry(const uint64_t *a);    the fixture's entry on a[0 .. arity)
 *     uint64_t row_heap(void);                  bytes the row's code allocated since
 *                                               row_init; UINT64_MAX if not observed
 *
 * Entry profile (docs/benchmark-plan.md: the operation with its guards and
 * result handoff; no process or runtime startup):
 *
 *     BIN REPS WARMUP A1 [A2 ... A5]
 *
 * calls row_init once, then WARMUP untimed calls (at least one: the first
 * result is the expected value), then times REPS calls in one
 * CLOCK_MONOTONIC interval. Before every call the arguments pass through an
 * empty asm with a memory clobber, so a call cannot be hoisted or merged;
 * every result is compared with the first and folded into an
 * order-sensitive sink. It prints
 *
 *     REPS RESULT NS_PER_OP SINK HEAP
 *
 * With REPS = 0 only the setup and the warm-up run, which lets `perf stat`
 * subtract them from a run with REPS calls.
 *
 * Built with -DPROCESS, the driver is the process profile's program instead:
 * `BIN A1 [A2 ... A5]` initialises the row, makes one call and prints the
 * result as the fixture's own `main` does.
 */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

void row_init(void);
uint64_t row_entry(const uint64_t *a);
uint64_t row_heap(void);

#define MAX_ARGS 5

static int parse_args(int argc, char **argv, int first, uint64_t *args) {
  int n = argc - first;
  if (n < 1 || n > MAX_ARGS) return -1;
  for (int i = 0; i < MAX_ARGS; i++) args[i] = 0;
  for (int i = 0; i < n; i++) {
    char *end;
    args[i] = strtoull(argv[first + i], &end, 10);
    if (*end != 0 || end == argv[first + i]) return -1;
  }
  return n;
}

#ifdef PROCESS

int main(int argc, char **argv) {
  uint64_t args[MAX_ARGS];
  if (parse_args(argc, argv, 1, args) < 0) {
    fprintf(stderr, "usage: %s A1 [A2 ... A5]\n", argv[0]);
    return 2;
  }
  row_init();
  printf("%" PRIu64 "\n", row_entry(args));
  return 0;
}

#else

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
  uint64_t args[MAX_ARGS];
  if (argc < 4 || parse_args(argc, argv, 3, args) < 0) {
    fprintf(stderr, "usage: %s REPS WARMUP A1 [A2 ... A5]\n", argv[0]);
    return 2;
  }
  uint64_t reps = strtoull(argv[1], NULL, 10);
  uint64_t warmup = strtoull(argv[2], NULL, 10);
  if (warmup == 0) warmup = 1;
  row_init();
  uint64_t x[MAX_ARGS];
  for (int i = 0; i < MAX_ARGS; i++) x[i] = args[i];
  __asm__ volatile("" : : "r"(x) : "memory");
  uint64_t expected = row_entry(x);
  uint64_t sink = expected;
  for (uint64_t w = 1; w < warmup; w++) {
    for (int i = 0; i < MAX_ARGS; i++) x[i] = args[i];
    __asm__ volatile("" : : "r"(x) : "memory");
    uint64_t v = row_entry(x);
    if (v != expected) {
      fprintf(stderr, "warm-up result %" PRIu64 " differs from %" PRIu64 "\n", v, expected);
      return 1;
    }
    sink = sink * 31 + v;
  }
  uint64_t start = now_ns();
  for (uint64_t r = 0; r < reps; r++) {
    for (int i = 0; i < MAX_ARGS; i++) x[i] = args[i];
    __asm__ volatile("" : : "r"(x) : "memory");
    uint64_t v = row_entry(x);
    if (v != expected) {
      fprintf(stderr, "result %" PRIu64 " differs from %" PRIu64 " at repetition %" PRIu64 "\n", v, expected, r);
      return 1;
    }
    sink = sink * 31 + v;
  }
  uint64_t stop = now_ns();
  double per = reps ? (double)(stop - start) / (double)reps : 0.0;
  printf("%" PRIu64 " %" PRIu64 " %.3f %" PRIu64 " %" PRIu64 "\n", reps, expected, per, sink, row_heap());
  return 0;
}

#endif
