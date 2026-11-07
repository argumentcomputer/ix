/*
 * MEAS-4 timing driver (untrusted measurement code). One executable per row:
 * this file plus the row's adapter (row_<row>.c), which provides row_init
 * and the three kernels on natural numbers, and the row's code.
 *
 * usage: <row> KERNEL REPS A [B]      KERNEL is fib, sum_loop or gcd
 *
 * The driver computes the result once, runs WARMUP untimed calls, then times
 * REPS calls in-process (the benchmark design's entry profile: the operation
 * with its guards and result handoff; no process or runtime startup). Every
 * call's argument passes through an empty asm so it cannot be hoisted, and
 * every result is compared with the first and folded into a sink. It prints
 *
 *     KERNEL REPS RESULT NS_PER_OP SINK
 *
 * With REPS = 0 only the setup and warm-up run, which lets `perf stat`
 * subtract them from a run with REPS calls.
 */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

void row_init(void);
uint64_t row_fib(uint64_t n);
uint64_t row_sum_loop(uint64_t n);
uint64_t row_gcd(uint64_t a, uint64_t b);

#define WARMUP 5

static uint64_t call_fib(uint64_t a, uint64_t b) { (void)b; return row_fib(a); }
static uint64_t call_sum_loop(uint64_t a, uint64_t b) { (void)b; return row_sum_loop(a); }
static uint64_t call_gcd(uint64_t a, uint64_t b) { return row_gcd(a, b); }

static uint64_t now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
  if (argc < 4 || argc > 5) {
    fprintf(stderr, "usage: %s KERNEL REPS A [B]\n", argv[0]);
    return 2;
  }
  uint64_t (*kernel)(uint64_t, uint64_t);
  if (strcmp(argv[1], "fib") == 0) kernel = call_fib;
  else if (strcmp(argv[1], "sum_loop") == 0) kernel = call_sum_loop;
  else if (strcmp(argv[1], "gcd") == 0) kernel = call_gcd;
  else {
    fprintf(stderr, "unknown kernel %s\n", argv[1]);
    return 2;
  }
  uint64_t reps = strtoull(argv[2], NULL, 10);
  uint64_t a = strtoull(argv[3], NULL, 10);
  uint64_t b = argc == 5 ? strtoull(argv[4], NULL, 10) : 0;
  row_init();
  uint64_t expected = kernel(a, b);
  uint64_t sink = expected;
  for (int w = 0; w < WARMUP; w++) {
    uint64_t x = a;
    __asm__ volatile("" : "+r"(x));
    sink = sink * 31 + kernel(x, b);
  }
  uint64_t start = now_ns();
  for (uint64_t r = 0; r < reps; r++) {
    uint64_t x = a;
    __asm__ volatile("" : "+r"(x));
    uint64_t v = kernel(x, b);
    if (v != expected) {
      fprintf(stderr, "result %" PRIu64 " differs from %" PRIu64 " at repetition %" PRIu64 "\n", v, expected, r);
      return 1;
    }
    sink = sink * 31 + v;
  }
  uint64_t stop = now_ns();
  double per = reps ? (double)(stop - start) / (double)reps : 0.0;
  printf("%s %" PRIu64 " %" PRIu64 " %.3f %" PRIu64 "\n", argv[1], reps, expected, per, sink);
  return 0;
}
