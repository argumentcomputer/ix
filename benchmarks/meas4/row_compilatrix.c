/*
 * MEAS-4 adapter for the compilatrix-probe row (untrusted measurement code):
 * the objects backend-probe writes (lir_fib.o, lir_sumLoop.o, lir_gcd.o),
 * each exporting the SysV wrapper of note 05 §6.1,
 *
 *     {status, value} lir_<kernel>(void *region, a1, ...)    in rax:rdx
 *
 * which takes natural numbers (below 2^63) and returns the tagged result.
 * The context is set up once as fixtures/x86/backend_driver.c does
 * (cx_init's job): ctx = region + 64, with stackBudget, bump, limit and
 * regionBase below it; the wrapper itself writes entrySp and stackLimit on
 * every call. The wrapper's cost is part of every call (the entry profile).
 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

typedef struct {
  uint64_t status, value;
} exit_t;

extern exit_t lir_fib(void *region, uint64_t n);
extern exit_t lir_sumLoop(void *region, uint64_t n);
extern exit_t lir_gcd(void *region, uint64_t a, uint64_t b);

#define REGION_SIZE ((size_t)1 << 16)
#define STACK_BUDGET ((uint64_t)1 << 20)

static uint8_t *region;

static void set_field(int offset, uint64_t value) { memcpy(region + 64 + offset, &value, 8); }

void row_init(void) {
  region = mmap(NULL, REGION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (region == MAP_FAILED) {
    perror("mmap region");
    exit(2);
  }
  memset(region, 0, 64 + 640);
  set_field(-40, (uint64_t)(uintptr_t)(region + 1024));
  set_field(-32, (uint64_t)(uintptr_t)(region + REGION_SIZE));
  set_field(-24, (uint64_t)(uintptr_t)(region + 1024));
  set_field(-48, STACK_BUDGET);
}

static uint64_t untag(exit_t r) {
  if (r.status != 0) {
    fprintf(stderr, "kernel failed with status %" PRIu64 "\n", r.status);
    exit(3);
  }
  return r.value >> 1;
}

uint64_t row_fib(uint64_t n) { return untag(lir_fib(region, n)); }
uint64_t row_sum_loop(uint64_t n) { return untag(lir_sumLoop(region, n)); }
uint64_t row_gcd(uint64_t a, uint64_t b) { return untag(lir_gcd(region, a, b)); }
