/*
 * The runner's adapter for the diagnostic lir-kernel row (untrusted
 * measurement code): the early backend probe's hand-written Lir kernels
 * (IxCCTests/Lir/Kernels.lean) through the current backend, as
 * `backend-probe DIR` writes them (lir_fib.o, lir_sumLoop.o, lir_gcd.o), each
 * exporting the SysV export wrapper,
 *
 *     {status, value} lir_<kernel>(void *region, a1, ...)    in rax:rdx
 *
 * The objects carry no cx_init, so the context is set up once as
 * benchmarks/meas4/row_ixcc.c does; the wrapper writes entrySp and
 * the stack limit on every call. FIXTURE_<name> selects the kernel; only
 * fib, sum-loop and gcd have one.
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

#if defined(FIXTURE_fib)
extern exit_t lir_fib(void *region, uint64_t n);
uint64_t row_entry(const uint64_t *a) { return untag(lir_fib(region, a[0])); }
#elif defined(FIXTURE_sum_loop)
extern exit_t lir_sumLoop(void *region, uint64_t n);
uint64_t row_entry(const uint64_t *a) { return untag(lir_sumLoop(region, a[0])); }
#elif defined(FIXTURE_gcd)
extern exit_t lir_gcd(void *region, uint64_t a, uint64_t b);
uint64_t row_entry(const uint64_t *a) { return untag(lir_gcd(region, a[0], a[1])); }
#else
#error "no Lir kernel for this fixture"
#endif

uint64_t row_heap(void) { return UINT64_MAX; }
