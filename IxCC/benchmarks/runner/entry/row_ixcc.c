/*
 * The runner's adapter for the ixcc row (untrusted measurement code).
 * The row's code is `ixcc compile`'s object for the fixture's frozen
 * closure (fixtures/ixon-v4/bench-k1/<fixture>.ixe), which exports, as
 * IxCC/X86/Driver.lean models them,
 *
 *     cx_result cx_init(void *region, uint64_t size, uint64_t stack_budget);
 *     cx_result cx_entry(void *region, uint64_t a1, ..., uint64_t a5);
 *
 * each returning {status, value} in rax:rdx (0 ok, 1 heap, 2 stack,
 * 3 natOverflow, 4 trap). row_init maps one private region and calls
 * cx_init once; every row_entry then calls the root's SysV wrapper directly,
 * on this thread's stack (the wrapper records entrySp and the stack limit
 * on each call), so the wrapper's argument checks, tagging and callee-saved
 * saves are part of every call, as the entry profile requires. The result
 * must be a Nat (the tagged word 2n + 1); any other result or a nonzero
 * status ends the process.
 *
 * The stack budget is the main thread's stack limit less 1 MiB (at most
 * 1 GiB), which leaves the wrapper frame and the frameless leaf's slack
 * above the limit, as the driver contract (X86.Driver.Ok) asks; a deeper recursion
 * ends in status 2, not a fault. row_heap reports how far the bump pointer
 * moved since cx_init (Phase 1's immortal allocation).
 */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>

typedef struct {
  uint64_t status, value;
} cx_result;

extern cx_result cx_init(void *region, uint64_t size, uint64_t stack_budget);
extern cx_result cx_entry(void *region, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5);

#define REGION_SIZE ((uint64_t)64 << 20)
#define BUMP_OFFSET (64 - 40) /* ctx - 40, with ctx = region + 64 */
#define BUDGET_OFFSET (64 - 48) /* ctx - 48 */

static uint8_t *region;
static uint64_t bump_at_init;

static uint64_t bump(void) {
  uint64_t v;
  memcpy(&v, region + BUMP_OFFSET, 8);
  return v;
}

static uint64_t stack_budget(void) {
  struct rlimit limit;
  uint64_t budget = (uint64_t)1 << 30;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY) {
    uint64_t soft = (uint64_t)limit.rlim_cur;
    if (soft < ((uint64_t)2 << 20)) {
      fprintf(stderr, "the stack limit %" PRIu64 " is below 2 MiB\n", soft);
      exit(2);
    }
    if (soft - ((uint64_t)1 << 20) < budget) budget = soft - ((uint64_t)1 << 20);
  }
  return budget;
}

void row_init(void) {
  region = mmap(NULL, REGION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) {
    perror("mmap region");
    exit(2);
  }
  /* The stack budget at region + 16 (ctx - 48), where every export wrapper,
   * cx_init's included, reads it (X86.Driver.initBytes). */
  uint64_t budget = stack_budget();
  memcpy(region + BUDGET_OFFSET, &budget, 8);
  cx_result r = cx_init(region, REGION_SIZE, budget);
  if (r.status != 0) {
    fprintf(stderr, "cx_init failed with status %" PRIu64 "\n", r.status);
    exit(3);
  }
  bump_at_init = bump();
}

uint64_t row_entry(const uint64_t *a) {
  cx_result r = cx_entry(region, a[0], a[1], a[2], a[3], a[4]);
  if (r.status != 0) {
    fprintf(stderr, "cx_entry failed with status %" PRIu64 "\n", r.status);
    exit(3);
  }
  if ((r.value & 1) == 0) {
    fprintf(stderr, "cx_entry returned %#" PRIx64 ", not a scalar Nat\n", r.value);
    exit(3);
  }
  return r.value >> 1;
}

uint64_t row_heap(void) { return bump() - bump_at_init; }
