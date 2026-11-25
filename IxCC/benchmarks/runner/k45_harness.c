/*
 * Process-profile C harness for linking IxCC relocatable objects (.o) whose
 * entry result shape is not yet emitted by `ixcc compile --exe` (for example,
 * K4 `blake3` returning `ByteArray` or K2/K3 fixtures returning `Nat x Nat`).
 *
 * Compile-time configuration:
 *   -DRESULT_BYTEARRAY_HEX   print ByteArray cell payload as lowercase hex + '\n'
 *   -DRESULT_NAT_PAIR        print (Nat, Nat) constructor cell as "%llu %llu\n"
 *   -DRESULT_NAT             print tagged Nat as "%llu\n" (default)
 *   -DREGION_BYTES=<bytes>   arena region size (default 64 MiB)
 *   -DSTACK_BYTES=<bytes>    stack budget upper bound (default 8 MiB)
 *
 * Untrusted benchmark measurement harness; not part of IxCC or its trusted base.
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

#ifndef REGION_BYTES
#define REGION_BYTES ((uint64_t)64 << 20)
#endif

#ifndef STACK_BYTES
#define STACK_BYTES ((uint64_t)8 << 20)
#endif

#define BUDGET_OFFSET (64 - 48) /* ctx - 48, with ctx = region + 64 */
#define MAX_ARGS 5
#define TAG_BYTE_ARRAY 0x7F02u

static uint64_t compute_stack_budget(void) {
  uint64_t budget = (uint64_t)STACK_BYTES;
  struct rlimit limit;
  if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY) {
    uint64_t soft = (uint64_t)limit.rlim_cur;
    if (soft < ((uint64_t)2 << 20)) {
      fprintf(stderr, "k45_harness: stack limit %" PRIu64 " is below 2 MiB\n", soft);
      exit(2);
    }
    uint64_t safe = soft - ((uint64_t)1 << 20);
    if (safe < budget) budget = safe;
  }
  return budget;
}

int main(int argc, char **argv) {
  int n = argc - 1;
  if (n < 1 || n > MAX_ARGS) {
    fprintf(stderr, "usage: %s A1 [A2 ... A5]\n", argv[0]);
    return 2;
  }
  uint64_t args[MAX_ARGS] = {0, 0, 0, 0, 0};
  for (int i = 0; i < n; i++) {
    char *end = NULL;
    args[i] = strtoull(argv[1 + i], &end, 10);
    if (*end != '\0' || end == argv[1 + i]) {
      fprintf(stderr, "k45_harness: invalid Nat argument '%s'\n", argv[1 + i]);
      return 2;
    }
  }

  uint8_t *region = mmap(NULL, (size_t)REGION_BYTES, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) {
    perror("k45_harness: mmap region");
    return 2;
  }

  uint64_t budget = compute_stack_budget();
  memcpy(region + BUDGET_OFFSET, &budget, 8);
  cx_result init_r = cx_init(region, (uint64_t)REGION_BYTES, budget);
  if (init_r.status != 0) {
    fprintf(stderr, "k45_harness: cx_init failed with status %" PRIu64 "\n", init_r.status);
    return 3;
  }

  cx_result r = cx_entry(region, args[0], args[1], args[2], args[3], args[4]);
  if (r.status != 0) {
    fprintf(stderr, "k45_harness: cx_entry failed with status %" PRIu64 "\n", r.status);
    return 3;
  }

#if defined(RESULT_BYTEARRAY_HEX)
  if ((r.value & 1u) != 0 || r.value == 0) {
    fprintf(stderr, "k45_harness: expected ByteArray pointer, got %#" PRIx64 "\n", r.value);
    return 3;
  }
  const uint8_t *cell = (const uint8_t *)(uintptr_t)r.value;
  uint64_t hdr = 0, len = 0;
  memcpy(&hdr, cell + 0, 8);
  memcpy(&len, cell + 8, 8);
  uint32_t tag = (uint32_t)((hdr >> 16) & 0xFFFFu);
  if (tag != TAG_BYTE_ARRAY) {
    fprintf(stderr, "k45_harness: unexpected ByteArray tag %#x (expected %#x)\n", tag, TAG_BYTE_ARRAY);
    return 3;
  }
  const uint8_t *bytes = cell + 24;
  static const char hex[] = "0123456789abcdef";
  for (uint64_t i = 0; i < len; i++) {
    putchar(hex[bytes[i] >> 4]);
    putchar(hex[bytes[i] & 0x0Fu]);
  }
  putchar('\n');
#elif defined(RESULT_NAT_PAIR)
  if ((r.value & 1u) != 0 || r.value == 0) {
    fprintf(stderr, "k45_harness: expected Prod pointer, got %#" PRIx64 "\n", r.value);
    return 3;
  }
  const uint8_t *cell = (const uint8_t *)(uintptr_t)r.value;
  uint64_t fst = 0, snd = 0;
  memcpy(&fst, cell + 8, 8);
  memcpy(&snd, cell + 16, 8);
  if ((fst & 1u) == 0 || (snd & 1u) == 0) {
    fprintf(stderr, "k45_harness: non-scalar Nat pair (%#" PRIx64 ", %#" PRIx64 ")\n", fst, snd);
    return 3;
  }
  printf("%" PRIu64 " %" PRIu64 "\n", fst >> 1, snd >> 1);
#else
  if ((r.value & 1u) == 0) {
    fprintf(stderr, "k45_harness: expected scalar Nat, got %#" PRIx64 "\n", r.value);
    return 3;
  }
  printf("%" PRIu64 "\n", r.value >> 1);
#endif
  return 0;
}
