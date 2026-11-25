/* C harness for IxCC-compiled K4 `blake3.o` (untrusted measurement wrapper).
 * Links against `blake3.o` (`cx_init` + `cx_entry` or `cx_blake3Bench`),
 * decodes the returned `ByteArray` cell (header tag 0x7F02, size 32, payload
 * at offset 24), and prints the 32-byte digest as 64 lowercase hex chars.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>

typedef struct { uint64_t status, value; } cx_result;

extern cx_result cx_init(void *region, uint64_t size, uint64_t stack_budget);
extern cx_result cx_blake3Bench(void *region, uint64_t n) __attribute__((weak));
extern cx_result cx_entry(void *region, uint64_t n) __attribute__((weak));

#ifndef IXCC_BLAKE3_REGION_SIZE
#define IXCC_BLAKE3_REGION_SIZE ((uint64_t)4ULL << 30)
#endif
#define IXCC_BUDGET_OFFSET (64 - 48)
#define IXCC_TAG_BYTEARRAY 0x7F02ULL

static uint64_t stack_budget(void) {
  struct rlimit lim;
  uint64_t budget = (uint64_t)1ULL << 30;
  if (getrlimit(RLIMIT_STACK, &lim) == 0 && lim.rlim_cur != RLIM_INFINITY) {
    uint64_t soft = (uint64_t)lim.rlim_cur;
    if (soft < ((uint64_t)2ULL << 20)) {
      fprintf(stderr, "blake3 harness: stack limit too small: %" PRIu64 "\n", soft);
      exit(2);
    }
    if (soft - ((uint64_t)1ULL << 20) < budget) budget = soft - ((uint64_t)1ULL << 20);
  }
  return budget;
}

int main(int argc, char **argv) {
  if (argc != 2) {
    fprintf(stderr, "usage: blake3 N\n");
    return 1;
  }
  char *end = NULL;
  errno = 0;
  unsigned long long n = strtoull(argv[1], &end, 10);
  if (errno != 0 || end == argv[1] || *end != '\0') {
    fprintf(stderr, "blake3 harness: invalid N: %s\n", argv[1]);
    return 1;
  }
  uint8_t *region = mmap(NULL, IXCC_BLAKE3_REGION_SIZE, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  if (region == MAP_FAILED) { perror("mmap"); return 2; }
  uint64_t budget = stack_budget();
  memcpy(region + IXCC_BUDGET_OFFSET, &budget, 8);
  cx_result r0 = cx_init(region, IXCC_BLAKE3_REGION_SIZE, budget);
  if (r0.status != 0) {
    fprintf(stderr, "blake3 harness: cx_init failed (status=%" PRIu64 ")\n", r0.status);
    return 3;
  }
  cx_result r;
  if (cx_blake3Bench) {
    r = cx_blake3Bench(region, (uint64_t)n);
  } else if (cx_entry) {
    r = cx_entry(region, (uint64_t)n);
  } else {
    fprintf(stderr, "blake3 harness: missing cx_blake3Bench / cx_entry symbol\n");
    return 2;
  }
  if (r.status != 0) {
    fprintf(stderr, "blake3 harness: entry failed (status=%" PRIu64 ")\n", r.status);
    return 3;
  }
  if ((r.value & 1ULL) != 0 || r.value == 0) {
    fprintf(stderr, "blake3 harness: expected ByteArray cell, got %#" PRIx64 "\n", r.value);
    return 4;
  }
  const uint64_t *cell = (const uint64_t *)(uintptr_t)r.value;
  uint64_t tag = (cell[0] >> 16) & 0xFFFFULL;
  uint64_t sz = cell[1];
  if (tag != IXCC_TAG_BYTEARRAY || sz != 32ULL) {
    fprintf(stderr, "blake3 harness: unexpected ByteArray header tag=0x%" PRIx64 " size=%" PRIu64 "\n", tag, sz);
    return 4;
  }
  const uint8_t *bytes = (const uint8_t *)(cell + 3);
  for (int i = 0; i < 32; i++) printf("%02x", bytes[i]);
  putchar('\n');
  return 0;
}
