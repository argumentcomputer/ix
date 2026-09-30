/*
 * Runtime driver for backend objects (note 04 §6; untrusted test code).
 *
 * The object exports one SysV wrapper, ENTRY(void *region, a1, ..., a5),
 * returning {status, value} in rax:rdx (0 ok, 1 heap, 2 stack,
 * 3 natOverflow, 4 trap). The driver maps a private region and, per case,
 * sets up the context block as cx_init would: ctx = region + 64, the heads
 * above it zeroed, and below it stackBudget, bump, limit and regionBase
 * (the wrapper itself writes entrySp and stackLimit). It then calls the
 * wrapper with sentinels in rbx, rbp and r12-r15, and prints
 *
 *     status value ok
 *
 * where ok is 1 when the six sentinels and rsp came back unchanged.
 *
 * Cases come one per line on stdin: "budget a1 ... an" (at most five
 * arguments), or "seed S" to refill the region with the test pattern of
 * CompilatrixTests.Lir.Region (seed S, fixed region only). Built with
 * -DFIXED_REGION, the region is mapped at 0x10000, the address the Lean
 * test region uses, so programs that compute with absolute addresses agree
 * with the Lean models.
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#ifndef ENTRY
#error "ENTRY must name the exported wrapper"
#endif

struct result {
  uint64_t rax, rdx, rbx, rbp, r12, r13, r14, r15, rsp_before, rsp_after;
};

extern void ENTRY(void);
void call_with_sentinels(const uint64_t *args, struct result *out, void (*export)(void));

/* rdi = args (region, a1..a5), rsi = out, rdx = export. */
__asm__(
    ".text\n"
    ".globl call_with_sentinels\n"
    ".type call_with_sentinels, @function\n"
    "call_with_sentinels:\n"
    "  push %rbx\n"
    "  push %rbp\n"
    "  push %r12\n"
    "  push %r13\n"
    "  push %r14\n"
    "  push %r15\n"
    "  sub $8, %rsp\n"
    "  mov %rsi, (%rsp)\n"
    "  mov %rsp, 64(%rsi)\n"
    "  mov %rdx, %rax\n"
    "  mov 40(%rdi), %r9\n"
    "  mov 32(%rdi), %r8\n"
    "  mov 24(%rdi), %rcx\n"
    "  mov 16(%rdi), %rdx\n"
    "  mov 8(%rdi), %rsi\n"
    "  mov 0(%rdi), %rdi\n"
    "  movabs $0x1111111111111111, %rbx\n"
    "  movabs $0x2222222222222222, %rbp\n"
    "  movabs $0x3333333333333333, %r12\n"
    "  movabs $0x4444444444444444, %r13\n"
    "  movabs $0x5555555555555555, %r14\n"
    "  movabs $0x6666666666666666, %r15\n"
    "  call *%rax\n"
    "  mov (%rsp), %rcx\n"
    "  mov %rax, 0(%rcx)\n"
    "  mov %rdx, 8(%rcx)\n"
    "  mov %rbx, 16(%rcx)\n"
    "  mov %rbp, 24(%rcx)\n"
    "  mov %r12, 32(%rcx)\n"
    "  mov %r13, 40(%rcx)\n"
    "  mov %r14, 48(%rcx)\n"
    "  mov %r15, 56(%rcx)\n"
    "  mov %rsp, 72(%rcx)\n"
    "  add $8, %rsp\n"
    "  pop %r15\n"
    "  pop %r14\n"
    "  pop %r13\n"
    "  pop %r12\n"
    "  pop %rbp\n"
    "  pop %rbx\n"
    "  ret\n"
    ".size call_with_sentinels, .-call_with_sentinels\n");

#define REGION_SIZE ((size_t)1 << 16)
#define FIXED_BASE ((uintptr_t)0x10000)
/* The Lean test region: heap at base + 0x400, the model's region ends at base + 0x900. */
#define TEST_HEAP 0x400

static uint8_t *region;
static int patterned;

/* CompilatrixTests.Lir.Region.pattern */
static uint8_t pattern(uint64_t seed, uint64_t address) {
  return (uint8_t)((address * 0x9e3779b97f4a7c15ULL + seed) >> 29);
}

static void set_field(int offset, uint64_t value) {
  uint8_t *ctx = region + 64;
  memcpy(ctx + offset, &value, 8);
}

/* cx_init's job, for one case. With a pattern, only the fields the Lean
 * region sets are written; otherwise the heads are zeroed and the bump
 * allocator spans the rest of the region. */
static void init_context(uint64_t budget) {
  if (!patterned) {
    memset(region, 0, 64 + 640);
    set_field(-40, (uint64_t)(uintptr_t)(region + 1024));
    set_field(-32, (uint64_t)(uintptr_t)(region + REGION_SIZE));
    set_field(-24, (uint64_t)(uintptr_t)(region + 1024));
  }
  set_field(-48, budget);
}

int main(void) {
#ifdef FIXED_REGION
  region = mmap((void *)FIXED_BASE, REGION_SIZE, PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
  if (region != (uint8_t *)FIXED_BASE) {
    perror("mmap fixed region");
    return 2;
  }
#else
  region = mmap(NULL, REGION_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (region == MAP_FAILED) {
    perror("mmap region");
    return 2;
  }
#endif
  char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    if (strncmp(line, "seed ", 5) == 0) {
      uint64_t seed = strtoull(line + 5, NULL, 0);
      uint64_t base = (uint64_t)(uintptr_t)region;
      for (size_t i = 0; i < REGION_SIZE; i++) region[i] = pattern(seed, base + i);
      set_field(-24, base + TEST_HEAP);
      patterned = 1;
      continue;
    }
    uint64_t args[6] = {(uint64_t)(uintptr_t)region, 0, 0, 0, 0, 0};
    char *cursor = line;
    char *end;
    uint64_t budget = strtoull(cursor, &end, 0);
    if (end == cursor) continue;
    cursor = end;
    for (int i = 1; i < 6; i++) {
      uint64_t value = strtoull(cursor, &end, 0);
      if (end == cursor) break;
      args[i] = value;
      cursor = end;
    }
    init_context(budget);
    struct result r;
    call_with_sentinels(args, &r, ENTRY);
    int ok = r.rbx == 0x1111111111111111ULL && r.rbp == 0x2222222222222222ULL &&
             r.r12 == 0x3333333333333333ULL && r.r13 == 0x4444444444444444ULL &&
             r.r14 == 0x5555555555555555ULL && r.r15 == 0x6666666666666666ULL &&
             r.rsp_after == r.rsp_before;
    printf("%llu %llu %d\n", (unsigned long long)r.rax, (unsigned long long)r.rdx, ok);
    fflush(stdout);
  }
  return 0;
}
