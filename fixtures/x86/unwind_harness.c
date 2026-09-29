/*
 * Native harness for the failure-exit fixture (note 05 §6.1).
 *
 * compilatrix_main(ctx, depth, mode) is an export wrapper: it saves the
 * callee-saved registers and its stack pointer at ctx[0], recurses `depth`
 * levels (each checking the stack against ctx[1]), and at the bottom either
 * returns 42 (mode 0: rax:rdx = 0:42) or fails (mode 1: rax:rdx = 1:0). A
 * failure, or a stack check that trips (rax:rdx = 2:0), leaves through the
 * exit group's `unwind`, which drops every frame the recursion pushed.
 *
 * call_with_sentinels loads sentinels into rbx, rbp and r12-r15, records rsp,
 * calls the export, and records rax, rdx, the six registers and rsp, so the
 * checks below see exactly what the export returned to its caller. This file
 * is test code; it is not part of any compiled program.
 */
#include <stdint.h>
#include <stdio.h>

#ifndef EXPECTED_RESULT
#error "EXPECTED_RESULT must be defined"
#endif

struct result {
  uint64_t rax, rdx, rbx, rbp, r12, r13, r14, r15, rsp_before, rsp_after;
};

extern void compilatrix_main(void);
void call_with_sentinels(uint64_t *ctx, uint64_t depth, uint64_t mode, struct result *out, void (*export)(void));

/* rdi = ctx, rsi = depth, rdx = mode, rcx = out, r8 = export. */
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
    "  mov %rcx, (%rsp)\n"
    "  mov %rsp, 64(%rcx)\n"
    "  movabs $0x1111111111111111, %rbx\n"
    "  movabs $0x2222222222222222, %rbp\n"
    "  movabs $0x3333333333333333, %r12\n"
    "  movabs $0x4444444444444444, %r13\n"
    "  movabs $0x5555555555555555, %r14\n"
    "  movabs $0x6666666666666666, %r15\n"
    "  call *%r8\n"
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

static int failures;

static void expect(const char *name, uint64_t *ctx, uint64_t depth, uint64_t mode, uint64_t status,
                   uint64_t value) {
  struct result r;
  call_with_sentinels(ctx, depth, mode, &r, compilatrix_main);
  int ok = r.rax == status && r.rdx == value && r.rbx == 0x1111111111111111ULL &&
           r.rbp == 0x2222222222222222ULL && r.r12 == 0x3333333333333333ULL &&
           r.r13 == 0x4444444444444444ULL && r.r14 == 0x5555555555555555ULL &&
           r.r15 == 0x6666666666666666ULL && r.rsp_after == r.rsp_before;
  if (!ok) {
    fprintf(stderr, "%s: rax:rdx = %llx:%llx (expected %llx:%llx), sentinels or rsp differ\n", name,
            (unsigned long long)r.rax, (unsigned long long)r.rdx, (unsigned long long)status,
            (unsigned long long)value);
    failures++;
  }
}

int main(void) {
  static uint64_t ctx[16];
  /* The typed run's outcome: depth 3, mode 1, status 1. */
  expect("local", ctx, 3, 1, (uint64_t)EXPECTED_RESULT, 0);
  /* The same context region serves a second, successful call. */
  expect("success after failure", ctx, 3, 0, 0, 42);
  expect("failure at depth 0", ctx, 0, 1, 1, 0);
  expect("failure at depth 1", ctx, 1, 1, 1, 0);
  /* A deep recursion under a small stack budget fails with status 2. */
  uint64_t here = 0;
  ctx[1] = (uint64_t)(uintptr_t)&here - 16384;
  expect("stack budget", ctx, 1000000, 0, 2, 0);
  ctx[1] = 0;
  expect("success after stack failure", ctx, 5, 0, 0, 42);
  return failures == 0 ? 0 : 1;
}
