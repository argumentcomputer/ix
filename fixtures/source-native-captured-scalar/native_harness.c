#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

#ifndef FAMILY
#error "FAMILY is required"
#endif
#ifndef STACK_DEPTH
#error "STACK_DEPTH is required"
#endif
struct result { uint64_t value, status; };
#ifndef CAPTURE
#error "CAPTURE is required"
#endif
extern struct result compilatrix_scalar(uint64_t);
extern struct result scalar_on_stack(void *, uint64_t, uint64_t);

/* The bridge's saved RSP uses RBX, whose preservation is part of the ABI.
   Six pushes preserve its caller's registers on the original stack. */
__asm__(
    ".text\n.globl scalar_on_stack\n.type scalar_on_stack,@function\n"
    "scalar_on_stack:\n"
    "push %rbp\npush %rbx\npush %r12\npush %r13\npush %r14\npush %r15\n"
    "mov %rsp,%rbx\nmov %rdi,%rsp\nmov %rsi,%rdi\nmov %rdx,%rsi\n"
    "call compilatrix_scalar\nmov %rbx,%rsp\n"
    "pop %r15\npop %r14\npop %r13\npop %r12\npop %rbx\npop %rbp\nret\n"
    ".size scalar_on_stack,.-scalar_on_stack\n");

static void need(int condition, const char *message) {
    if (!condition) { fprintf(stderr, "captured scalar native: %s\n", message); exit(1); }
}
static struct result expected(uint64_t a, uint64_t b) {
    (void)b;
    switch (FAMILY) {
    case 0: return (struct result){CAPTURE, 0};
    case 1: return (struct result){a == 0 ? CAPTURE : a - 1, 0};
    case 2: return (struct result){a < 3 ? CAPTURE : a - 3, 0};
    default: abort();
    }
}
__attribute__((noinline)) static void verify(uint64_t a, uint64_t b, void *top) {
    register uint64_t bx __asm__("rbx") = UINT64_C(0x1020304050607080);
    register uint64_t bp __asm__("rbp") = UINT64_C(0x2131415161718191);
    register uint64_t r12 __asm__("r12") = UINT64_C(0x32425262728292a2);
    register uint64_t r13 __asm__("r13") = UINT64_C(0x435363738393a3b3);
    register uint64_t r14 __asm__("r14") = UINT64_C(0x5464748494a4b4c4);
    register uint64_t r15 __asm__("r15") = UINT64_C(0x65758595a5b5c5d5);
    volatile uint64_t frame[16];
    for (size_t i = 0; i < 16; ++i) frame[i] = UINT64_C(0xc13fa9a902a6328f) ^ i;
    uintptr_t before, after;
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    __asm__ volatile("mov %%rsp,%0" : "=r"(before));
    struct result actual = compilatrix_scalar(a);
    __asm__ volatile("mov %%rsp,%0" : "=r"(after));
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    struct result wanted = expected(a, b);
    need(actual.value == wanted.value && actual.status == wanted.status, "wrong value/status");
    need(before == after, "stack pointer changed");
    need(bx == UINT64_C(0x1020304050607080) && bp == UINT64_C(0x2131415161718191) &&
        r12 == UINT64_C(0x32425262728292a2) && r13 == UINT64_C(0x435363738393a3b3) &&
        r14 == UINT64_C(0x5464748494a4b4c4) && r15 == UINT64_C(0x65758595a5b5c5d5), "saved register changed");
    for (size_t i = 0; i < 16; ++i) need(frame[i] == (UINT64_C(0xc13fa9a902a6328f) ^ i), "caller frame changed");
    actual = scalar_on_stack(top, a, b);
    need(actual.value == wanted.value && actual.status == wanted.status, "guarded-stack result changed");
}
int main(void) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    need(272 * STACK_DEPTH < page, "guarded reservation is too large");
    uint8_t *mapping = mmap(NULL, page * 3, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    need(mapping != MAP_FAILED, "stack mapping failed");
    uint8_t *low = mapping + page;
    need(mprotect(low, page, PROT_READ | PROT_WRITE) == 0, "stack permissions failed");
    void *top = low + 272 * STACK_DEPTH;
    for (size_t i = 272 * STACK_DEPTH; i < page; ++i) low[i] = (uint8_t)(i ^ 0xa7);
    const uint64_t m = UINT64_MAX;
    const uint64_t cases[][2] = {
        {0,0}, {0,1}, {1,0}, {1,1}, {2,3}, {3,2}, {7,7}, {7,19}, {19,7},
        {0,m}, {m,0}, {m,1}, {1,m}, {m,m}, {m-1,1}, {m-1,2}, {2,m-1}, {m,m-1}, {m-1,m}
    };
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) verify(cases[i][0], cases[i][1], top);
    uint64_t seed = UINT64_C(0xfedcba9876543210);
    for (size_t i = 0; i < 64; ++i) {
        seed = seed * UINT64_C(6364136223846793005) + 1;
        uint64_t a = seed;
        seed = seed * UINT64_C(6364136223846793005) + 1;
        verify(a, seed, top);
    }
    for (size_t i = 272 * STACK_DEPTH; i < page; ++i)
        need(low[i] == (uint8_t)(i ^ 0xa7), "guarded stack wrote above its reservation");
    need(munmap(mapping, page * 3) == 0, "stack unmap failed");
    printf("{\"calls\":166,\"saved_registers\":true,\"stack\":true,\"caller_frame\":true,\"guarded_stack\":true}\n");
    return 0;
}
