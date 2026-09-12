#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#ifndef FAMILY
#error "FAMILY is required"
#endif
#ifndef STACK_DEPTH
#error "STACK_DEPTH is required"
#endif
_Static_assert(STACK_DEPTH > 0 && STACK_DEPTH <= 32, "finite activation depth");
#define WORK_WORDS (272 + 34 * STACK_DEPTH + 2)
#define WORK_BYTES (8 * WORK_WORDS)
struct result { uint64_t value, status; };
extern struct result heap_on_stack(void *, void *, uint64_t, uint64_t);

/* The generated ABI takes scalar words in RDI/RSI and the finite workspace
   in RDX. CALL places the external return address in its final word. The
   bridge checks the generated callee's registers before restoring its own. */
__asm__(
    ".text\n.globl heap_on_stack\n.type heap_on_stack,@function\n"
    "heap_on_stack:\n"
    "push %rbp\npush %rbx\npush %r12\npush %r13\npush %r14\npush %r15\nsub $32,%rsp\n"
    "mov %rsp,%rbx\nmov %rsi,16(%rbx)\nmov %rdi,%r8\nmov %rsi,%r9\n"
    "mov %rdx,%rdi\nmov %rcx,%rsi\nmov %r8,%rdx\n"
    "movabs $0x2131415161718191,%rbp\nmovabs $0x32425262728292a2,%r12\n"
    "movabs $0x435363738393a3b3,%r13\nmovabs $0x5464748494a4b4c4,%r14\n"
    "movabs $0x65758595a5b5c5d5,%r15\nmov %r9,%rsp\n"
    "call compilatrix_heap_cfg\n"
    "mov %rax,0(%rbx)\nmov %rdx,8(%rbx)\nmov %rsp,%r10\nmov %rbx,%rsp\n"
    "cmp 16(%rsp),%r10\njne 9f\n"
    "movabs $0x2131415161718191,%r11\ncmp %r11,%rbp\njne 9f\n"
    "movabs $0x32425262728292a2,%r11\ncmp %r11,%r12\njne 9f\n"
    "movabs $0x435363738393a3b3,%r11\ncmp %r11,%r13\njne 9f\n"
    "movabs $0x5464748494a4b4c4,%r11\ncmp %r11,%r14\njne 9f\n"
    "movabs $0x65758595a5b5c5d5,%r11\ncmp %r11,%r15\njne 9f\n"
    "mov 0(%rsp),%rax\nmov 8(%rsp),%rdx\njmp 10f\n"
    "9:\nxor %eax,%eax\nmov $2,%edx\n"
    "10:\nadd $32,%rsp\npop %r15\npop %r14\npop %r13\npop %r12\npop %rbx\npop %rbp\nret\n"
    ".size heap_on_stack,.-heap_on_stack\n");

static void need(int condition, const char *message) {
    if (!condition) { fprintf(stderr, "heap native family %d: %s\n", FAMILY, message); exit(1); }
}
static uint64_t demand(void) {
    return FAMILY == 8 ? 64 : (FAMILY == 3 || FAMILY == 5 || FAMILY == 6 ? 2 : 1);
}
static uint64_t expected(uint64_t a, uint64_t b) {
    if (FAMILY == 4) return b;
    if (FAMILY == 1 || FAMILY == 5) return a == 0 ? b : a - 1;
    if (FAMILY == 2) return a == 0 ? 0 : a - 1;
    return a;
}
static uint64_t poison(size_t index) { return UINT64_C(0xa7d31564e0cb982f) ^ (index * UINT64_C(0x0101010101010101)); }

__attribute__((noinline)) static void verify(uint64_t a, uint64_t b, uint64_t capacity,
                                            uint64_t *workspace, uint8_t *copy, size_t payload) {
    volatile uint64_t frame[16];
    for (size_t i = 0; i < 16; ++i) frame[i] = UINT64_C(0xc13fa9a902a6328f) ^ i;
    for (size_t i = 0; i < WORK_WORDS; ++i) workspace[i] = poison(i);
    workspace[1] = capacity;
    memcpy(copy, workspace, WORK_BYTES - 8);
    uintptr_t before, after;
    __asm__ volatile("mov %%rsp,%0" : "=r"(before) : : "memory");
    struct result result = heap_on_stack(workspace, workspace + WORK_WORDS, a, b);
    __asm__ volatile("mov %%rsp,%0" : "=r"(after) : : "memory");
    need(before == after, "caller stack changed");
    for (size_t i = 0; i < 16; ++i) need(frame[i] == (UINT64_C(0xc13fa9a902a6328f) ^ i), "caller frame changed");
    if (capacity < demand() || capacity > 64) {
        need(result.value == 0 && result.status == 1, "capacity rejection or saved register check failed");
        need(memcmp(copy, workspace, WORK_BYTES - 8) == 0, "rejection wrote heap or activation storage");
    } else {
        need(result.value == expected(a, b) && result.status == 0, "value/status/saved register check failed");
        uint64_t baseline = FAMILY < 5 ? 1 : 0;
        uint64_t allocations = baseline + demand();
        uint64_t reuses = FAMILY == 5 || FAMILY == 6 ? 1 : 0;
        uint64_t rcops = baseline + (FAMILY == 4 ? 1 : 0);
        uint64_t resets = FAMILY == 6 ? 2 : 0;
        uint64_t units = FAMILY == 5 ? 2 : (FAMILY == 6 ? 1 : 0);
        uint64_t header[] = {32 * demand(), capacity, allocations, allocations, reuses, rcops, resets, resets, units, 0};
        for (size_t i = 0; i < 10; ++i) need(workspace[i] == header[i], "exact arena header/counter mismatch");
        for (size_t i = 10; i < 16; ++i) need(workspace[i] == poison(i), "unused header word changed");
        for (size_t i = 0; i < demand(); ++i) need(workspace[16 + 4 * i] == 0, "cell was not reclaimed");
        for (size_t i = 16 + 4 * demand(); i < 272; ++i) need(workspace[i] == poison(i), "unused heap cell changed");
        if (FAMILY == 5) need(workspace[17] == 23 && workspace[18] == 19, "join/reuse fields changed");
        if (FAMILY == 6) need(workspace[17] == a, "credit/call/reuse runtime field changed");
        if (FAMILY == 4) need(workspace[17] == a && workspace[18] == b, "runtime pair fields changed");
    }
    for (size_t i = WORK_BYTES; i < payload; ++i)
        need(((uint8_t *)workspace)[i] == (uint8_t)(i ^ 0xa7), "write beyond finite workspace");
}

int main(void) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    size_t payload = ((WORK_BYTES + 64 + page - 1) / page) * page;
    uint8_t *mapping = mmap(NULL, payload + 2 * page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    need(mapping != MAP_FAILED, "workspace mapping failed");
    uint8_t *low = mapping + page;
    need(mprotect(low, payload, PROT_READ | PROT_WRITE) == 0, "workspace permissions failed");
    uint8_t *copy = malloc(WORK_BYTES);
    need(copy != NULL, "comparison storage allocation failed");
    for (size_t i = WORK_BYTES; i < payload; ++i) low[i] = (uint8_t)(i ^ 0xa7);
    const uint64_t m = UINT64_MAX;
    const uint64_t cases[][2] = {
        {0,0}, {0,1}, {1,0}, {1,1}, {2,3}, {3,2}, {7,7}, {7,19}, {19,7},
        {0,m}, {m,0}, {m,1}, {1,m}, {m,m}, {m-1,1}, {m-1,2}, {2,m-1}, {m,m-1}, {m-1,m}
    };
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i)
        verify(cases[i][0], cases[i][1], i % 2 == 0 ? demand() : 64, (uint64_t *)low, copy, payload);
    uint64_t seed = UINT64_C(0xfedcba9876543210);
    for (size_t i = 0; i < 64; ++i) {
        seed = seed * UINT64_C(6364136223846793005) + 1;
        uint64_t a = seed;
        seed = seed * UINT64_C(6364136223846793005) + 1;
        verify(a, seed, i % 2 == 0 ? demand() : 64, (uint64_t *)low, copy, payload);
    }
    const uint64_t rejected[] = {demand() - 1, 65, UINT64_MAX};
    for (size_t i = 0; i < 3; ++i) verify(7, 19, rejected[i], (uint64_t *)low, copy, payload);
    free(copy);
    need(munmap(mapping, payload + 2 * page) == 0, "workspace unmap failed");
    printf("{\"calls\":86,\"saved_registers\":true,\"stack\":true,\"caller_frame\":true,\"finite_workspace\":true,\"exact_counters\":true,\"reclaimed\":true,\"capacity_rejected\":true}\n");
    return 0;
}
