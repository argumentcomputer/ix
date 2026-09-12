#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* Fixed public ABI bounds, independent of producer-reported resource counts. */
#define WORK_WORDS (272 + 34 * 32 + 2)
#define WORK_BYTES (8 * WORK_WORDS)
struct result { uint64_t value, status; };
extern struct result scaling_on_stack(void *, void *, uint64_t);

__asm__(
    ".text\n.globl scaling_on_stack\n.type scaling_on_stack,@function\n"
    "scaling_on_stack:\n"
    "push %rbp\npush %rbx\npush %r12\npush %r13\npush %r14\npush %r15\nsub $32,%rsp\n"
    "mov %rsp,%rbx\nmov %rsi,16(%rbx)\nmov %rdi,%r8\nmov %rsi,%r9\n"
    "mov %rdx,%rdi\nxor %esi,%esi\nmov %r8,%rdx\n"
    "movabs $0x2131415161718191,%rbp\nmovabs $0x32425262728292a2,%r12\n"
    "movabs $0x435363738393a3b3,%r13\nmovabs $0x5464748494a4b4c4,%r14\n"
    "movabs $0x65758595a5b5c5d5,%r15\nmov %r9,%rsp\n"
    "call compilatrix_scaling\n"
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
    ".size scaling_on_stack,.-scaling_on_stack\n");

static const char *family;
static uint64_t size;
static unsigned calls;
static void need(int condition, const char *message) {
    if (!condition) { fprintf(stderr, "scaling native %s/%" PRIu64 ": %s\n", family, size, message); exit(1); }
}
static uint64_t demand(void) {
    return strcmp(family, "allocations") == 0 ? size : (strcmp(family, "call-depth") == 0 ? 1 : 0);
}
static uint64_t expected(uint64_t a) {
    return strcmp(family, "branches") == 0 || strcmp(family, "joins") == 0 ? (a > size ? a - size : 0) : a;
}
static uint64_t poison(size_t i) { return UINT64_C(0xa7d31564e0cb982f) ^ (i * UINT64_C(0x0101010101010101)); }

__attribute__((noinline)) static void verify(uint64_t a, uint64_t capacity,
                                            uint64_t *workspace, uint8_t *copy, size_t payload) {
    volatile uint64_t frame[16];
    for (size_t i = 0; i < 16; ++i) frame[i] = UINT64_C(0xc13fa9a902a6328f) ^ i;
    for (size_t i = 0; i < WORK_WORDS; ++i) workspace[i] = poison(i);
    workspace[1] = capacity;
    memcpy(copy, workspace, WORK_BYTES - 8);
    uintptr_t before, after;
    __asm__ volatile("mov %%rsp,%0" : "=r"(before) : : "memory");
    struct result result = scaling_on_stack(workspace, workspace + WORK_WORDS, a);
    __asm__ volatile("mov %%rsp,%0" : "=r"(after) : : "memory");
    need(before == after, "caller stack changed");
    for (size_t i = 0; i < 16; ++i) need(frame[i] == (UINT64_C(0xc13fa9a902a6328f) ^ i), "caller frame changed");
    if (capacity < demand() || capacity > 64) {
        need(result.value == 0 && result.status == 1, "capacity rejection or saved registers disagree");
        need(memcmp(copy, workspace, WORK_BYTES - 8) == 0, "rejection wrote workspace");
    } else {
        need(result.value == expected(a) && result.status == 0, "value/status/saved registers disagree");
        uint64_t allocations = 1 + demand();
        uint64_t rcops = 1 + (strcmp(family, "call-depth") == 0 ? 1 : 0);
        uint64_t header[] = {32 * demand(), capacity, allocations, allocations, 0, rcops, 0, 0, 0, 0};
        for (size_t i = 0; i < 10; ++i) need(workspace[i] == header[i], "exact arena counters disagree");
        for (size_t i = 10; i < 16; ++i) need(workspace[i] == poison(i), "unused header changed");
        for (size_t i = 0; i < demand(); ++i) need(workspace[16 + 4 * i] == 0, "cell not reclaimed");
        for (size_t i = 16 + 4 * demand(); i < 272; ++i) need(workspace[i] == poison(i), "unused cell changed");
        if (strcmp(family, "call-depth") == 0)
            need(workspace[17] == a && workspace[18] == a, "runtime pair fields changed");
    }
    for (size_t i = WORK_BYTES; i < payload; ++i)
        need(((uint8_t *)workspace)[i] == (uint8_t)(i ^ 0xa7), "write beyond workspace");
    ++calls;
}

int main(int argc, char **argv) {
    family = argc > 1 ? argv[1] : "missing";
    need(argc == 3, "expected FAMILY SIZE");
    char *end;
    size = strtoull(argv[2], &end, 10);
    need(*end == '\0' && size > 0 && size <= 1024, "invalid size");
    need(strcmp(family, "declarations") == 0 || strcmp(family, "call-depth") == 0 ||
         strcmp(family, "branches") == 0 || strcmp(family, "allocations") == 0 || strcmp(family, "joins") == 0,
         "unknown family");
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    size_t payload = ((WORK_BYTES + 64 + page - 1) / page) * page;
    uint8_t *mapping = mmap(NULL, payload + 2 * page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    need(mapping != MAP_FAILED, "workspace mapping failed");
    uint8_t *low = mapping + page;
    need(mprotect(low, payload, PROT_READ | PROT_WRITE) == 0, "workspace permissions failed");
    uint8_t *copy = malloc(WORK_BYTES);
    need(copy != NULL, "comparison allocation failed");
    for (size_t i = WORK_BYTES; i < payload; ++i) low[i] = (uint8_t)(i ^ 0xa7);
    const uint64_t cases[] = {0, 1, 2, 3, 7, 19, 31, 32, 33, 63, 64, 127, 255, UINT64_MAX - 1, UINT64_MAX};
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i)
        verify(cases[i], i % 2 == 0 ? demand() : 64, (uint64_t *)low, copy, payload);
    uint64_t seed = UINT64_C(0xfedcba9876543210);
    for (size_t i = 0; i < 16; ++i) {
        seed = seed * UINT64_C(6364136223846793005) + 1;
        verify(seed, demand(), (uint64_t *)low, copy, payload);
    }
    if (demand() > 0) verify(7, demand() - 1, (uint64_t *)low, copy, payload);
    verify(7, 65, (uint64_t *)low, copy, payload);
    verify(7, UINT64_MAX, (uint64_t *)low, copy, payload);
    free(copy);
    need(munmap(mapping, payload + 2 * page) == 0, "workspace unmap failed");
    printf("{\"calls\":%u,\"values\":true,\"saved_registers\":true,\"finite_workspace\":true,\"exact_counters\":true,\"reclaimed\":true,\"capacity_rejected\":true}\n", calls);
    return 0;
}
