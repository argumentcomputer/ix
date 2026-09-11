#include "common.h"
#include "arena.h"
#include <stdlib.h>
#include <string.h>

static void prepare(Arena *arena, const BenchInput *input, uint64_t capacity) {
    memset(arena, 0, 80 + 32 * capacity);
    arena->header[CURSOR] = 32 * (input->n + 1);
    arena->header[CAPACITY] = 32 * capacity;
    arena->header[ALLOCS] = arena->header[LIVE] = arena->header[PEAK] = input->n + 1;
    for (uint64_t i = 1; i <= input->n; ++i) {
        arena->cells[i][0] = 1;
        arena->cells[i][1] = input->values[input->n - i];
        arena->cells[i][2] = (uintptr_t)arena->cells[i - 1];
    }
}
void backend_init(void) {}
void backend_finish(void) {}
BenchItem backend_make(const BenchInput *input, uint64_t capacity) {
    Arena *arena = malloc(80 + 32 * capacity);
    bench_need(arena != NULL, "arena allocation failed");
    prepare(arena, input, capacity);
    return (BenchItem){arena, input->n};
}
BenchItem backend_reverse(BenchItem input, uint64_t n) {
    return (BenchItem){input.owner, compilatrix_runtime_reverse(input.owner, n)};
}
uint64_t backend_digest(BenchItem output) {
    uint64_t *cell = (uint64_t *)(uintptr_t)output.value, hash = UINT64_C(14695981039346656037);
    while (cell[0] == 1) {
        hash = (hash ^ cell[1]) * UINT64_C(1099511628211);
        cell = (uint64_t *)(uintptr_t)cell[2];
    }
    return hash;
}
void backend_release(BenchItem output) {
    compilatrix_runtime_drop(output.owner, output.value);
    free(output.owner);
}
uint64_t backend_capacity_count(const BenchInput *input) { return 65 - input->n; }

/* Same physical SysV observations as the existing N2 gate. Diagnostics only. */
__attribute__((noinline))
static uint64_t checked_call(uint64_t (*entry)(Arena *, uint64_t), Arena *arena, uint64_t root) {
    register uint64_t bx __asm__("rbx") = UINT64_C(0x1020304050607080);
    register uint64_t bp __asm__("rbp") = UINT64_C(0x2131415161718191);
    register uint64_t r12 __asm__("r12") = UINT64_C(0x32425262728292a2);
    register uint64_t r13 __asm__("r13") = UINT64_C(0x435363738393a3b3);
    register uint64_t r14 __asm__("r14") = UINT64_C(0x5464748494a4b4c4);
    register uint64_t r15 __asm__("r15") = UINT64_C(0x65758595a5b5c5d5);
    uintptr_t before, after;
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    __asm__ volatile("mov %%rsp, %0" : "=r"(before));
    uint64_t result = entry(arena, root);
    __asm__ volatile("mov %%rsp, %0" : "=r"(after));
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    bench_need(before == after, "stack pointer changed");
    bench_need(bx == UINT64_C(0x1020304050607080) && bp == UINT64_C(0x2131415161718191) &&
        r12 == UINT64_C(0x32425262728292a2) && r13 == UINT64_C(0x435363738393a3b3) &&
        r14 == UINT64_C(0x5464748494a4b4c4) && r15 == UINT64_C(0x65758595a5b5c5d5), "callee-saved register changed");
    return result;
}
static uint64_t spare(uint64_t cell, uint64_t field) {
    return UINT64_C(0xc13fa9a902a6328f) ^ (cell * 17 + field);
}
static void frame(const uint64_t *storage, uint64_t words, const Arena *arena, uint64_t n, uint64_t capacity) {
    bench_need(storage[0] == UINT64_C(0xfedcba9876543210) && storage[1] == UINT64_C(0x123456789abcdef0) &&
        storage[words + 2] == UINT64_C(0xfedcba9876543210) && storage[words + 3] == UINT64_C(0x123456789abcdef0),
        "arena canary changed");
    for (uint64_t i = n + 2; i < capacity; ++i)
        for (uint64_t j = 0; j < 4; ++j) bench_need(arena->cells[i][j] == spare(i, j), "unused capacity changed");
}
static void headers(const Arena *arena, uint64_t n, uint64_t capacity, int released) {
    const uint64_t expected[10] = {32 * (n + 2), 32 * capacity, n + 2, released ? n + 2 : 1,
        n, released ? 0 : n + 1, n + 2, 0, 2 * n, 0};
    bench_need(memcmp(arena->header, expected, sizeof expected) == 0, "arena counters mismatch");
}
static void heap(const Arena *arena, uint64_t n) {
    printf("{\"header\":"); bench_values(arena->header, 10); printf(",\"cells\":[");
    for (uint64_t i = 0; i < n + 2; ++i) {
        const uint64_t *cell = arena->cells[i];
        printf("%s[%" PRIu64 ",%" PRIu64 ",", i ? "," : "", cell[0], cell[1]);
        if (cell[2] == 0) printf("null");
        else printf("%" PRIu64, (cell[2] - (uint64_t)(uintptr_t)arena->cells) / 32);
        printf(",%" PRIu64 "]", cell[3]);
    }
    printf("]}");
}
void backend_verify(const BenchInput *input, uint64_t capacity, int emit) {
    uint64_t n = input->n, words = 10 + 4 * capacity;
    uint64_t *storage = malloc((words + 4) * 8);
    bench_need(storage != NULL, "diagnostic allocation failed");
    storage[0] = storage[words + 2] = UINT64_C(0xfedcba9876543210);
    storage[1] = storage[words + 3] = UINT64_C(0x123456789abcdef0);
    Arena *arena = (Arena *)(storage + 2);
    prepare(arena, input, capacity);
    for (uint64_t i = n + 2; i < capacity; ++i)
        for (uint64_t j = 0; j < 4; ++j) arena->cells[i][j] = spare(i, j);
    uint64_t root = checked_call(compilatrix_runtime_reverse, arena, n);
    bench_need(root == (uintptr_t)arena->cells[1], "wrong arena result root");
    headers(arena, n, capacity, 0); frame(storage, words, arena, n, capacity);
    uint64_t values[MAX_N];
    for (uint64_t i = 0; i < n + 2; ++i) {
        const uint64_t *cell = arena->cells[i];
        if (i == 0) bench_need(cell[0] == 3 && cell[1] == 0 && cell[2] == 0 && cell[3] == 0, "old nil not freed");
        else if (i == n + 1) bench_need(cell[0] == 0 && cell[1] == 0 && cell[2] == 0 && cell[3] == 0, "new nil invalid");
        else {
            bench_need(cell[0] == 1 && cell[1] == input->values[n - i] &&
                cell[2] == (uintptr_t)arena->cells[i + 1] && cell[3] == 0, "reversed cell mismatch");
            values[i - 1] = cell[1];
        }
    }
    uint64_t hash = backend_digest((BenchItem){arena, root});
    bench_need(hash == input->digest, "arena digest mismatch");
    if (emit) {
        printf("{\"kind\":\"case\",\"id\":%" PRIu64 ",\"capacity\":%" PRIu64 ",\"values\":",
            n * 9 + input->pattern, capacity);
        bench_values(values, n); printf(",\"digest\":%" PRIu64 ",\"returned\":", hash); heap(arena, n);
    }
    bench_need(checked_call(compilatrix_runtime_drop, arena, root) == 0, "release result mismatch");
    headers(arena, n, capacity, 1); frame(storage, words, arena, n, capacity);
    for (uint64_t i = 0; i < n + 2; ++i)
        bench_need(arena->cells[i][0] == 3 && arena->cells[i][1] == 0 &&
            arena->cells[i][2] == 0 && arena->cells[i][3] == 0, "incomplete arena release");
    if (emit) {
        printf(",\"reclaimed\":"); heap(arena, n);
        printf(",\"abi_preserved\":true,\"canaries_preserved\":true,\"unused_capacity_preserved\":true}\n");
    }
    free(storage);
}
