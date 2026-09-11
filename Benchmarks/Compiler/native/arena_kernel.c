/* One C implementation is compiled unchanged by CompCert, GCC, and Clang.
   The caller supplies mapped, aligned storage for the declared capacity.
   All integer checks precede cell pointer formation. The guards, counters,
   cell reuse, and complete release match native-reverse/1's production ABI. */
#include "arena.h"

uint64_t compilatrix_runtime_reverse(Arena *arena, uint64_t length) {
    uint64_t base = (uint64_t)(uintptr_t)arena;
    uint64_t capacity, cursor, index, accumulator;
    if (length > BENCH_MAX_LENGTH || base == 0 || base % 8 != 0)
        return 0;
    capacity = arena->header[CAPACITY];
    cursor = 32 * (length + 1);
    if (capacity > 32 * BENCH_MAX_CAPACITY || capacity % 32 != 0 ||
        capacity < cursor + 32 || base > UINT64_MAX - 80 - capacity)
        return 0;
    if (arena->header[CURSOR] != cursor ||
        arena->header[ALLOCS] != length + 1 || arena->header[FREES] != 0 ||
        arena->header[REUSES] != 0 || arena->header[LIVE] != length + 1 ||
        arena->header[PEAK] != length + 1 || arena->header[RCOPS] != 0 ||
        arena->header[PAYLOAD] != 0 || arena->header[RESERVATIONS] != 0)
        return 0;
    if (arena->cells[0][0] != 0 || arena->cells[0][1] != 0 ||
        arena->cells[0][2] != 0 || arena->cells[0][3] != 0)
        return 0;
    for (index = 1; index <= length; ++index) {
        if (arena->cells[index][0] != 1 || arena->cells[index][3] != 0 ||
            arena->cells[index][2] != (uint64_t)(uintptr_t)arena->cells[index - 1])
            return 0;
    }

    index = length + 1;
    arena->cells[index][0] = 0;
    arena->cells[index][1] = 0;
    arena->cells[index][2] = 0;
    arena->cells[index][3] = 0;
    accumulator = (uint64_t)(uintptr_t)arena->cells[index];
    arena->header[CURSOR] += 32;
    ++arena->header[ALLOCS];
    ++arena->header[LIVE];
    arena->header[PEAK] = arena->header[LIVE];
    for (index = length; index != 0; --index) {
        arena->cells[index][2] = accumulator;
        accumulator = (uint64_t)(uintptr_t)arena->cells[index];
        ++arena->header[REUSES];
        arena->header[PAYLOAD] += 2;
    }
    arena->cells[0][0] = 3;
    ++arena->header[FREES];
    --arena->header[LIVE];
    return accumulator;
}

/* As in the emitted release entry, root must own a well-formed returned
   chain. Invalid-input diagnostics exercise reversal's guarded entry. */
uint64_t compilatrix_runtime_drop(Arena *arena, uint64_t root) {
    uint64_t current = root;
    while (current != 0) {
        uint64_t *cell = (uint64_t *)(uintptr_t)current;
        uint64_t next = cell[0] == 1 ? cell[2] : 0;
        cell[0] = 3;
        cell[1] = 0;
        cell[2] = 0;
        cell[3] = 0;
        ++arena->header[FREES];
        --arena->header[LIVE];
        current = next;
    }
    return 0;
}
