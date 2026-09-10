#ifndef COMPILATRIX_BENCH_ARENA_H
#define COMPILATRIX_BENCH_ARENA_H

#include <stdint.h>

enum { BENCH_MAX_LENGTH = 64, BENCH_MAX_CAPACITY = 66, HEADER_WORDS = 10, CELL_WORDS = 4 };
enum { CURSOR, CAPACITY, ALLOCS, FREES, REUSES, LIVE, PEAK, RCOPS, PAYLOAD, RESERVATIONS };

typedef struct {
    uint64_t header[HEADER_WORDS];
    uint64_t cells[][CELL_WORDS];
} Arena;

uint64_t compilatrix_runtime_reverse(Arena *arena, uint64_t length);
uint64_t compilatrix_runtime_drop(Arena *arena, uint64_t root);

#endif
