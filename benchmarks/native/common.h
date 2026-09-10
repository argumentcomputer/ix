#ifndef COMPILATRIX_BENCH_COMMON_H
#define COMPILATRIX_BENCH_COMMON_H
#include <inttypes.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

enum { INPUT_COUNT = 585, MAX_N = 64, MAX_C = 66, CHUNK = 4096, ROW_COUNT = 38 };
typedef struct { uint64_t n, pattern, domain, seed, values[MAX_N], digest; } BenchInput;
typedef struct { uint64_t id, n, domain, profile, operations; } BenchRow;
typedef struct {
    BenchRow rows[ROW_COUNT];
    uint64_t count, samples, warm_ns, chunk, mode;
} BenchSchedule;
extern BenchInput bench_inputs[INPUT_COUNT];
extern BenchSchedule bench_schedule;
extern const char *bench_implementation;
void bench_need(int ok, const char *message);
uint64_t bench_word(const unsigned char *bytes);
void bench_put_word(unsigned char *bytes, uint64_t value);
void bench_load(const char *datasets, const char *schedule);
uint64_t bench_now(void);
uint64_t bench_rss_kb(void);
void bench_metadata(void);
const BenchInput *bench_input(const BenchRow *row, uint64_t operation);
uint64_t bench_expected_sink(const BenchRow *row, uint64_t operations);
void bench_values(const uint64_t *values, uint64_t n);
void bench_sample_begin(void);
void bench_clock_start(void);
void bench_clock_stop(void);
uint64_t bench_elapsed(void);
void bench_sample_end(const BenchRow *row, uint64_t sample, uint64_t sink);

typedef struct { void *owner; uint64_t value; } BenchItem;
void backend_init(void);
void backend_finish(void);
BenchItem backend_make(const BenchInput *input, uint64_t capacity);
BenchItem backend_reverse(BenchItem input, uint64_t n);
uint64_t backend_digest(BenchItem output);
void backend_release(BenchItem output);
void backend_verify(const BenchInput *input, uint64_t capacity, int emit);
uint64_t backend_capacity_count(const BenchInput *input);
#endif
