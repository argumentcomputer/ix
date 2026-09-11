#define _GNU_SOURCE
#include "common.h"
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

BenchInput bench_inputs[INPUT_COUNT];
BenchSchedule bench_schedule;
const char *bench_implementation;
static uint64_t elapsed, started, chunks, minimum_chunk;
static struct rusage sample_usage;
static uint64_t sample_envelope;

void bench_need(int ok, const char *message) {
    if (!ok) { fprintf(stderr, "benchmark: %s\n", message); exit(1); }
}
uint64_t bench_word(const unsigned char *bytes) {
    uint64_t value = 0;
    for (unsigned i = 0; i < 8; ++i) value |= (uint64_t)bytes[i] << (8 * i);
    return value;
}
void bench_put_word(unsigned char *bytes, uint64_t value) {
    for (unsigned i = 0; i < 8; ++i) bytes[i] = value >> (8 * i);
}
static uint64_t read_word(FILE *file) {
    unsigned char bytes[8];
    bench_need(fread(bytes, 1, 8, file) == 8, "truncated binary input");
    return bench_word(bytes);
}
static FILE *open_binary(const char *name, const char *magic) {
    FILE *file = fopen(name, "rb");
    unsigned char actual[8];
    bench_need(file != NULL, "cannot open binary input");
    bench_need(fread(actual, 1, 8, file) == 8 && memcmp(actual, magic, 8) == 0, "wrong binary magic");
    return file;
}
static void close_binary(FILE *file) {
    bench_need(fgetc(file) == EOF && !ferror(file), "trailing binary input");
    bench_need(fclose(file) == 0, "cannot close binary input");
}
void bench_load(const char *datasets, const char *schedule) {
    FILE *file = open_binary(datasets, "CPBN001\n");
    bench_need(read_word(file) == INPUT_COUNT, "wrong dataset inventory");
    for (uint64_t id = 0; id < INPUT_COUNT; ++id) {
        BenchInput *input = &bench_inputs[id];
        input->n = read_word(file); input->pattern = read_word(file);
        input->domain = read_word(file); input->seed = read_word(file);
        bench_need(input->n == id / 9 && input->pattern == id % 9 &&
            input->domain == (id % 9 < 6 ? 0 : id % 9 - 5), "noncanonical dataset metadata");
        for (uint64_t i = 0; i < MAX_N; ++i) {
            input->values[i] = read_word(file);
            bench_need(i < input->n || input->values[i] == 0, "nonzero dataset padding");
            bench_need(input->domain != 0 || input->values[i] < (UINT64_C(1) << 30), "primary value out of range");
        }
        input->digest = UINT64_C(14695981039346656037);
        for (uint64_t i = input->n; i != 0; --i)
            input->digest = (input->digest ^ input->values[i - 1]) * UINT64_C(1099511628211);
    }
    close_binary(file);
    if (schedule == NULL) return;
    file = open_binary(schedule, "CPBS001\n");
    bench_schedule.count = read_word(file); bench_schedule.samples = read_word(file);
    bench_schedule.warm_ns = read_word(file); bench_schedule.chunk = read_word(file);
    bench_schedule.mode = read_word(file);
    bench_need(bench_schedule.count > 0 && bench_schedule.count <= ROW_COUNT &&
        bench_schedule.samples > 0 && bench_schedule.samples <= 10 &&
        bench_schedule.warm_ns <= UINT64_C(10000000000) && bench_schedule.chunk == CHUNK &&
        bench_schedule.mode <= 2, "invalid schedule header");
    if (bench_schedule.mode == 2)
        bench_need(bench_schedule.count == ROW_COUNT && bench_schedule.samples == 3 &&
            bench_schedule.warm_ns >= UINT64_C(1000000000), "incomplete measurement schedule");
    uint64_t seen = 0;
    const uint64_t lengths[10] = {0, 1, 2, 4, 8, 16, 32, 48, 63, 64};
    const uint64_t stress_lengths[3] = {1, 16, 64};
    for (uint64_t i = 0; i < bench_schedule.count; ++i) {
        BenchRow *row = &bench_schedule.rows[i];
        row->id = read_word(file); row->n = read_word(file); row->domain = read_word(file);
        row->profile = read_word(file); row->operations = read_word(file);
        bench_need(row->id < ROW_COUNT, "schedule row id out of range");
        uint64_t local = row->id % 19;
        bench_need(row->profile == row->id / 19 && row->domain == (local < 10 ? 0 : 1 + (local - 10) / 3) &&
            row->n == (local < 10 ? lengths[local] : stress_lengths[(local - 10) % 3]) &&
            row->operations > 0 && row->operations <= UINT64_C(1000000000000) &&
            row->operations % (CHUNK * 6) == 0 && !(seen & (UINT64_C(1) << row->id)), "invalid schedule row");
        seen |= UINT64_C(1) << row->id;
    }
    close_binary(file);
}
uint64_t bench_now(void) {
    struct timespec value;
    bench_need(clock_gettime(CLOCK_MONOTONIC_RAW, &value) == 0, "monotonic timer unavailable");
    return (uint64_t)value.tv_sec * UINT64_C(1000000000) + value.tv_nsec;
}
uint64_t bench_rss_kb(void) {
    FILE *file = fopen("/proc/self/statm", "r");
    unsigned long pages, resident;
    bench_need(file != NULL && fscanf(file, "%lu %lu", &pages, &resident) == 2, "cannot read process RSS");
    fclose(file);
    return (uint64_t)resident * (uint64_t)sysconf(_SC_PAGESIZE) / 1024;
}
void bench_metadata(void) {
    uint64_t minimum = UINT64_MAX, sum = 0;
    for (unsigned i = 0; i < 10000; ++i) {
        uint64_t before = bench_now(), delta = bench_now() - before;
        if (delta && delta < minimum) minimum = delta;
        sum += delta;
    }
    struct timespec resolution;
    bench_need(clock_getres(CLOCK_MONOTONIC_RAW, &resolution) == 0, "cannot read timer resolution");
    printf("{\"kind\":\"metadata\",\"format\":\"compilatrix/benchmark-native/1\",\"implementation\":\"%s\","
        "\"timer\":\"CLOCK_MONOTONIC_RAW\",\"resolution_ns\":%" PRIu64 ",\"timer_pair_min_ns\":%" PRIu64
        ",\"timer_pair_mean_ns\":%.4f,\"initial_rss_kb\":%" PRIu64 "}\n", bench_implementation,
        (uint64_t)resolution.tv_sec * UINT64_C(1000000000) + resolution.tv_nsec, minimum, sum / 10000.0, bench_rss_kb());
}
const BenchInput *bench_input(const BenchRow *row, uint64_t operation) {
    uint64_t pattern = row->domain == 0 ? operation % 6 : row->domain + 5;
    return &bench_inputs[row->n * 9 + pattern];
}
uint64_t bench_expected_sink(const BenchRow *row, uint64_t operations) {
    if (row->domain != 0) return bench_input(row, 0)->digest * operations;
    uint64_t cycle = 0, rest = 0;
    for (uint64_t i = 0; i < 6; ++i) {
        cycle += bench_input(row, i)->digest;
        if (i < operations % 6) rest += bench_input(row, i)->digest;
    }
    return cycle * (operations / 6) + rest;
}
void bench_values(const uint64_t *values, uint64_t n) {
    printf("[");
    for (uint64_t i = 0; i < n; ++i) printf("%s%" PRIu64, i ? "," : "", values[i]);
    printf("]");
}
void bench_sample_begin(void) {
    elapsed = chunks = 0; minimum_chunk = UINT64_MAX;
    bench_need(getrusage(RUSAGE_SELF, &sample_usage) == 0, "cannot read sample resource usage");
    sample_envelope = bench_now();
}
void bench_clock_start(void) { started = bench_now(); }
void bench_clock_stop(void) {
    uint64_t delta = bench_now() - started;
    elapsed += delta; ++chunks;
    if (delta < minimum_chunk) minimum_chunk = delta;
}
uint64_t bench_elapsed(void) { return elapsed; }
static uint64_t cpu_ns(struct rusage *usage) {
    return ((uint64_t)usage->ru_utime.tv_sec + usage->ru_stime.tv_sec) * UINT64_C(1000000000) +
        ((uint64_t)usage->ru_utime.tv_usec + usage->ru_stime.tv_usec) * 1000;
}
void bench_sample_end(const BenchRow *row, uint64_t sample, uint64_t sink) {
    struct rusage usage;
    uint64_t envelope = bench_now() - sample_envelope;
    bench_need(getrusage(RUSAGE_SELF, &usage) == 0, "cannot read resource usage");
    bench_need(sink == bench_expected_sink(row, row->operations), "timed sink mismatch");
    bench_need(chunks == row->operations / CHUNK && elapsed > 0, "invalid timed chunk count");
    printf("{\"kind\":\"sample\",\"implementation\":\"%s\",\"mode\":%" PRIu64
        ",\"row\":%" PRIu64 ",\"sample\":%" PRIu64 ",\"operations\":%" PRIu64
        ",\"elapsed_ns\":%" PRIu64 ",\"chunks\":%" PRIu64 ",\"timer_calls\":%" PRIu64
        ",\"minimum_chunk_ns\":%" PRIu64 ",\"sink\":%" PRIu64 ",\"envelope_ns\":%" PRIu64
        ",\"envelope_cpu_ns\":%" PRIu64 ",\"rss_kb\":%" PRIu64 ",\"peak_rss_kb\":%ld"
        ",\"minor_faults\":%ld,\"major_faults\":%ld,\"voluntary_switches\":%ld,\"involuntary_switches\":%ld}\n",
        bench_implementation, bench_schedule.mode, row->id, sample, row->operations, elapsed, chunks, chunks * 2,
        minimum_chunk, sink, envelope, cpu_ns(&usage) - cpu_ns(&sample_usage), bench_rss_kb(), usage.ru_maxrss,
        usage.ru_minflt - sample_usage.ru_minflt, usage.ru_majflt - sample_usage.ru_majflt,
        usage.ru_nvcsw - sample_usage.ru_nvcsw, usage.ru_nivcsw - sample_usage.ru_nivcsw);
    fflush(stdout);
}
