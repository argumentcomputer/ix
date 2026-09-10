#include "common.h"
#include <stdlib.h>
#include <string.h>

static BenchItem inputs[CHUNK], outputs[CHUNK];
static volatile uint64_t observed;

static uint64_t run_chunk(const BenchRow *row, uint64_t offset, int timed) {
    uint64_t sink = 0;
    if (row->profile == 0) {
        for (uint64_t i = 0; i < CHUNK; ++i) inputs[i] = backend_make(bench_input(row, offset + i), row->n + 2);
        if (timed) bench_clock_start();
        for (uint64_t i = 0; i < CHUNK; ++i) {
            BenchItem owned = inputs[i]; inputs[i] = (BenchItem){0, 0};
            outputs[i] = backend_reverse(owned, row->n);
        }
        if (timed) bench_clock_stop();
        for (uint64_t i = 0; i < CHUNK; ++i) {
            BenchItem owned = outputs[i]; outputs[i] = (BenchItem){0, 0};
            sink += backend_digest(owned); backend_release(owned);
        }
    } else {
        if (timed) bench_clock_start();
        for (uint64_t i = 0; i < CHUNK; ++i) {
            BenchItem owned = backend_make(bench_input(row, offset + i), row->n + 2);
            owned = backend_reverse(owned, row->n);
            sink += backend_digest(owned); backend_release(owned);
        }
        if (timed) bench_clock_stop();
    }
    return sink;
}

/* Opaque call and bounded slot traffic, without reversal. It exposes driver
   overhead; its raw time is never subtracted from the workload samples. */
__attribute__((noinline)) static BenchItem handoff(BenchItem item) {
    __asm__ volatile("" : "+r"(item.owner), "+r"(item.value) : : "memory");
    return item;
}
static void control(void) {
    uint64_t total = 0, count = 1024 * CHUNK;
    uint64_t before = bench_now();
    for (uint64_t j = 0; j < 1024; ++j)
        for (uint64_t i = 0; i < CHUNK; ++i) outputs[i] = handoff(inputs[i]);
    uint64_t elapsed = bench_now() - before;
    for (uint64_t i = 0; i < CHUNK; ++i) total += outputs[i].value;
    observed = total;
    printf("{\"kind\":\"control\",\"name\":\"opaque-empty-handoff\",\"operations\":%" PRIu64
        ",\"elapsed_ns\":%" PRIu64 ",\"sink\":%" PRIu64 "}\n", count, elapsed, total);
}

int main(int argc, char **argv) {
    bench_need(argc == 4 || argc == 5, "usage: executable IMPLEMENTATION verify DATASET | IMPLEMENTATION run DATASET SCHEDULE");
    bench_implementation = argv[1];
    int verify = strcmp(argv[2], "verify") == 0;
    bench_need((verify && argc == 4) || (!verify && argc == 5 && strcmp(argv[2], "run") == 0), "unknown driver mode");
    bench_load(argv[3], verify ? NULL : argv[4]);
    backend_init(); bench_metadata(); control();
    if (verify) {
        uint64_t count = 0;
        for (uint64_t i = 0; i < INPUT_COUNT; ++i)
            for (uint64_t j = 0; j < backend_capacity_count(&bench_inputs[i]); ++j) {
                backend_verify(&bench_inputs[i], bench_inputs[i].n + 2 + j, 1); ++count;
            }
        printf("{\"kind\":\"verified\",\"cases\":%" PRIu64 "}\n", count);
    } else {
        BenchRow warm = {28, 64, 0, 1, CHUNK};
        uint64_t before = bench_now(), operations = 0, sink = 0;
        do { sink += run_chunk(&warm, operations, 0); operations += CHUNK; }
        while (bench_now() - before < bench_schedule.warm_ns);
        bench_need(sink == bench_expected_sink(&warm, operations), "warm-up sink mismatch");
        observed = sink;
        printf("{\"kind\":\"warmup\",\"elapsed_ns\":%" PRIu64 ",\"operations\":%" PRIu64
            ",\"sink\":%" PRIu64 "}\n", bench_now() - before, operations, sink);
        for (uint64_t r = 0; r < bench_schedule.count; ++r) {
            const BenchRow *row = &bench_schedule.rows[r];
            for (uint64_t sample = 0; sample < bench_schedule.samples; ++sample) {
                bench_sample_begin(); sink = 0;
                for (uint64_t op = 0; op < row->operations; op += CHUNK) sink += run_chunk(row, op, 1);
                observed = sink; bench_sample_end(row, sample, sink);
                for (uint64_t pattern = 0; pattern < (row->domain ? 1 : 6); ++pattern)
                    backend_verify(bench_input(row, pattern), row->n + 2, 0);
            }
        }
        printf("{\"kind\":\"completed\",\"rows\":%" PRIu64 ",\"samples_per_row\":%" PRIu64 "}\n",
            bench_schedule.count, bench_schedule.samples);
    }
    backend_finish();
    return 0;
}
