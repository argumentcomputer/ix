#include "common.h"
#include <stdlib.h>
#include <string.h>

extern unsigned int argc;
extern char **argv;
#ifdef BENCH_CAKEML_GC
extern int numGC;
extern long prevOcc, numAllocBytes, microsecs;
static int gc_before;
#endif
static int verifying;
static uint64_t row_index, warm_start, terminal_start;

static int command(const unsigned char *text, long length, const char *expected) {
    return length == (long)strlen(expected) && memcmp(text, expected, length) == 0;
}
void ffibench(unsigned char *config, long length, unsigned char *bytes, long size) {
    bench_need(size == 1024, "CakeML FFI packet size mismatch");
    if (command(config, length, "init")) {
        bench_need(argc == 4 || argc == 5, "invalid CakeML driver arguments");
        bench_implementation = argv[1]; verifying = strcmp(argv[2], "verify") == 0;
        bench_need((verifying && argc == 4) || (!verifying && argc == 5 && strcmp(argv[2], "run") == 0), "invalid CakeML mode");
        bench_load(argv[3], verifying ? NULL : argv[4]);
        bench_metadata();
        bench_put_word(bytes, verifying); bench_put_word(bytes + 8, bench_schedule.count);
        bench_put_word(bytes + 16, bench_schedule.samples); bench_put_word(bytes + 24, bench_schedule.warm_ns);
#ifdef BENCH_CAKEML_GC
        bench_put_word(bytes + 32, 1);
#else
        bench_put_word(bytes + 32, 0);
#endif
    } else if (command(config, length, "input")) {
        uint64_t id = bench_word(bytes);
        bench_need(id < INPUT_COUNT, "CakeML input id out of range");
        bench_put_word(bytes, bench_inputs[id].n);
        for (uint64_t i = 0; i < MAX_N; ++i) bench_put_word(bytes + 8 + i * 8, bench_inputs[id].values[i]);
    } else if (command(config, length, "row")) {
        row_index = bench_word(bytes);
        bench_need(row_index < bench_schedule.count, "CakeML row out of range");
        const BenchRow *row = &bench_schedule.rows[row_index];
        bench_put_word(bytes, row->id); bench_put_word(bytes + 8, row->n); bench_put_word(bytes + 16, row->domain);
        bench_put_word(bytes + 24, row->profile); bench_put_word(bytes + 32, row->operations);
    } else if (command(config, length, "sample-begin")) {
        bench_sample_begin();
#ifdef BENCH_CAKEML_GC
        gc_before = numGC;
#endif
    } else if (command(config, length, "clock-start")) bench_clock_start();
    else if (command(config, length, "clock-stop")) bench_clock_stop();
    else if (command(config, length, "sample-end")) {
        uint64_t sample = bench_word(bytes), sink = bench_word(bytes + 8);
        bench_sample_end(&bench_schedule.rows[row_index], sample, sink);
#ifdef BENCH_CAKEML_GC
        printf("{\"kind\":\"gc-sample\",\"row\":%" PRIu64 ",\"sample\":%" PRIu64
            ",\"collections\":%d,\"total_collections\":%d,\"last_post_gc_live_bytes\":%ld,"
            "\"allocated_bytes_at_last_gc\":%ld,\"total_gc_microseconds\":%ld}\n",
            bench_schedule.rows[row_index].id, sample, numGC - gc_before, numGC, prevOcc, numAllocBytes, microsecs);
#endif
    } else if (command(config, length, "warm-start")) warm_start = bench_now();
    else if (command(config, length, "warm-test")) bench_put_word(bytes, bench_now() - warm_start >= bench_schedule.warm_ns);
    else if (command(config, length, "warm-end")) {
        uint64_t operations = bench_word(bytes), sink = bench_word(bytes + 8);
        BenchRow row = {28, 64, 0, 1, operations};
        bench_need(sink == bench_expected_sink(&row, operations), "CakeML warm-up sink mismatch");
        printf("{\"kind\":\"warmup\",\"elapsed_ns\":%" PRIu64 ",\"operations\":%" PRIu64
            ",\"sink\":%" PRIu64 "}\n", bench_now() - warm_start, operations, sink);
    } else if (command(config, length, "control-start")) terminal_start = bench_now();
    else if (command(config, length, "control-end")) {
        uint64_t duration = bench_now() - terminal_start;
        bench_need(bench_word(bytes) == 0, "CakeML empty control mismatch");
        printf("{\"kind\":\"control\",\"name\":\"empty-reverse-handoff\",\"operations\":4194304,\"elapsed_ns\":%" PRIu64
            ",\"sink\":0}\n", duration);
    } else if (command(config, length, "verify")) {
        uint64_t id = bench_word(bytes), n = bench_word(bytes + 8), hash = bench_word(bytes + 16), emit = bench_word(bytes + 24);
        bench_need(id < INPUT_COUNT && n == bench_inputs[id].n && hash == bench_inputs[id].digest, "CakeML result metadata mismatch");
        uint64_t values[MAX_N];
        for (uint64_t i = 0; i < n; ++i) {
            values[i] = bench_word(bytes + 32 + 8 * i);
            bench_need(values[i] == bench_inputs[id].values[n - i - 1], "CakeML reversed value mismatch");
        }
        if (emit) {
            printf("{\"kind\":\"case\",\"id\":%" PRIu64 ",\"capacity\":null,\"values\":", id);
            bench_values(values, n);
            printf(",\"digest\":%" PRIu64 ",\"roots_dropped\":true}\n", hash);
        }
    } else if (command(config, length, "terminal-start")) terminal_start = bench_now();
    else if (command(config, length, "terminal-end")) {
#ifdef BENCH_CAKEML_GC
        printf("{\"kind\":\"terminal-gc\",\"elapsed_ns\":%" PRIu64 ",\"total_collections\":%d,\"post_gc_live_bytes\":%ld,"
            "\"rss_kb\":%" PRIu64 "}\n", bench_now() - terminal_start, numGC, prevOcc, bench_rss_kb());
#else
        bench_need(0, "terminal GC must use the diagnostic executable");
#endif
    } else if (command(config, length, "finish")) {
        if (verifying) printf("{\"kind\":\"verified\",\"cases\":585}\n");
        else printf("{\"kind\":\"completed\",\"rows\":%" PRIu64 ",\"samples_per_row\":%" PRIu64 "}\n",
            bench_schedule.count, bench_schedule.samples);
    } else bench_need(0, "unknown CakeML FFI command");
}
