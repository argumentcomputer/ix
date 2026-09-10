#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

#ifndef EXPECTED_RESULT
#error "EXPECTED_RESULT must be defined"
#endif
extern uint64_t compilatrix_main(void);
static volatile uint64_t observed;
static void need(int condition, const char *message) {
    if (!condition) { fprintf(stderr, "upstream native: %s\n", message); exit(1); }
}
static uint64_t now(void) {
    struct timespec value;
    need(clock_gettime(CLOCK_MONOTONIC_RAW, &value) == 0, "timer failed");
    return (uint64_t)value.tv_sec * UINT64_C(1000000000) + value.tv_nsec;
}
__attribute__((noinline)) static void verify(void) {
    register uint64_t bx __asm__("rbx") = UINT64_C(0x1020304050607080);
    register uint64_t bp __asm__("rbp") = UINT64_C(0x2131415161718191);
    register uint64_t r12 __asm__("r12") = UINT64_C(0x32425262728292a2);
    register uint64_t r13 __asm__("r13") = UINT64_C(0x435363738393a3b3);
    register uint64_t r14 __asm__("r14") = UINT64_C(0x5464748494a4b4c4);
    register uint64_t r15 __asm__("r15") = UINT64_C(0x65758595a5b5c5d5);
    volatile uint64_t frame[32];
    for (size_t i = 0; i < 32; ++i) frame[i] = UINT64_C(0xc13fa9a902a6328f) ^ i;
    uintptr_t before, after;
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    __asm__ volatile("mov %%rsp, %0" : "=r"(before));
    uint64_t result = compilatrix_main();
    __asm__ volatile("mov %%rsp, %0" : "=r"(after));
    __asm__ volatile("" : "+r"(bx), "+r"(bp), "+r"(r12), "+r"(r13), "+r"(r14), "+r"(r15) : : "memory");
    need(result == EXPECTED_RESULT, "wrong result");
    need(before == after, "stack pointer changed");
    need(bx == UINT64_C(0x1020304050607080) && bp == UINT64_C(0x2131415161718191) &&
        r12 == UINT64_C(0x32425262728292a2) && r13 == UINT64_C(0x435363738393a3b3) &&
        r14 == UINT64_C(0x5464748494a4b4c4) && r15 == UINT64_C(0x65758595a5b5c5d5), "saved register changed");
    for (size_t i = 0; i < 32; ++i) need(frame[i] == (UINT64_C(0xc13fa9a902a6328f) ^ i), "caller frame changed");
}
__attribute__((noinline)) static uint64_t calls(uint64_t operations) {
    uint64_t sink = 0;
    for (uint64_t i = 0; i < operations; ++i) sink += compilatrix_main();
    return sink;
}
int main(int argc, char **argv) {
    verify();
    if (argc == 1) {
        printf("{\"value\":%u,\"saved_registers\":true,\"stack\":true,\"caller_frame\":true,\"heap_allocations\":0}\n", (unsigned)EXPECTED_RESULT);
        return 0;
    }
    need(argc == 3, "usage: executable [OPERATIONS SAMPLES]");
    char *end;
    uint64_t operations = strtoull(argv[1], &end, 10);
    need(*end == 0 && operations > 0 && operations <= UINT64_C(100000000000), "invalid operation count");
    uint64_t samples = strtoull(argv[2], &end, 10);
    need(*end == 0 && samples > 0 && samples <= 10, "invalid sample count");
    uint64_t warm = now(), warm_operations = 0;
    do { observed = calls(65536); warm_operations += 65536; } while (now() - warm < UINT64_C(1000000000));
    printf("{\"kind\":\"warmup\",\"elapsed_ns\":%" PRIu64 ",\"operations\":%" PRIu64 "}\n", now() - warm, warm_operations);
    fflush(stdout);
    for (uint64_t sample = 0; sample < samples; ++sample) {
        uint64_t start = now(), sink = calls(operations), elapsed = now() - start;
        observed = sink;
        need(sink == EXPECTED_RESULT * operations, "timed sink disagrees");
        struct rusage usage;
        need(getrusage(RUSAGE_SELF, &usage) == 0, "resource usage failed");
        printf("{\"kind\":\"sample\",\"sample\":%" PRIu64 ",\"operations\":%" PRIu64
            ",\"elapsed_ns\":%" PRIu64 ",\"sink\":%" PRIu64 ",\"peak_rss_kb\":%ld}\n",
            sample, operations, elapsed, sink, usage.ru_maxrss);
        fflush(stdout);
        verify();
    }
    return 0;
}
