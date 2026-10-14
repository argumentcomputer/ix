#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int (*main_function)(int, char **, char **);
typedef int (*start_function)(main_function, int, char **, void (*)(void),
                              void (*)(void), void (*)(void), void *);
typedef int (*memory_function)(int, size_t *, size_t *);
typedef int (*ordinal_function)(int, int *);
typedef int (*fft_function)(int, void *, uint32_t, bool, const void *);
typedef int (*msm_create_function)(int, void **, const void *, size_t);
typedef int (*msm_invoke_function)(int, void *, void *, const void *, size_t, const void *);
typedef int (*msm_destroy_function)(int, void *);
typedef int (*fri_round_trip_function)(int, uint64_t *, uint32_t);
typedef int (*host_copy_function)(int, void *, const void *, size_t);

static main_function original_main;

static void *require_symbol(const char *name) {
    dlerror();
    void *symbol = dlsym(RTLD_DEFAULT, name);
    const char *error = dlerror();
    if (error || !symbol) {
        fprintf(stderr, "CUDA link smoke: missing %s: %s\n", name,
                error ? error : "null symbol");
        exit(90);
    }
    return symbol;
}

static int check_status(const char *operation, int status) {
    if (status) fprintf(stderr, "CUDA link smoke: %s returned %d\n", operation, status);
    return status != 0;
}

struct scalar {
    uint64_t limbs[4];
};

struct affine {
    uint64_t coordinates[12];
    uint8_t infinity;
};

_Static_assert(sizeof(struct scalar) == 32, "BLS12-381 scalar ABI");
_Static_assert(sizeof(struct affine) == 104, "Arkworks affine ABI");

/* BLS12-381 Fr represents one as 2^256 mod r in its Montgomery ABI. */
static const struct scalar scalar_one = {{
    UINT64_C(0x00000001fffffffe), UINT64_C(0x5884b7fa00034802),
    UINT64_C(0x998c4fefecbc4ff5), UINT64_C(0x1824b159acc5056f),
}};

static int check_fft(int device) {
    fft_function fft = (fft_function)require_symbol("ix_kzg_fft");
    struct scalar values[1024] = {0};
    struct scalar expected[1024] = {0};
    values[0] = values[1] = values[17] = scalar_one;
    memcpy(expected, values, sizeof(values));
    if (check_status("KZG forward FFT", fft(device, values, 10, false, &scalar_one))) return 1;
    if (memcmp(values, expected, sizeof(values)) == 0) {
        fputs("CUDA link smoke: KZG forward FFT did not transform its input\n", stderr);
        return 1;
    }
    if (check_status("KZG inverse FFT", fft(device, values, 10, true, &scalar_one))) return 1;
    if (memcmp(values, expected, sizeof(values))) {
        fputs("CUDA link smoke: KZG FFT round trip changed coefficients\n", stderr);
        return 1;
    }
    return 0;
}

static int check_msm(int device) {
    msm_create_function create = (msm_create_function)require_symbol("ix_kzg_msm_create");
    msm_invoke_function invoke = (msm_invoke_function)require_symbol("ix_kzg_msm_invoke");
    msm_destroy_function destroy = (msm_destroy_function)require_symbol("ix_kzg_msm_destroy");
    struct affine points[8] = {0};
    struct scalar scalars[8];
    uint64_t result[18];
    for (size_t i = 0; i < 8; ++i) {
        points[i].infinity = 1;
        scalars[i] = scalar_one;
    }
    memset(result, 0xa5, sizeof(result));
    void *context = NULL;
    if (check_status("KZG MSM creation", create(device, &context, points, 8))) return 1;
    int failed = check_status("KZG MSM", invoke(device, context, result, scalars, 8, NULL));
    failed |= check_status("KZG MSM destruction", destroy(device, context));
    if (failed) return 1;
    /* A Jacobian point is infinity exactly when its six Z limbs are zero. */
    for (size_t i = 12; i < 18; ++i) {
        if (result[i]) {
            fputs("CUDA link smoke: MSM of identity points was not identity\n", stderr);
            return 1;
        }
    }
    return 0;
}

static int check_fri(int device) {
    fri_round_trip_function round_trip =
        (fri_round_trip_function)require_symbol("multi_stark_sppark_borrowed_round_trip");
    host_copy_function copy =
        (host_copy_function)require_symbol("multi_stark_sppark_parallel_memcpy");
    uint64_t values[4096];
    for (size_t i = 0; i < 4096; ++i) values[i] = 17 * i + 3;
    if (check_status("FRI borrowed NTT", round_trip(device, values, 12))) return 1;
    for (size_t i = 0; i < 4096; ++i) {
        if (values[i] != 17 * i + 3) {
            fputs("CUDA link smoke: FRI NTT round trip changed coefficients\n", stderr);
            return 1;
        }
    }

    const size_t bytes = (8u << 20) + 37, prefix = 19, suffix = 29;
    unsigned char *input = malloc(bytes);
    unsigned char *output = malloc(prefix + bytes + suffix);
    if (!input || !output) {
        fputs("CUDA link smoke: host copy allocation failed\n", stderr);
        free(output);
        free(input);
        return 1;
    }
    int failed = 0;
    for (unsigned int pass = 0; pass < 2 && !failed; ++pass) {
        for (size_t i = 0; i < bytes; ++i) input[i] = (unsigned char)(i + pass);
        memset(output, 0xa5, prefix + bytes + suffix);
        failed = check_status("FRI pooled host copy", copy(device, output + prefix, input, bytes));
        if (!failed && memcmp(output + prefix, input, bytes)) failed = 1;
        for (size_t i = 0; i < prefix; ++i) failed |= output[i] != 0xa5;
        for (size_t i = 0; i < suffix; ++i) failed |= output[prefix + bytes + i] != 0xa5;
        if (failed) fputs("CUDA link smoke: FRI host copy or its guard bytes differed\n", stderr);
    }
    free(output);
    free(input);
    return failed;
}

static int checked_main(int argc, char **argv, char **envp) {
    memory_function memory = (memory_function)require_symbol("ix_kzg_memory");
    size_t free_bytes = 0, total_bytes = 0;
    /* This throws and catches a typed C++ exception even without a GPU.
       A shared personality or type-info symbol can silently miss the catch. */
    int status = memory(-1, &free_bytes, &total_bytes);
    if (status != -101) {
        fprintf(stderr, "CUDA link smoke: typed exception returned %d, expected -101\n", status);
        return 91;
    }
    const char *gpu = getenv("IX_CUDA_LINK_SMOKE_GPU");
    if (gpu && strcmp(gpu, "1") == 0) {
        ordinal_function ordinal = (ordinal_function)require_symbol("ix_kzg_device_ordinal");
        int device = -1;
        if (check_status("CUDA device selection", ordinal(0, &device))) return 92;
        if (check_status("CUDA memory query", memory(device, &free_bytes, &total_bytes))) return 92;
        if (total_bytes == 0 || free_bytes > total_bytes) {
            fputs("CUDA link smoke: invalid CUDA memory report\n", stderr);
            return 92;
        }
        if (check_fft(device) || check_msm(device) || check_fri(device)) return 93;
        fputs("CUDA link smoke: typed exception and GPU checks passed\n", stderr);
    } else {
        fputs("CUDA link smoke: typed exception check passed\n", stderr);
    }
    return original_main(argc, argv, envp);
}

/* Interposing startup exercises the runtime in the final Lean executable,
   including its own C++ libraries, before continuing into the requested CLI. */
int __libc_start_main(main_function main, int argc, char **argv,
                      void (*init)(void), void (*fini)(void),
                      void (*rtld_fini)(void), void *stack_end) {
    dlerror();
    start_function start = (start_function)dlsym(RTLD_NEXT, "__libc_start_main");
    const char *error = dlerror();
    if (error || !start) {
        fprintf(stderr, "CUDA link smoke: cannot resolve libc startup: %s\n",
                error ? error : "null symbol");
        _Exit(90);
    }
    original_main = main;
    return start(checked_main, argc, argv, init, fini, rtld_fini, stack_end);
}
