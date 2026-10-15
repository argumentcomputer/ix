#define _GNU_SOURCE
#include <dlfcn.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int (*main_function)(int, char **, char **);
typedef int (*start_function)(main_function, int, char **, void (*)(void),
                              void (*)(void), void (*)(void), void *);
typedef int (*memory_function)(int, size_t *, size_t *);
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

static int check_private_runtime(void *entry) {
    Dl_info info;
    if (!dladdr(entry, &info) || !info.dli_fname ||
        !strstr(info.dli_fname, "/libmulti_stark_cuda.so")) {
        fputs("CUDA link smoke: Goldilocks backend is not in libmulti_stark_cuda.so\n", stderr);
        return 1;
    }
    void *backend = dlopen(info.dli_fname, RTLD_NOW | RTLD_NOLOAD);
    if (!backend) {
        fprintf(stderr, "CUDA link smoke: cannot open backend: %s\n", dlerror());
        return 1;
    }
    /* C++ definitions must stay local even when the executable exports
       Lean's own exception and typeinfo symbols. */
    int leaked = dlsym(backend, "_ZNSt13runtime_errorC1EPKc") != NULL ||
                 dlsym(backend, "__gxx_personality_v0") != NULL ||
                 dlsym(backend, "_Unwind_RaiseException") != NULL;
    dlclose(backend);
    if (leaked) fputs("CUDA link smoke: backend exports its C++ runtime\n", stderr);
    return leaked;
}

static int check_status(const char *operation, int status) {
    if (status) fprintf(stderr, "CUDA link smoke: %s returned %d\n", operation, status);
    return status != 0;
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
    /* KZG proving belongs to the separate worker; the Lean executable keeps
       only the Goldilocks backend for its aggregate prover. */
    dlerror();
    if (dlsym(RTLD_DEFAULT, "ix_kzg_memory")) {
        fputs("CUDA link smoke: KZG proving code is linked into the Lean executable\n", stderr);
        return 91;
    }
    dlerror();
    memory_function memory =
        (memory_function)require_symbol("multi_stark_cuda_memory_info");
    fri_round_trip_function round_trip =
        (fri_round_trip_function)require_symbol("multi_stark_sppark_borrowed_round_trip");
    host_copy_function copy =
        (host_copy_function)require_symbol("multi_stark_sppark_parallel_memcpy");
    if (check_private_runtime((void *)round_trip)) return 91;
    /* Invalid arguments return cudaErrorInvalidValue before touching a GPU. */
    if (round_trip(-1, NULL, 0) != 1 || copy(-1, NULL, NULL, 1) != 1) {
        fputs("CUDA link smoke: invalid Goldilocks arguments were not rejected\n", stderr);
        return 91;
    }
    const char *gpu = getenv("IX_CUDA_LINK_SMOKE_GPU");
    if (gpu && strcmp(gpu, "1") == 0) {
        size_t free_bytes = 0, total_bytes = 0;
        if (check_status("CUDA memory query", memory(0, &free_bytes, &total_bytes))) return 92;
        if (total_bytes == 0 || free_bytes > total_bytes) {
            fputs("CUDA link smoke: invalid CUDA memory report\n", stderr);
            return 92;
        }
        if (check_fri(0)) return 93;
        fputs("CUDA link smoke: Goldilocks link and GPU checks passed\n", stderr);
    } else {
        fputs("CUDA link smoke: Goldilocks link checks passed\n", stderr);
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
