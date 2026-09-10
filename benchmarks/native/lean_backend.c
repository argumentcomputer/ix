#include "common.h"
#include <lean/lean.h>

extern lean_object *bench_lean_reverse(lean_object *input);
extern lean_object *initialize_LeanReverse(uint8_t builtin);
extern void lean_initialize_runtime_module(void);
static lean_object *scalars[INPUT_COUNT][MAX_N];

void backend_init(void) {
    lean_initialize_runtime_module();
    lean_object *result = initialize_LeanReverse(1);
    bench_need(lean_io_result_is_ok(result), "Lean initialization failed");
    lean_dec_ref(result);
    lean_io_mark_end_initialization();
    for (uint64_t id = 0; id < INPUT_COUNT; ++id)
        for (uint64_t i = 0; i < bench_inputs[id].n; ++i)
            scalars[id][i] = lean_uint64_to_nat(bench_inputs[id].values[i]);
}
void backend_finish(void) {
    for (uint64_t id = 0; id < INPUT_COUNT; ++id)
        for (uint64_t i = 0; i < bench_inputs[id].n; ++i) lean_dec(scalars[id][i]);
}
BenchItem backend_make(const BenchInput *input, uint64_t capacity) {
    (void)capacity;
    uint64_t id = input - bench_inputs;
    lean_object *list = lean_box(0);
    for (uint64_t i = input->n; i != 0; --i) {
        lean_object *node = lean_alloc_ctor(1, 2, 0), *value = scalars[id][i - 1];
        lean_inc(value);
        lean_ctor_set(node, 0, value); lean_ctor_set(node, 1, list); list = node;
    }
    return (BenchItem){list, 0};
}
BenchItem backend_reverse(BenchItem input, uint64_t n) {
    (void)n;
    return (BenchItem){bench_lean_reverse(input.owner), 0};
}
uint64_t backend_digest(BenchItem output) {
    lean_object *list = output.owner;
    uint64_t hash = UINT64_C(14695981039346656037);
    while (!lean_is_scalar(list)) {
        hash = (hash ^ lean_uint64_of_nat(lean_ctor_get(list, 0))) * UINT64_C(1099511628211);
        list = lean_ctor_get(list, 1);
    }
    return hash;
}
void backend_release(BenchItem output) { lean_dec((lean_object *)output.owner); }
uint64_t backend_capacity_count(const BenchInput *input) { (void)input; return 1; }
void backend_verify(const BenchInput *input, uint64_t capacity, int emit) {
    BenchItem owned = backend_make(input, capacity);
    /* Integer addresses are diagnostic weak observations, never RC owners. */
    uintptr_t addresses[MAX_N];
    lean_object *cursor = owned.owner;
    for (uint64_t i = 0; i < input->n; ++i) {
        bench_need(!lean_is_scalar(cursor) && lean_is_exclusive(cursor), "Lean input spine is shared");
        addresses[i] = (uintptr_t)cursor;
        cursor = lean_ctor_get(cursor, 1);
    }
    bench_need(lean_is_scalar(cursor) && lean_unbox(cursor) == 0, "Lean input nil invalid");
    cursor = NULL;
    BenchItem result = backend_reverse(owned, input->n); owned = (BenchItem){0, 0};
    cursor = result.owner;
    uint64_t values[MAX_N], reused = 0;
    for (uint64_t i = 0; i < input->n; ++i) {
        bench_need(!lean_is_scalar(cursor) && lean_is_exclusive(cursor), "Lean output spine is shared or short");
        values[i] = lean_uint64_of_nat(lean_ctor_get(cursor, 0));
        bench_need(values[i] == input->values[input->n - i - 1], "Lean reversal value mismatch");
        reused += (uintptr_t)cursor == addresses[input->n - i - 1];
        cursor = lean_ctor_get(cursor, 1);
    }
    bench_need(lean_is_scalar(cursor) && lean_unbox(cursor) == 0 && reused == input->n, "Lean reuse or nil mismatch");
    uint64_t hash = backend_digest(result);
    bench_need(hash == input->digest, "Lean digest mismatch");
    cursor = NULL;
    backend_release(result); result = (BenchItem){0, 0};
    if (emit) {
        printf("{\"kind\":\"case\",\"id\":%" PRIu64 ",\"capacity\":null,\"values\":", input->n * 9 + input->pattern);
        bench_values(values, input->n);
        printf(",\"digest\":%" PRIu64 ",\"exclusive_input_cons\":%" PRIu64
            ",\"exclusive_output_cons\":%" PRIu64 ",\"reused_cons\":%" PRIu64 ",\"released\":true}\n",
            hash, input->n, input->n, reused);
    }
}
