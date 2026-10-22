#pragma once
#include <goldilocks.cuh>
#include "trace_runtime.cuh"

namespace aiur_trace {
using namespace multi_stark_cuda;

static __device__ __noinline__ uint64_t inverse(uint64_t value) {
    return value == 0 ? 0 : goldilocks_pow(value, GOLDILOCKS_P - 2);
}

__device__ __forceinline__ uint64_t word(uint64_t a, uint64_t b, uint64_t c, uint64_t d) {
    return a | (b << 8) | (c << 16) | (d << 24);
}

struct WordSum { uint64_t low; uint64_t carry; };

__device__ __forceinline__ WordSum add_words(uint64_t a, uint64_t b, uint64_t c = 0) {
    const uint64_t ab = a + b;
    const uint64_t low = ab + c;
    const uint64_t high = uint64_t(ab < a) + uint64_t(low < ab);
    return {low & 0xffffffffULL, (low >> 32) + (high << 32)};
}
} // namespace aiur_trace
