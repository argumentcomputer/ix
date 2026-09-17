#pragma once
#include <cuda_runtime.h>
#include <cstddef>
#include <cstdint>
#include <limits>

namespace aiur_trace {
constexpr size_t STAGING_BYTES = 16 * 1024 * 1024;
constexpr size_t MAX_SEED_BYTES = STAGING_BYTES - 8;
constexpr size_t MAX_ROWS = 65537;
constexpr uint32_t ABI_VERSION = 2;

struct Layout {
    size_t width;
    size_t selectors;
    size_t auxiliaries;
};

// Typed seed words are naturally aligned: the host lays wider words out
// first and pads every stride to a multiple of eight.
__device__ __forceinline__ uint64_t load_u8(const uint8_t* p) { return *p; }
__device__ __forceinline__ uint64_t load_u16(const uint8_t* p) {
    return *reinterpret_cast<const uint16_t*>(p);
}
__device__ __forceinline__ uint64_t load_u32(const uint8_t* p) {
    return *reinterpret_cast<const uint32_t*>(p);
}
__device__ __forceinline__ uint64_t load_u64(const uint8_t* p) {
    return *reinterpret_cast<const uint64_t*>(p);
}

using Launch = cudaError_t (*)(const uint8_t*, uint32_t, size_t, size_t,
    Layout, uint64_t*, uint32_t*);

// `seed_stride` is the byte stride of `encoding` for this function; the
// generated entry point resolves it, since typed strides differ per function.
// `output` is blanked before `launch` runs, so a kernel writes only the
// columns of the first `real` rows that are set.
int upload(int device, const uint8_t* seeds, uint32_t encoding,
    size_t seed_stride, size_t real, size_t rows, Layout layout,
    uint64_t* output, Launch launch);
} // namespace aiur_trace
