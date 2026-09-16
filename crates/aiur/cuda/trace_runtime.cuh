#pragma once
#include <cuda_runtime.h>
#include <cstddef>
#include <cstdint>
#include <limits>

namespace aiur_trace {
constexpr size_t STAGING_BYTES = 16 * 1024 * 1024;
constexpr size_t MAX_SEED_BYTES = STAGING_BYTES - 8;
constexpr size_t MAX_ROWS = 65537;
constexpr uint32_t ABI_VERSION = 1;

struct Layout {
    size_t width;
    size_t selectors;
    size_t auxiliaries;
};

template<bool Packed> struct Seed {
    const uint8_t* data;
    __device__ __forceinline__ uint64_t word(size_t index) const {
        if constexpr (Packed) {
            return index == 0 ? *reinterpret_cast<const uint64_t*>(data)
                              : uint64_t(data[7 + index]);
        } else {
            return reinterpret_cast<const uint64_t*>(data)[index];
        }
    }
};

inline size_t stride(size_t words, uint32_t encoding) {
    if (!words || words > (std::numeric_limits<size_t>::max() - 14) / 8)
        return 0;
    if (encoding == 0) return words * 8;
    if (encoding == 1) return ((words + 14) / 8) * 8;
    return 0;
}

using Launch = cudaError_t (*)(const uint8_t*, uint32_t, size_t, size_t,
    Layout, uint64_t*, uint32_t*);

int upload(int device, const uint8_t* seeds, uint32_t encoding,
    size_t words, size_t real, size_t rows, Layout layout,
    uint64_t* output, Launch launch);
} // namespace aiur_trace
