#include <cuda_runtime.h>
#include <cstddef>
#include <cstdint>

namespace {
constexpr size_t WIDTH = 533;
constexpr size_t SEED_WORDS = 162;
__device__ __constant__ uint64_t stage_inverse[7] = {15811494916641072275ULL, 3074457344902430720ULL, 3689348813882916864ULL, 4611686017353646080ULL, 6148914689804861440ULL, 9223372034707292160ULL, 18446744069414584320ULL};

struct Writer {
    uint64_t* row;
    size_t column = 132;
    __device__ void emit(uint64_t value) { row[column++] = value; }
    __device__ void word(uint32_t value) {
        #pragma unroll
        for (int byte = 0; byte < 4; ++byte) emit((value >> (8 * byte)) & 255);
    }
    __device__ uint32_t add3(uint32_t a, uint32_t b, uint32_t c) {
        const uint64_t sum = uint64_t(a) + b + c;
        word(uint32_t(sum));
        emit((sum >> 32) == 0 ? 2 : 0); emit(0);
        return uint32_t(sum);
    }
    __device__ uint32_t add2(uint32_t a, uint32_t b) {
        const uint64_t sum = uint64_t(a) + b;
        word(uint32_t(sum)); emit(sum >> 32);
        return uint32_t(sum);
    }
    __device__ uint32_t xor_rotate(uint32_t a, uint32_t b, int rotate) {
        const uint32_t value = a ^ b;
        const int split = rotate == 12 ? 4 : 7;
        #pragma unroll
        for (int byte = 0; byte < 4; ++byte) {
            const uint32_t v = (value >> (8 * byte)) & 255;
            emit(v >> split); emit((v << (8 - split)) & 255);
        }
        return (value >> rotate) | (value << (32 - rotate));
    }
    __device__ void mix(uint32_t* s, int a, int b, int c, int d, int x, int y) {
        s[a] = add3(s[a], s[b], s[x]);
        uint32_t v = s[d] ^ s[a]; word(v); s[d] = (v >> 16) | (v << 16);
        s[c] = add2(s[c], s[d]); s[b] = xor_rotate(s[b], s[c], 12);
        s[a] = add3(s[a], s[b], s[y]);
        v = s[d] ^ s[a]; word(v); s[d] = (v >> 8) | (v << 24);
        s[c] = add2(s[c], s[d]); s[b] = xor_rotate(s[b], s[c], 7);
    }
};

__global__ void generate(const uint64_t* seeds, size_t real, size_t rows, uint64_t* output) {
    const size_t r = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
    if (r >= rows) return;
    uint64_t* row = output + r * WIDTH;
    for (size_t col = 0; col < WIDTH; ++col) row[col] = 0;
    if (r >= real) return;
    const uint64_t* seed = seeds + r * SEED_WORDS;
    for (size_t col = 0; col < 129; ++col) row[col] = seed[col];
    row[131] = seed[161];
    uint32_t state[32];
    #pragma unroll
    for (int word = 0; word < 32; ++word) {
        uint32_t value = 0;
        #pragma unroll
        for (int byte = 0; byte < 4; ++byte) value |= uint32_t(seed[1 + 4 * word + byte]) << (8 * byte);
        state[word] = value;
    }
    Writer writer{row};
    if (seed[0] == 7) {
        row[129] = 1;
        for (int word = 0; word < 8; ++word) writer.word(state[word] ^ state[word + 8]);
    } else {
        row[130] = 1;
        writer.emit(stage_inverse[seed[0]]);
        writer.mix(state, 0,4,8,12,16,17);
        writer.mix(state, 1,5,9,13,18,19);
        writer.mix(state, 2,6,10,14,20,21);
        writer.mix(state, 3,7,11,15,22,23);
        writer.mix(state, 0,5,10,15,24,25);
        writer.mix(state, 1,6,11,12,26,27);
        writer.mix(state, 2,7,8,13,28,29);
        writer.mix(state, 3,4,9,14,30,31);
        for (size_t col = 129; col < 161; ++col) writer.emit(seed[col]);
    }
}
}

extern "C" int aiur_blake3_trace(int device, const uint64_t* seeds,
    size_t real, size_t rows, uint64_t* output) {
    if (!output || !rows || real > rows || (real && !seeds) || rows > 65537)
        return int(cudaErrorInvalidValue);
    cudaError_t status = cudaSetDevice(device);
    uint64_t* device_seeds = nullptr;
    const size_t bytes = real * SEED_WORDS * sizeof(uint64_t);
    if (status == cudaSuccess && real) status = cudaMallocAsync(
        reinterpret_cast<void**>(&device_seeds), bytes, cudaStreamPerThread);
    if (status == cudaSuccess && real) status = cudaMemcpyAsync(device_seeds, seeds, bytes,
        cudaMemcpyHostToDevice, cudaStreamPerThread);
    if (status == cudaSuccess) {
        generate<<<unsigned((rows + 127) / 128), 128, 0, cudaStreamPerThread>>>(device_seeds, real, rows, output);
        status = cudaGetLastError();
    }
    // The caller owns output; it may move to another thread immediately.
    if (status == cudaSuccess) status = cudaStreamSynchronize(cudaStreamPerThread);
    if (device_seeds) cudaFreeAsync(device_seeds, cudaStreamPerThread);
    return int(status);
}
