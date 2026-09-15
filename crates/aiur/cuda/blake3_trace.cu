#include <cuda_runtime.h>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <pthread.h>

namespace {
constexpr size_t WIDTH = 533;
constexpr size_t MAX_ROWS = 65537;

struct Blake3Seed {
    uint64_t multiplicity;
    uint8_t stage;
    uint8_t input[128];
    uint8_t output[32];
    uint8_t padding[7];
};
static_assert(sizeof(Blake3Seed) == 176 && alignof(Blake3Seed) == 8);
static_assert(offsetof(Blake3Seed, multiplicity) == 0);
static_assert(offsetof(Blake3Seed, stage) == 8);
static_assert(offsetof(Blake3Seed, input) == 9);
static_assert(offsetof(Blake3Seed, output) == 137);
static_assert(offsetof(Blake3Seed, padding) == 169);

// Portable slots are shared across devices and retained for the process lifetime.
// Four maximum-size tiles bound pinned memory to just over 44 MiB.
struct PinnedSeedSlot {
    void* data = nullptr;
    bool busy = false;
};
PinnedSeedSlot pinned_seeds[4];
pthread_mutex_t pinned_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t pinned_ready = PTHREAD_COND_INITIALIZER;

class PinnedSeedLease {
    PinnedSeedSlot* slot_ = nullptr;
public:
    PinnedSeedLease() = default;
    PinnedSeedLease(const PinnedSeedLease&) = delete;
    PinnedSeedLease& operator=(const PinnedSeedLease&) = delete;
    ~PinnedSeedLease() {
        if (!slot_) return;
        pthread_mutex_lock(&pinned_mutex);
        slot_->busy = false;
        pthread_cond_signal(&pinned_ready);
        pthread_mutex_unlock(&pinned_mutex);
    }
    cudaError_t acquire() {
        pthread_mutex_lock(&pinned_mutex);
        while (!slot_) {
            for (auto& slot : pinned_seeds) {
                if (!slot.busy) {
                    slot.busy = true;
                    slot_ = &slot;
                    break;
                }
            }
            if (!slot_) pthread_cond_wait(&pinned_ready, &pinned_mutex);
        }
        pthread_mutex_unlock(&pinned_mutex);
        if (slot_->data) return cudaSuccess;
        const cudaError_t status = cudaHostAlloc(&slot_->data,
            MAX_ROWS * sizeof(Blake3Seed), cudaHostAllocPortable);
        if (status != cudaSuccess) slot_->data = nullptr;
        return status;
    }
    void* data() const { return slot_->data; }
};

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

__global__ void generate(const Blake3Seed* seeds, size_t real, size_t rows, uint64_t* output) {
    const size_t r = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
    if (r >= rows) return;
    uint64_t* row = output + r * WIDTH;
    for (size_t col = 0; col < WIDTH; ++col) row[col] = 0;
    if (r >= real) return;
    const Blake3Seed& seed = seeds[r];
    row[0] = seed.stage;
    for (size_t col = 0; col < 128; ++col) row[col + 1] = seed.input[col];
    row[131] = seed.multiplicity;
    uint32_t state[32];
    #pragma unroll
    for (int word = 0; word < 32; ++word) {
        uint32_t value = 0;
        #pragma unroll
        for (int byte = 0; byte < 4; ++byte) value |= uint32_t(seed.input[4 * word + byte]) << (8 * byte);
        state[word] = value;
    }
    Writer writer{row};
    if (seed.stage == 7) {
        row[129] = 1;
        for (int word = 0; word < 8; ++word) writer.word(state[word] ^ state[word + 8]);
    } else {
        row[130] = 1;
        writer.emit(stage_inverse[seed.stage]);
        writer.mix(state, 0,4,8,12,16,17);
        writer.mix(state, 1,5,9,13,18,19);
        writer.mix(state, 2,6,10,14,20,21);
        writer.mix(state, 3,7,11,15,22,23);
        writer.mix(state, 0,5,10,15,24,25);
        writer.mix(state, 1,6,11,12,26,27);
        writer.mix(state, 2,7,8,13,28,29);
        writer.mix(state, 3,4,9,14,30,31);
        for (size_t col = 0; col < 32; ++col) writer.emit(seed.output[col]);
    }
}
}

extern "C" int aiur_blake3_trace(int device, const Blake3Seed* seeds,
    size_t real, size_t rows, uint64_t* output) {
    if (!output || !rows || real > rows || (real && !seeds) || rows > MAX_ROWS)
        return int(cudaErrorInvalidValue);
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess) return int(status);
    PinnedSeedLease staging;
    if (real) status = staging.acquire();
    Blake3Seed* device_seeds = nullptr;
    const size_t bytes = real * sizeof(Blake3Seed);
    if (status == cudaSuccess && real) status = cudaMallocAsync(
        reinterpret_cast<void**>(&device_seeds), bytes, cudaStreamPerThread);
    if (status == cudaSuccess && real) {
        std::memcpy(staging.data(), seeds, bytes);
        status = cudaMemcpyAsync(device_seeds, staging.data(), bytes,
            cudaMemcpyHostToDevice, cudaStreamPerThread);
    }
    if (status == cudaSuccess) {
        generate<<<unsigned((rows + 127) / 128), 128, 0, cudaStreamPerThread>>>(device_seeds, real, rows, output);
        status = cudaGetLastError();
    }
    if (device_seeds) {
        const cudaError_t freed = cudaFreeAsync(device_seeds, cudaStreamPerThread);
        if (status == cudaSuccess) status = freed;
    }
    // Output may move to another thread and the staging slot may be reused.
    // Drain even on launch failure, since the upload may already be in flight.
    const cudaError_t synced = cudaStreamSynchronize(cudaStreamPerThread);
    if (status == cudaSuccess) status = synced;
    return int(status);
}
