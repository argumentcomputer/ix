#include "trace_runtime.cuh"
#include <cstring>
#include <pthread.h>

namespace aiur_trace {
namespace {
struct Slot { uint8_t* data = nullptr; bool busy = false; };
Slot slots[4];
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t ready = PTHREAD_COND_INITIALIZER;

class Lease {
    Slot* slot_ = nullptr;
public:
    Lease() = default;
    Lease(const Lease&) = delete;
    Lease& operator=(const Lease&) = delete;
    ~Lease() {
        if (!slot_) return;
        pthread_mutex_lock(&mutex);
        slot_->busy = false;
        pthread_cond_signal(&ready);
        pthread_mutex_unlock(&mutex);
    }
    cudaError_t acquire() {
        pthread_mutex_lock(&mutex);
        while (!slot_) {
            for (auto& slot : slots) if (!slot.busy) {
                slot.busy = true;
                slot_ = &slot;
                break;
            }
            if (!slot_) pthread_cond_wait(&ready, &mutex);
        }
        pthread_mutex_unlock(&mutex);
        if (slot_->data) return cudaSuccess;
        const auto status = cudaHostAlloc(reinterpret_cast<void**>(&slot_->data),
            STAGING_BYTES, cudaHostAllocPortable);
        if (status != cudaSuccess) slot_->data = nullptr;
        return status;
    }
    uint8_t* data() const { return slot_->data; }
    uint32_t* error() const { return reinterpret_cast<uint32_t*>(data() + MAX_SEED_BYTES); }
};
} // namespace

int upload(int device, const uint8_t* seeds, uint32_t encoding,
    size_t words, size_t real, size_t rows, Layout layout,
    uint64_t* output, Launch launch) {
    const size_t seed_stride = stride(words, encoding);
    if (!output || !launch || !rows || rows > MAX_ROWS || real > rows
        || !seed_stride || seed_stride > MAX_SEED_BYTES
        || real > MAX_SEED_BYTES / seed_stride || (real && !seeds)
        || !layout.width || layout.width > std::numeric_limits<size_t>::max() / rows / 8)
        return int(cudaErrorInvalidValue);
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess) return int(status);
    if (!real) {
        status = cudaMemsetAsync(output, 0, rows * layout.width * 8, cudaStreamPerThread);
        const auto synced = cudaStreamSynchronize(cudaStreamPerThread);
        return int(status == cudaSuccess ? synced : status);
    }
    // A lease bounds both pinned memory and live device seed allocations.
    Lease lease;
    status = lease.acquire();
    if (status != cudaSuccess) return int(status);
    *lease.error() = 0;
    const size_t bytes = real * seed_stride;
    uint8_t* device_seeds = nullptr;
    status = cudaMallocAsync(reinterpret_cast<void**>(&device_seeds), bytes + 8, cudaStreamPerThread);
    uint32_t* device_error = nullptr;
    if (status == cudaSuccess) {
        device_error = reinterpret_cast<uint32_t*>(device_seeds + bytes);
        std::memcpy(lease.data(), seeds, bytes);
        status = cudaMemcpyAsync(device_seeds, lease.data(), bytes, cudaMemcpyHostToDevice, cudaStreamPerThread);
    }
    if (status == cudaSuccess) status = cudaMemsetAsync(device_error, 0, 4, cudaStreamPerThread);
    if (status == cudaSuccess) status = launch(device_seeds, encoding, real, rows, layout, output, device_error);
    if (status == cudaSuccess) status = cudaMemcpyAsync(lease.error(), device_error, 4, cudaMemcpyDeviceToHost, cudaStreamPerThread);
    if (device_seeds) {
        const auto freed = cudaFreeAsync(device_seeds, cudaStreamPerThread);
        if (status == cudaSuccess) status = freed;
    }
    // The output and staging lease may cross threads immediately after return.
    const auto synced = cudaStreamSynchronize(cudaStreamPerThread);
    if (status == cudaSuccess) status = synced;
    if (status != cudaSuccess) return int(status);
    return *lease.error() ? 10000 + int(*lease.error()) : 0;
}
} // namespace aiur_trace
