#include "trace_runtime.cuh"
#include <algorithm>
#include <cstring>
#include <pthread.h>

namespace aiur_trace {
namespace {
// One staging lease is a ring of pinned chunk buffers, each with the event
// of its last transfer, so a span's host copy into pinned memory overlaps
// the DMA of the chunks before it and the blanking of the output. The
// kernel still runs once over the whole span: a per-chunk launch would
// leave most of the device idle.
constexpr size_t RING = 8;
constexpr size_t CHUNK_BYTES = (MAX_SEED_BYTES / RING) & ~size_t(7);

struct Slot {
    uint8_t* data = nullptr;
    cudaEvent_t events[RING] = {};
    bool busy = false;
};
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
        auto status = cudaHostAlloc(reinterpret_cast<void**>(&slot_->data),
            STAGING_BYTES, cudaHostAllocPortable);
        if (status != cudaSuccess) {
            slot_->data = nullptr;
            return status;
        }
        for (auto& event : slot_->events) {
            status = cudaEventCreateWithFlags(&event, cudaEventDisableTiming);
            if (status != cudaSuccess) return status;
        }
        return cudaSuccess;
    }
    uint8_t* chunk(size_t index) const { return slot_->data + index * CHUNK_BYTES; }
    cudaEvent_t event(size_t index) const { return slot_->events[index]; }
    uint32_t* error() const { return reinterpret_cast<uint32_t*>(slot_->data + MAX_SEED_BYTES); }
};

// Streams `bytes` from pageable `source` to `destination` on the calling
// thread's stream through the lease's ring, so each host copy overlaps the
// transfers before it. `chunk` counts the lease's transfers so far and is
// carried across calls: a ring slot is reused only once the transfer it
// last staged has landed, whichever span that transfer belonged to. The
// last chunks are still in flight on return.
cudaError_t stage_copy(const Lease& lease, uint8_t* destination,
    const uint8_t* source, size_t bytes, size_t& chunk) {
    cudaError_t status = cudaSuccess;
    size_t offset = 0;
    for (; status == cudaSuccess && offset < bytes; ++chunk) {
        const size_t index = chunk % RING;
        if (chunk >= RING) status = cudaEventSynchronize(lease.event(index));
        const size_t length = std::min(CHUNK_BYTES, bytes - offset);
        if (status == cudaSuccess) {
            std::memcpy(lease.chunk(index), source + offset, length);
            status = cudaMemcpyAsync(destination + offset, lease.chunk(index), length,
                cudaMemcpyHostToDevice, cudaStreamPerThread);
        }
        if (status == cudaSuccess) status = cudaEventRecord(lease.event(index), cudaStreamPerThread);
        offset += length;
    }
    return status;
}

bool on_device(const void* pointer, cudaError_t& status) {
    cudaPointerAttributes attributes{};
    status = cudaPointerGetAttributes(&attributes, pointer);
    return status == cudaSuccess && attributes.type == cudaMemoryTypeDevice;
}

// Rows from seeds already resident on the device: no staging, no seed
// allocation, one error word for the launch.
int generate_resident(const uint8_t* seeds, uint32_t encoding, size_t real,
    size_t rows, Layout layout, uint64_t* output, Launch launch) {
    uint32_t* device_error = nullptr;
    cudaError_t status = cudaMallocAsync(reinterpret_cast<void**>(&device_error), 4, cudaStreamPerThread);
    if (status == cudaSuccess) status = cudaMemsetAsync(device_error, 0, 4, cudaStreamPerThread);
    if (status == cudaSuccess)
        status = cudaMemsetAsync(output, 0, rows * layout.width * 8, cudaStreamPerThread);
    if (status == cudaSuccess)
        status = launch(seeds, encoding, real, rows, layout, output, device_error);
    uint32_t error = 0;
    if (status == cudaSuccess)
        status = cudaMemcpyAsync(&error, device_error, 4, cudaMemcpyDeviceToHost, cudaStreamPerThread);
    if (device_error) {
        const auto freed = cudaFreeAsync(device_error, cudaStreamPerThread);
        if (status == cudaSuccess) status = freed;
    }
    // The output may cross threads immediately after return.
    const auto synced = cudaStreamSynchronize(cudaStreamPerThread);
    if (status == cudaSuccess) status = synced;
    if (status != cudaSuccess) return int(status);
    return error ? 10000 + int(error) : 0;
}
} // namespace

int upload(int device, const uint8_t* seeds, uint32_t encoding,
    size_t seed_stride, size_t real, size_t rows, Layout layout,
    uint64_t* output, Launch launch) {
    if (!output || !launch || !rows || rows > MAX_ROWS || real > rows
        || !seed_stride
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
    if (on_device(seeds, status))
        return generate_resident(seeds, encoding, real, rows, layout, output, launch);
    if (status != cudaSuccess) return int(status);
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
        status = cudaMemsetAsync(device_error, 0, 4, cudaStreamPerThread);
    }
    // Kernels write only the columns a row sets. Blanking the tile here with
    // coalesced stores, while the host is still copying seeds, is a third
    // cheaper than a zero pass over each row inside the kernel.
    if (status == cudaSuccess)
        status = cudaMemsetAsync(output, 0, rows * layout.width * 8, cudaStreamPerThread);
    size_t chunk = 0;
    if (status == cudaSuccess) status = stage_copy(lease, device_seeds, seeds, bytes, chunk);
    if (status == cudaSuccess)
        status = launch(device_seeds, encoding, real, rows, layout, output, device_error);
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

extern "C" int aiur_trace_seed_cache_upload(int device, const uint8_t* const* spans,
    const size_t* lengths, size_t count, size_t total, uint8_t** cached) {
    if (!cached) return int(cudaErrorInvalidValue);
    *cached = nullptr;
    if (!spans || !lengths || !count || !total) return int(cudaErrorInvalidValue);
    size_t sum = 0;
    for (size_t i = 0; i < count; ++i) {
        if (!spans[i] || !lengths[i] || lengths[i] > total - sum)
            return int(cudaErrorInvalidValue);
        sum += lengths[i];
    }
    if (sum != total) return int(cudaErrorInvalidValue);
    cudaError_t status = cudaSetDevice(device);
    if (status != cudaSuccess) return int(status);
    uint8_t* buffer = nullptr;
    status = cudaMalloc(reinterpret_cast<void**>(&buffer), total);
    if (status != cudaSuccess) {
        // Out of memory is an answer, not a sticky fault.
        cudaGetLastError();
        return int(status);
    }
    Lease lease;
    status = lease.acquire();
    size_t offset = 0, chunk = 0;
    for (size_t i = 0; status == cudaSuccess && i < count; ++i) {
        status = stage_copy(lease, buffer + offset, spans[i], lengths[i], chunk);
        offset += lengths[i];
    }
    // The lease's chunks are reused as soon as it is released.
    const auto synced = cudaStreamSynchronize(cudaStreamPerThread);
    if (status == cudaSuccess) status = synced;
    if (status != cudaSuccess) {
        cudaFree(buffer);
        return int(status);
    }
    *cached = buffer;
    return 0;
}

extern "C" int aiur_trace_seed_cache_free(int device, uint8_t* cached) {
    if (!cached) return 0;
    cudaError_t status = cudaSetDevice(device);
    if (status == cudaSuccess) status = cudaFree(cached);
    return int(status);
}
// Memory-table rows: `[multiplicity, 1, pointer, values...]` from seeds of
// `[multiplicity, pointer, values...]`, one thread per row. Every table row
// is real, zero multiplicities included; the padding rows keep the blank
// the uploader wrote.
namespace {
__global__ void memory_rows(const uint8_t* __restrict__ seeds, size_t real,
    size_t, Layout layout, uint64_t* __restrict__ output, uint32_t*) {
    const size_t r = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
    if (r >= real) return;
    uint64_t* row = output + r * layout.width;
    const size_t values = layout.width - 3;
    const uint64_t* seed =
        reinterpret_cast<const uint64_t*>(seeds + r * (values + 2) * 8);
    row[0] = seed[0];
    row[1] = 1;
    row[2] = seed[1];
    for (size_t i = 0; i < values; ++i) row[3 + i] = seed[2 + i];
}

cudaError_t launch_memory(const uint8_t* seeds, uint32_t, size_t real,
    size_t rows, Layout layout, uint64_t* output, uint32_t* error) {
    memory_rows<<<unsigned((real + 127) / 128), 128, 0, cudaStreamPerThread>>>(
        seeds, real, rows, layout, output, error);
    return cudaGetLastError();
}
} // namespace

extern "C" int aiur_trace_memory(int device, const uint8_t* seeds,
    size_t values, size_t real, size_t rows, uint64_t* output) {
    if (values > std::numeric_limits<size_t>::max() / 8 - 3)
        return int(cudaErrorInvalidValue);
    return upload(device, seeds, 0, (values + 2) * 8, real, rows,
        {values + 3, 0, 0}, output, launch_memory);
}
} // namespace aiur_trace
