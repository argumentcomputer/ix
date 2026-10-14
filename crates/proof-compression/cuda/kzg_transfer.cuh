#pragma once

#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <mutex>

namespace {

bool transfer_profiling() {
    static const bool enabled = [] {
        const char* value = std::getenv("IX_KZG_CUDA_PROFILE");
        return value && std::strcmp(value, "1") == 0;
    }();
    return enabled;
}

struct TransferStats {
    double upload_ms = 0, download_ms = 0, kernel_ms = 0, host_copy_ms = 0, call_ms = 0;
    size_t upload_bytes = 0, download_bytes = 0, device_copy_bytes = 0;

    void report(int device, const char* operation, size_t count) const {
        if (!transfer_profiling()) return;
        std::fprintf(stderr,
            "KZG CUDA profile device=%d operation=%s elements=%zu "
            "upload_ms=%.3f kernel_ms=%.3f download_ms=%.3f host_copy_ms=%.3f "
            "upload_bytes=%zu download_bytes=%zu device_copy_bytes=%zu call_ms=%.3f\n",
            device, operation, count, upload_ms, kernel_ms, download_ms,
            host_copy_ms, upload_bytes, download_bytes, device_copy_bytes, call_ms);
    }
};

class TimedKernel {
    cudaEvent_t start_ = nullptr, end_ = nullptr;
  public:
    TimedKernel() {
        if (transfer_profiling()) {
            CUDA_OK(cudaEventCreate(&start_));
            try { CUDA_OK(cudaEventCreate(&end_)); }
            catch (...) { cudaEventDestroy(start_); throw; }
        }
    }
    ~TimedKernel() {
        if (start_) cudaEventDestroy(start_);
        if (end_) cudaEventDestroy(end_);
    }
    void start(cudaStream_t stream) {
        if (start_) CUDA_OK(cudaEventRecord(start_, stream));
    }
    void end(cudaStream_t stream) {
        if (end_) CUDA_OK(cudaEventRecord(end_, stream));
    }
    void collect(TransferStats& stats) {
        if (!end_) return;
        CUDA_OK(cudaEventSynchronize(end_));
        float elapsed = 0;
        CUDA_OK(cudaEventElapsedTime(&elapsed, start_, end_));
        stats.kernel_ms += elapsed;
    }
};

// Each device lease owns two FFT lanes. A ring bounds pinned memory regardless
// of polynomial size and overlaps the next host copy with the preceding DMA.
class TransferRing {
    static constexpr size_t CHUNK = size_t(16) << 20;
    static constexpr size_t RING = 4;
    unsigned char* memory_ = nullptr;
    std::array<cudaEvent_t, RING> ready_{};
    std::array<cudaEvent_t, RING> start_{};
    std::array<bool, RING> pending_{};

    void wait(size_t slot, double& milliseconds) {
        if (!pending_[slot]) return;
        CUDA_OK(cudaEventSynchronize(ready_[slot]));
        if (start_[slot]) {
            float elapsed = 0;
            CUDA_OK(cudaEventElapsedTime(&elapsed, start_[slot], ready_[slot]));
            milliseconds += elapsed;
        }
        pending_[slot] = false;
    }

    void copy_host(const gpu_t& gpu, void* dst, const void* src, size_t bytes,
                   TransferStats& stats) {
        const auto started = std::chrono::steady_clock::now();
        constexpr size_t GRAIN = size_t(4) << 20;
        const size_t parts = (bytes + GRAIN - 1) / GRAIN;
        gpu.par_map(parts, 1, [&](size_t part) {
            const size_t offset = part * GRAIN;
            std::memcpy(static_cast<unsigned char*>(dst) + offset,
                        static_cast<const unsigned char*>(src) + offset,
                        std::min(GRAIN, bytes - offset));
        });
        stats.host_copy_ms += std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now() - started).count();
    }

    void enqueue(size_t slot, void* dst, const void* src, size_t bytes,
                 cudaMemcpyKind kind, cudaStream_t stream) {
        if (start_[slot]) CUDA_OK(cudaEventRecord(start_[slot], stream));
        CUDA_OK(cudaMemcpyAsync(dst, src, bytes, kind, stream));
        CUDA_OK(cudaEventRecord(ready_[slot], stream));
        pending_[slot] = true;
    }

  public:
    TransferRing() {
        try {
            CUDA_OK(cudaMallocHost(reinterpret_cast<void**>(&memory_), RING * CHUNK));
            for (size_t i = 0; i < RING; ++i) {
                CUDA_OK(cudaEventCreateWithFlags(&ready_[i], transfer_profiling()
                    ? cudaEventDefault : cudaEventDisableTiming));
                if (transfer_profiling()) CUDA_OK(cudaEventCreate(&start_[i]));
            }
        } catch (...) { release(); throw; }
    }
    TransferRing(const TransferRing&) = delete;
    ~TransferRing() { release(); }

    void release() {
        // An exception may leave a DMA using the pinned memory in flight.
        for (size_t i = 0; i < RING; ++i) {
            if (ready_[i]) {
                if (pending_[i]) cudaEventSynchronize(ready_[i]);
                cudaEventDestroy(ready_[i]);
            }
            if (start_[i]) cudaEventDestroy(start_[i]);
        }
        if (memory_) cudaFreeHost(memory_);
    }

    void upload(const gpu_t& gpu, cudaStream_t stream, void* dst,
                const void* src, size_t bytes, TransferStats& stats) {
        for (size_t offset = 0, i = 0; offset < bytes; offset += CHUNK, ++i) {
            const size_t slot = i % RING;
            wait(slot, stats.upload_ms);
            auto* buffer = memory_ + slot * CHUNK;
            const size_t count = std::min(CHUNK, bytes - offset);
            copy_host(gpu, buffer, static_cast<const unsigned char*>(src) + offset,
                      count, stats);
            enqueue(slot, static_cast<unsigned char*>(dst) + offset, buffer, count,
                    cudaMemcpyHostToDevice, stream);
        }
        stats.upload_bytes += bytes;
    }

    void finish_upload(TransferStats& stats) {
        for (size_t i = 0; i < RING; ++i) wait(i, stats.upload_ms);
    }

    void download(const gpu_t& gpu, cudaStream_t stream, void* dst,
                  const void* src, size_t bytes, TransferStats& stats) {
        const size_t chunks = (bytes + CHUNK - 1) / CHUNK;
        for (size_t i = 0; i < chunks + RING; ++i) {
            const size_t slot = i % RING;
            auto* buffer = memory_ + slot * CHUNK;
            if (i >= RING && i - RING < chunks) {
                wait(slot, stats.download_ms);
                const size_t offset = (i - RING) * CHUNK;
                copy_host(gpu, static_cast<unsigned char*>(dst) + offset, buffer,
                          std::min(CHUNK, bytes - offset), stats);
            }
            if (i < chunks) {
                const size_t offset = i * CHUNK;
                enqueue(slot, buffer, static_cast<const unsigned char*>(src) + offset,
                        std::min(CHUNK, bytes - offset), cudaMemcpyDeviceToHost, stream);
            }
        }
        stats.download_bytes += bytes;
    }
};

struct TransferLane {
    TransferRing upload, download;
};

TransferLane& transfer_lane(const gpu_t& gpu, size_t lane = 0) {
    static std::mutex mutex;
    static std::map<int, std::array<std::unique_ptr<TransferLane>, 2>> lanes;
    std::lock_guard<std::mutex> lock(mutex);
    auto& entry = lanes[gpu.cid()][lane];
    if (!entry) entry = std::make_unique<TransferLane>();
    return *entry;
}

} // namespace
