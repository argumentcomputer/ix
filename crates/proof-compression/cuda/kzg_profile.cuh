#pragma once

#include <memory>
#include <vector>
#include <nvtx3/nvToolsExt.h>

#include "kzg_transfer.cuh"

namespace {

class ProfileRange {
  public:
    explicit ProfileRange(const char* name) {
        if (transfer_profiling()) nvtxRangePushA(name);
    }
    ~ProfileRange() {
        if (transfer_profiling()) nvtxRangePop();
    }
    ProfileRange(const ProfileRange&) = delete;
};

class MsmKernelTimings;
thread_local MsmKernelTimings* active_msm_timings = nullptr;

class MsmKernelTimings {
    MsmKernelTimings* previous_;
    std::vector<std::unique_ptr<TimedKernel>> intervals_;
  public:
    MsmKernelTimings() : previous_(active_msm_timings) {
        if (transfer_profiling()) active_msm_timings = this;
    }
    ~MsmKernelTimings() { active_msm_timings = previous_; }
    MsmKernelTimings(const MsmKernelTimings&) = delete;

    TimedKernel* start(cudaStream_t stream) {
        auto timer = std::make_unique<TimedKernel>();
        timer->start(stream);
        intervals_.push_back(std::move(timer));
        return intervals_.back().get();
    }
    void collect(TransferStats& stats) {
        for (const auto& timer : intervals_) timer->collect(stats);
    }
};

TimedKernel* kzg_msm_profile_start(cudaStream_t stream) {
    return active_msm_timings ? active_msm_timings->start(stream) : nullptr;
}

void kzg_msm_profile_end(TimedKernel* timer, cudaStream_t stream) {
    if (timer) timer->end(stream);
}

} // namespace

// sppark's Pippenger header brackets its digit and bucket passes with these.
#define SPPARK_MSM_PROFILE_START(stream) kzg_msm_profile_start(stream)
#define SPPARK_MSM_PROFILE_END(timer, stream) kzg_msm_profile_end(timer, stream)
