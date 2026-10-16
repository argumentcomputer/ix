#pragma once

namespace {

constexpr size_t SRS_UPLOAD_POINTS = size_t(1) << 18;

uint32_t srs_msm_window(size_t count) {
    count = (count + 31) & ~size_t(31);
    uint32_t bits = 0;
    for (size_t n = count + count / 2; n >>= 1;) ++bits;
    return count <= 192 ? 10 : std::max(10u, std::min(bits - 8, 18u));
}

struct SrsPoints {
    int device;
    size_t count;
    dev_ptr_t<affine_t> points;
    SrsPoints(const gpu_t& gpu, size_t count)
        : device(gpu.cid()), count(count), points(count, gpu) {}
};

struct SrsMsmWorkspace {
    int device;
    uint32_t window;
    msm_impl msm;
    SrsMsmWorkspace(const gpu_t& gpu, size_t count)
        : device(gpu.cid()), window(srs_msm_window(count)),
          msm(nullptr, count, sizeof(affine_t), gpu.id()) {}
};

} // namespace

extern "C" int ix_kzg_srs_plan(int device, size_t count, uint32_t* window,
                                          size_t* persistent, size_t* temporary) {
    try {
        if (!count || count > (size_t(1) << 24) || !window || !persistent || !temporary)
            return cudaErrorInvalidValue;
        const auto& gpu = device_gpu(device);
        *window = srs_msm_window(count);
        const size_t windows = (fr_t::bit_length() - 1) / *window + 1;
        const size_t row = size_t(1) << (*window - 1);
        *persistent = (windows * row + gpu.sm_count() * BATCH_ADD_BLOCK_SIZE / WARP_SZ)
                    * sizeof(bucket_t::mem_t) + windows * row * sizeof(uint32_t);
        uint32_t lg = 0;
        for (size_t n = count + count / 2; n >>= 1;) ++lg;
        const size_t batch = std::max(size_t(1), (size_t(1) << (std::max(lg, *window) - *window)) >> 6);
        const size_t stride = ((count + batch - 1) / batch + 31) & ~size_t(31);
        // Device scalar pointers avoid sppark's point/scalar upload buffers.
        // One full scalar buffer covers host uploads or resident normalization.
        *temporary = stride * (2 * sizeof(uint2) + windows * sizeof(uint32_t))
                   + ((count + 31) & ~size_t(31)) * sizeof(fr_t);
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}

extern "C" int ix_kzg_srs_upload(int device, const ArkAffine* input,
                                            size_t count, void** output) {
    ProfileRange range("kzg/srs-cache-upload");
    try {
        if (!input || !output || !count || count > (size_t(1) << 24))
            return cudaErrorInvalidValue;
        const auto& gpu = device_gpu(device);
        auto result = std::make_unique<SrsPoints>(gpu, count);
        {
            dev_ptr_t<ArkAffine> staging(std::min(count, SRS_UPLOAD_POINTS), gpu);
            auto& transfer = transfer_lane(gpu);
            TransferStats stats;
            std::vector<TimedKernel> conversions((count + SRS_UPLOAD_POINTS - 1) / SRS_UPLOAD_POINTS);
            const auto started = std::chrono::steady_clock::now();
            for (size_t offset = 0; offset < count; offset += SRS_UPLOAD_POINTS) {
                const size_t length = std::min(count - offset, SRS_UPLOAD_POINTS);
                transfer.upload.upload(gpu, gpu, staging, input + offset,
                                       length * sizeof(ArkAffine), stats);
                auto& conversion = conversions[offset / SRS_UPLOAD_POINTS];
                conversion.start(gpu);
                unpack_affine<<<gpu.sm_count() * 4, 256, 0, gpu>>>(
                    &result->points[offset], staging, length);
                CUDA_OK(cudaGetLastError());
                conversion.end(gpu);
            }
            gpu.sync();
            transfer.upload.finish_upload(stats);
            for (auto& conversion : conversions) conversion.collect(stats);
            stats.call_ms = std::chrono::duration<double, std::milli>(
                std::chrono::steady_clock::now() - started).count();
            stats.report(device, "srs-cache-upload", count);
        }
        gpu.sync();
        *output = result.release();
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}

extern "C" int ix_kzg_srs_destroy(int device, void* pointer) {
    try {
        const auto& gpu = device_gpu(device);
        auto* points = static_cast<SrsPoints*>(pointer);
        if (!points || points->device != device) return cudaErrorInvalidValue;
        gpu.sync();
        delete points;
        gpu.sync();
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}

extern "C" int ix_kzg_srs_workspace_create(int device, size_t count, void** output) {
    try {
        if (!output || !count || count > (size_t(1) << 24)) return cudaErrorInvalidValue;
        *output = new SrsMsmWorkspace(device_gpu(device), count);
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}

extern "C" int ix_kzg_srs_workspace_destroy(int device, void* pointer) {
    try {
        const auto& gpu = device_gpu(device);
        auto* workspace = static_cast<SrsMsmWorkspace*>(pointer);
        if (!workspace || workspace->device != device) return cudaErrorInvalidValue;
        delete workspace;
        gpu.sync();
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}

extern "C" int ix_kzg_srs_msm(int device, void* workspace_pointer,
    const void* points_pointer, size_t point_offset, point_t* output,
    const fr_t* host_scalars, const void* polynomial, size_t scalar_offset,
    size_t count, const fr_t* normalization) {
    ProfileRange range("kzg/msm-cached-points");
    try {
        if (!workspace_pointer || !points_pointer || !output || !count
            || count > (size_t(1) << 24) || bool(host_scalars) == bool(polynomial))
            return cudaErrorInvalidValue;
        const auto& gpu = device_gpu(device);
        auto& workspace = *static_cast<SrsMsmWorkspace*>(workspace_pointer);
        const auto& points = *static_cast<const SrsPoints*>(points_pointer);
        if (workspace.device != device || workspace.window != srs_msm_window(count)
            || points.device != device || point_offset > points.count || count > points.count - point_offset)
            return cudaErrorInvalidValue;
        const auto* coefficients = static_cast<const ResidentPolynomial*>(polynomial);
        if (coefficients && (coefficients->device != device || scalar_offset > coefficients->count
            || count > coefficients->count - scalar_offset)) return cudaErrorInvalidValue;
        {
            dev_ptr_t<fr_t> temporary(host_scalars || normalization ? count : 0, gpu);
            fr_t* input = temporary;
            if (coefficients) input = const_cast<fr_t*>(&coefficients->data[scalar_offset]);
            TransferStats transfers;
            if (host_scalars) {
                auto& transfer = transfer_lane(gpu);
                transfer.upload.upload(gpu, gpu, temporary, host_scalars, count * sizeof(fr_t), transfers);
                gpu.sync();
                transfer.upload.finish_upload(transfers);
                transfers.report(device, "msm-scalars", count);
            }
            MsmKernelTimings kernels;
            TransferStats compute;
            const auto started = std::chrono::steady_clock::now();
            if (normalization) {
                auto* timer = kzg_msm_profile_start(gpu);
                scale_values<<<gpu.sm_count() * 4, 256, 0, gpu>>>(temporary, input, count, *normalization);
                CUDA_OK(cudaGetLastError());
                kzg_msm_profile_end(timer, gpu);
                gpu.sync();
                input = temporary;
            }
            // sppark retains pointer values between invocations. Rebind both
            // views while the device lease keeps their allocations alive.
            dev_ptr_t<affine_t> point_view(const_cast<affine_t*>(&points.points[point_offset]), count);
            dev_ptr_t<fr_t> scalar_view(input, count);
            const int code = msm_result(workspace.msm.invoke(*output, point_view, count, scalar_view, true));
            if (code) return code;
            kernels.collect(compute);
            compute.call_ms = std::chrono::duration<double, std::milli>(
                std::chrono::steady_clock::now() - started).count();
            compute.report(device, "msm-compute", count);
        }
        gpu.sync();
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}
