#pragma once

#include <ff/batch_inversion.hpp>
#include <polynomial/prefix_op.cuh>

namespace {

struct alignas(32) LookupParameters {
    fr_t beta, gamma;
    uint32_t trace_log, slots, group_size, blocks;
};
static_assert(sizeof(LookupParameters) == 96);

__device__ __forceinline__ void lookup_rational_row(
    fr_t* numerators, fr_t* denominators, fr_t* values, const fr_t* evaluations,
    const QuotientColumn* columns, const QuotientInstruction* nodes, size_t node_count,
    const QuotientLookup* lookups, size_t lookup_count, const uint32_t* arguments,
    LookupParameters parameters, size_t column_stride, size_t row, size_t next,
    fr_t first, fr_t last, fr_t transition
) {
    const size_t groups = (lookup_count + parameters.group_size - 1) / parameters.group_size;
    fr_t zero;
    zero.zero();
    const fr_t one = fr_t::one();
    evaluate_constraint_nodes(values, evaluations, columns, nodes, node_count,
        nullptr, column_stride, row, next, first, last, transition);
    for (size_t group = 0; group < groups; ++group) {
        const size_t start = group * parameters.group_size;
        const size_t remaining = lookup_count - start;
        const size_t count = remaining < parameters.group_size ? remaining : parameters.group_size;
        fr_t messages[8], prefix[9], suffix[9];
        bool active[8];
        prefix[0] = suffix[count] = one;
        for (size_t i = 0; i < count; ++i) {
            const auto& lookup = lookups[start + i];
            fr_t fingerprint = zero;
            for (size_t j = lookup.arg_count; j > 0; --j)
                fingerprint = fingerprint * parameters.gamma
                    + values[size_t(arguments[lookup.arg_start + j - 1]) * blockDim.x];
            const fr_t message = fingerprint + parameters.beta;
            active[i] = !message.is_zero();
            messages[i] = fr_t::csel(message, one, active[i]);
            prefix[i + 1] = prefix[i] * messages[i];
        }
        for (size_t i = count; i > 0; --i)
            suffix[i - 1] = messages[i - 1] * suffix[i];
        fr_t numerator = zero;
        for (size_t i = 0; i < count; ++i) {
            const fr_t contribution = prefix[i] * suffix[i + 1]
                * values[size_t(lookups[start + i].multiplicity) * blockDim.x];
            numerator += fr_t::csel(contribution, zero, active[i]);
        }
        // Replacing zero messages by one and masking their numerator terms
        // preserves the field convention inverse(0) = 0.
        numerators[group] = numerator;
        denominators[group] = prefix[count];
    }
}

__global__ __launch_bounds__(128) void lookup_rationals(
    fr_t* numerators, fr_t* denominators, const fr_t* evaluations,
    const QuotientColumn* columns, const QuotientInstruction* nodes, size_t node_count,
    const QuotientLookup* lookups, size_t lookup_count, const uint32_t* arguments,
    fr_t* scratch, LookupParameters parameters
) {
    const size_t n = size_t(1) << parameters.trace_log;
    const size_t groups = (lookup_count + parameters.group_size - 1) / parameters.group_size;
    fr_t zero;
    zero.zero();
    const fr_t one = fr_t::one();
    fr_t* values = scratch + size_t(blockIdx.x) * parameters.slots * blockDim.x + threadIdx.x;
    for (size_t row = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
         row < n; row += size_t(gridDim.x) * blockDim.x) {
        const size_t next = (row + 1) & (n - 1);
        // Lookup witnesses use Boolean trace selectors, not coset selectors.
        const fr_t first = fr_t::csel(one, zero, row == 0);
        const fr_t last = fr_t::csel(one, zero, row + 1 == n);
        const fr_t transition = fr_t::csel(zero, one, row + 1 == n);
        lookup_rational_row(numerators + row * groups, denominators + row * groups,
            values, evaluations, columns, nodes, node_count, lookups, lookup_count,
            arguments, parameters, n, row, next, first, last, transition);
    }
}

struct ReverseOutput {
    fr_t* values;
    size_t count;
    __device__ __forceinline__ fr_t& operator[](size_t i) const { return values[count - 1 - i]; }
};

struct ReverseInput {
    const fr_t* values;
    size_t count;
    __device__ __forceinline__ fr_t operator[](size_t i) const { return values[count - 1 - i]; }
};

__global__ void lookup_inverse_product(fr_t* inverse, const fr_t* product) {
    // Sppark's reciprocal cooperates with the adjacent lane via shfl_xor.
    // Every lane participates, while only lane zero publishes the result.
    fr_t local[1];
    batch_inversion<fr_t, 1>(local, product);
    if (threadIdx.x == 0) inverse[0] = local[0];
}

__global__ void lookup_contributions(fr_t* numerators, const fr_t* forward,
                                      const fr_t* reverse, const fr_t* inverse, size_t count) {
    for (size_t i = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
         i < count; i += size_t(gridDim.x) * blockDim.x) {
        const fr_t left = i == 0 ? fr_t::one() : forward[i - 1];
        const fr_t right = i + 1 == count ? fr_t::one() : reverse[i + 1];
        numerators[i] *= left * right * inverse[0];
    }
}

__global__ void lookup_exclusive_columns(fr_t* columns, const fr_t* inclusive,
                                         size_t n, size_t groups) {
    for (size_t i = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
         i < n * groups; i += size_t(gridDim.x) * blockDim.x) {
        const size_t column = i / n, row = i % n;
        const size_t index = row * groups + column;
        fr_t value;
        if (index) value = inclusive[index - 1]; else value.zero();
        columns[i] = value;
    }
}

} // namespace

extern "C" int ix_kzg_lookup(
    int device, const LookupParameters* parameters,
    const QuotientColumn* columns, size_t column_count, size_t evaluation_columns,
    const QuotientInstruction* nodes, size_t node_count,
    const QuotientLookup* lookups, size_t lookup_count,
    const uint32_t* args, size_t arg_count, fr_t* const* outputs, fr_t* total
) {
    ProfileRange range("kzg/lookup-resident");
    try {
        if (!parameters || !columns || !lookups || !lookup_count || !outputs || !total)
            return cudaErrorInvalidValue;
        const auto p = *parameters;
        if (p.trace_log < 10 || p.trace_log > 27 || !p.slots || !p.blocks || p.blocks > 256
            || !p.group_size || p.group_size > 8)
            return cudaErrorInvalidValue;
        const size_t n = size_t(1) << p.trace_log;
        const size_t groups = (lookup_count + p.group_size - 1) / p.group_size;
        if (groups > SIZE_MAX / n) return cudaErrorInvalidValue;
        const size_t count = n * groups;
        for (size_t i = 0; i < groups; ++i)
            if (!outputs[i]) return cudaErrorInvalidValue;
        for (size_t i = 0; i < column_count; ++i) {
            const auto& column = columns[i];
            if (!column.input || !column.count || column.count > n
                || (column.slot != UINT32_MAX && column.slot >= evaluation_columns)
                || (column.resident && (column.resident->device != device || column.resident->count != column.count)))
                return cudaErrorInvalidValue;
        }
        const auto& gpu = device_gpu(device);
        auto& stream = gpu[0];
        auto& transfer = transfer_lane(gpu);
        TransferStats stats;
        const auto started = std::chrono::steady_clock::now();
        {
            dev_ptr_t<fr_t> evaluations(evaluation_columns * n, stream);
            dev_ptr_t<fr_t> numerators(count, stream), denominators(count, stream);
            dev_ptr_t<fr_t> forward(count, stream), reverse(count, stream), inverse(1, stream);
            dev_ptr_t<fr_t> scratch(size_t(p.blocks) * 128 * p.slots, stream);
            dev_ptr_t<QuotientColumn> d_columns(column_count, stream);
            dev_ptr_t<QuotientInstruction> d_nodes(node_count, stream);
            dev_ptr_t<QuotientLookup> d_lookups(lookup_count, stream);
            dev_ptr_t<uint32_t> d_args(arg_count, stream);
            auto upload = [&](void* dst, const void* src, size_t bytes) {
                if (bytes) transfer.upload.upload(gpu, stream, dst, src, bytes, stats);
            };
            upload(d_columns, columns, column_count * sizeof(*columns));
            upload(d_nodes, nodes, node_count * sizeof(*nodes));
            upload(d_lookups, lookups, lookup_count * sizeof(*lookups));
            upload(d_args, args, arg_count * sizeof(*args));
            std::vector<std::unique_ptr<TimedKernel>> kernels;
            auto timed = [&](auto operation) {
                auto timer = std::make_unique<TimedKernel>();
                timer->start(stream);
                operation();
                timer->end(stream);
                kernels.push_back(std::move(timer));
            };
            for (size_t i = 0; i < column_count; ++i) {
                const auto& column = columns[i];
                if (column.slot == UINT32_MAX) continue;
                fr_t* destination = &evaluations[size_t(column.slot) * n];
                const size_t bytes = column.count * sizeof(fr_t);
                if (column.resident) {
                    CUDA_OK(cudaMemcpyAsync(destination, column.resident->data, bytes, cudaMemcpyDeviceToDevice, stream));
                    stats.device_copy_bytes += bytes;
                } else upload(destination, column.input, bytes);
                if (column.count < n)
                    CUDA_OK(cudaMemsetAsync(destination + column.count, 0, (n - column.count) * sizeof(fr_t), stream));
                timed([&] { transform(gpu, stream, destination, p.trace_log, false, fr_t::one()); });
            }
            timed([&] {
                lookup_rationals<<<p.blocks, 128, 0, stream>>>(numerators, denominators, evaluations,
                    d_columns, d_nodes, node_count, d_lookups, lookup_count, d_args, scratch, p);
                CUDA_OK(cudaGetLastError());
                prefix_op<Multiply<fr_t>>(forward.data(), denominators.data(), count, stream);
                prefix_op<Multiply<fr_t>>(ReverseOutput{reverse, count}, ReverseInput{denominators, count}, count, stream);
                lookup_inverse_product<<<1, 32, 0, stream>>>(inverse, &forward[count - 1]);
                CUDA_OK(cudaGetLastError());
                lookup_contributions<<<gpu.sm_count() * 4, 256, 0, stream>>>(numerators, forward, reverse, inverse, count);
                CUDA_OK(cudaGetLastError());
                prefix_op<Add<fr_t>>(numerators.data(), count, stream);
                lookup_exclusive_columns<<<gpu.sm_count() * 4, 256, 0, stream>>>(denominators, numerators, n, groups);
                CUDA_OK(cudaGetLastError());
                for (size_t group = 0; group < groups; ++group)
                    transform(gpu, stream, &denominators[group * n], p.trace_log, true, fr_t::one());
            });
            transfer.download.download(gpu, stream, total, &numerators[count - 1], sizeof(fr_t), stats);
            for (size_t group = 0; group < groups; ++group)
                transfer.download.download(gpu, stream, outputs[group], &denominators[group * n], n * sizeof(fr_t), stats);
            stream.sync();
            transfer.upload.finish_upload(stats);
            for (auto& timer : kernels) timer->collect(stats);
        }
        stream.sync();
        stats.call_ms = std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now() - started).count();
        stats.report(device, "lookup-resident", n);
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}
