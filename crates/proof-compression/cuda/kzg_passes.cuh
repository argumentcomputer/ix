#pragma once

namespace {

struct alignas(32) ConstraintPass {
    fr_t weight;
    const QuotientColumn* columns;
    size_t column_count, evaluated;
    const QuotientInstruction* nodes;
    size_t node_count;
    const uint32_t* roots;
    size_t root_count;
    const QuotientLookup* lookups;
    size_t lookup_count;
    const uint32_t* args;
    size_t arg_count, slots, group;
};
static_assert(sizeof(ConstraintPass) == 160);
static_assert(offsetof(ConstraintPass, group) == 128);

struct PassShape {
    size_t columns = 0, evaluated = 0, nodes = 0, roots = 0, lookups = 0, args = 0, slots = 1;

    PassShape(int device, const ConstraintPass* passes, size_t count, size_t rows) {
        if (!passes || !count) CUDA_OK(cudaErrorInvalidValue);
        for (size_t i = 0; i < count; ++i) {
            const auto& p = passes[i];
            if (!p.columns || !p.column_count || !p.slots || p.evaluated > p.column_count
                || (p.node_count && !p.nodes) || (p.root_count && !p.roots)
                || (p.lookup_count && !p.lookups) || (p.arg_count && !p.args))
                CUDA_OK(cudaErrorInvalidValue);
            for (size_t j = 0; j < p.column_count; ++j) {
                const auto& c = p.columns[j];
                if (!c.input || !c.count || c.count > rows
                    || (c.slot != UINT32_MAX && c.slot >= p.evaluated)
                    || (c.resident && (c.resident->device != device || c.resident->count != c.count)))
                    CUDA_OK(cudaErrorInvalidValue);
            }
            columns = std::max(columns, p.column_count);
            evaluated = std::max(evaluated, p.evaluated);
            nodes = std::max(nodes, p.node_count);
            roots = std::max(roots, p.root_count);
            lookups = std::max(lookups, p.lookup_count);
            args = std::max(args, p.arg_count);
            slots = std::max(slots, p.slots);
        }
        if (evaluated > SIZE_MAX / rows / sizeof(fr_t)) CUDA_OK(cudaErrorInvalidValue);
    }
};

struct PassBuffers {
    dev_ptr_t<fr_t> evaluations, scratch;
    dev_ptr_t<QuotientColumn> columns;
    dev_ptr_t<QuotientInstruction> nodes;
    dev_ptr_t<uint32_t> roots, args;
    dev_ptr_t<QuotientLookup> lookups;
    std::vector<std::unique_ptr<TimedKernel>> kernels;

    PassBuffers(const PassShape& shape, size_t n, size_t blocks, const stream_t& stream)
        : evaluations(shape.evaluated * n, stream), scratch(blocks * 128 * shape.slots, stream),
          columns(shape.columns, stream), nodes(shape.nodes, stream), roots(shape.roots, stream),
          args(shape.args, stream), lookups(shape.lookups, stream) {}

    template<class Operation> void timed(const stream_t& stream, Operation operation) {
        auto timer = std::make_unique<TimedKernel>();
        timer->start(stream);
        operation();
        timer->end(stream);
        kernels.push_back(std::move(timer));
    }

    void load(const gpu_t& gpu, stream_t& stream, const ConstraintPass& pass,
              uint32_t log_n, fr_t shift, TransferStats& stats) {
        const size_t n = size_t(1) << log_n;
        auto& transfer = transfer_lane(gpu);
        auto upload = [&](void* to, const void* from, size_t bytes) {
            if (bytes) transfer.upload.upload(gpu, stream, to, from, bytes, stats);
        };
        upload(columns, pass.columns, pass.column_count * sizeof(QuotientColumn));
        upload(nodes, pass.nodes, pass.node_count * sizeof(QuotientInstruction));
        upload(roots, pass.roots, pass.root_count * sizeof(uint32_t));
        upload(lookups, pass.lookups, pass.lookup_count * sizeof(QuotientLookup));
        upload(args, pass.args, pass.arg_count * sizeof(uint32_t));
        for (size_t i = 0; i < pass.column_count; ++i) {
            const auto& column = pass.columns[i];
            if (column.slot == UINT32_MAX) continue;
            fr_t* destination = evaluations.data() + size_t(column.slot) * n;
            const size_t bytes = column.count * sizeof(fr_t);
            if (column.resident) {
                CUDA_OK(cudaMemcpyAsync(destination, column.resident->data, bytes, cudaMemcpyDeviceToDevice, stream));
                stats.device_copy_bytes += bytes;
            } else {
                upload(destination, column.input, bytes);
            }
            if (column.count < n)
                CUDA_OK(cudaMemsetAsync(destination + column.count, 0, (n - column.count) * sizeof(fr_t), stream));
            timed(stream, [&] { transform(gpu, stream, destination, log_n, false, shift); });
        }
    }

    void collect(TransferStats& stats) {
        for (auto& timer : kernels) timer->collect(stats);
    }
};

__global__ void lookup_pass_row_totals(fr_t* totals, const fr_t* contributions, size_t n, size_t groups) {
    for (size_t row = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
         row < n; row += size_t(gridDim.x) * blockDim.x) {
        fr_t sum;
        sum.zero();
        for (size_t group = 0; group < groups; ++group) sum += contributions[group * n + row];
        totals[row] = sum;
    }
}

__global__ void lookup_pass_accumulators(fr_t* contributions, const fr_t* inclusive_rows,
                                        size_t n, size_t groups) {
    for (size_t row = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
         row < n; row += size_t(gridDim.x) * blockDim.x) {
        fr_t prefix;
        if (row) prefix = inclusive_rows[row - 1]; else prefix.zero();
        // Read a contribution before replacing it with its row/group prefix.
        for (size_t group = 0; group < groups; ++group) {
            const size_t offset = group * n + row;
            const fr_t value = contributions[offset];
            contributions[offset] = prefix;
            prefix += value;
        }
    }
}

__global__ __launch_bounds__(128) void quotient_pass_sweep(
    fr_t* output, const fr_t* evaluations, const fr_t* first_selector,
    const QuotientColumn* columns, const QuotientInstruction* nodes, size_t node_count,
    const uint32_t* roots, const QuotientLookup* lookups, size_t lookup_count,
    const uint32_t* args, const fr_t* publics, fr_t* scratch, QuotientParameters parameters,
    size_t groups, size_t group, fr_t weight, fr_t shift, fr_t inverse_vanishing, uint32_t coset
) {
    const size_t n = size_t(1) << parameters.trace_log;
    const size_t ratio = size_t(1) << (parameters.quotient_log - parameters.trace_log);
    const size_t stride = size_t(gridDim.x) * blockDim.x;
    size_t row = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
    fr_t point = shift * (parameters.generator ^ uint32_t(row));
    const fr_t step = parameters.generator ^ uint32_t(stride);
    fr_t* values = scratch + size_t(blockIdx.x) * parameters.slots * blockDim.x + threadIdx.x;
    for (; row < n; row += stride, point *= step) {
        const size_t next = (row + 1) & (n - 1);
        const fr_t first = first_selector[row];
        const fr_t last = parameters.generator * first_selector[next];
        evaluate_constraint_nodes(values, evaluations, columns, nodes, node_count, publics,
            n, row, next, first, last, point - parameters.generator_inverse);
        const fr_t value = group == SIZE_MAX ? values[size_t(roots[0]) * blockDim.x]
            : quotient_lookup_group(values, evaluations, columns, lookups, lookup_count, args,
                                   publics, parameters, groups, group, n, row, next, last);
        output[row * ratio + coset] += weight * value * inverse_vanishing;
    }
}

} // namespace

extern "C" int ix_kzg_lookup_passes(
    int device, const LookupParameters* parameters, const ConstraintPass* passes,
    size_t pass_count, fr_t* const* outputs, fr_t* total
) {
    ProfileRange range("kzg/lookup-passes");
    try {
        if (!parameters || !outputs || !total || !passes || !pass_count) return cudaErrorInvalidValue;
        const auto p = *parameters;
        if (p.trace_log < 10 || p.trace_log > 27 || !p.blocks || p.blocks > 256
            || !p.group_size || p.group_size > 8) return cudaErrorInvalidValue;
        const size_t n = size_t(1) << p.trace_log;
        if (pass_count > SIZE_MAX / n / sizeof(fr_t)) return cudaErrorInvalidValue;
        const PassShape shape(device, passes, pass_count, n);
        for (size_t i = 0; i < pass_count; ++i) {
            if (!outputs[i] || passes[i].group != i || !passes[i].lookup_count
                || passes[i].lookup_count > p.group_size || passes[i].root_count) return cudaErrorInvalidValue;
        }
        const auto& gpu = device_gpu(device);
        auto& stream = gpu[0];
        auto& transfer = transfer_lane(gpu);
        TransferStats stats;
        const auto started = std::chrono::steady_clock::now();
        {
            PassBuffers buffers(shape, n, p.blocks, stream);
            dev_ptr_t<fr_t> contributions(n * pass_count, stream), denominators(n, stream);
            dev_ptr_t<fr_t> forward(n, stream), reverse(n, stream), inverse(1, stream);
            for (size_t group = 0; group < pass_count; ++group) {
                const auto& pass = passes[group];
                auto local = p;
                local.slots = uint32_t(pass.slots);
                buffers.load(gpu, stream, pass, p.trace_log, fr_t::one(), stats);
                fr_t* values = contributions.data() + group * n;
                buffers.timed(stream, [&] {
                    lookup_rationals<<<p.blocks, 128, 0, stream>>>(values, denominators, buffers.evaluations,
                        buffers.columns, buffers.nodes, pass.node_count, buffers.lookups, pass.lookup_count,
                        buffers.args, buffers.scratch, local);
                    CUDA_OK(cudaGetLastError());
                    prefix_op<Multiply<fr_t>>(forward.data(), denominators.data(), n, stream);
                    prefix_op<Multiply<fr_t>>(ReverseOutput{reverse, n}, ReverseInput{denominators, n}, n, stream);
                    lookup_inverse_product<<<1, 32, 0, stream>>>(inverse, forward.data() + n - 1);
                    CUDA_OK(cudaGetLastError());
                    lookup_contributions<<<gpu.sm_count() * 4, 256, 0, stream>>>(values, forward, reverse, inverse, n);
                    CUDA_OK(cudaGetLastError());
                });
            }
            buffers.timed(stream, [&] {
                lookup_pass_row_totals<<<gpu.sm_count() * 4, 256, 0, stream>>>(denominators, contributions, n, pass_count);
                CUDA_OK(cudaGetLastError());
                prefix_op<Add<fr_t>>(denominators.data(), n, stream);
                lookup_pass_accumulators<<<gpu.sm_count() * 4, 256, 0, stream>>>(contributions, denominators, n, pass_count);
                CUDA_OK(cudaGetLastError());
            });
            transfer.download.download(gpu, stream, total, denominators.data() + n - 1, sizeof(fr_t), stats);
            for (size_t group = 0; group < pass_count; ++group) {
                fr_t* values = contributions.data() + group * n;
                buffers.timed(stream, [&] { transform(gpu, stream, values, p.trace_log, true, fr_t::one()); });
                transfer.download.download(gpu, stream, outputs[group], values, n * sizeof(fr_t), stats);
            }
            stream.sync();
            transfer.upload.finish_upload(stats);
            buffers.collect(stats);
        }
        stream.sync();
        stats.call_ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - started).count();
        stats.report(device, "lookup-passes", n);
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}

extern "C" int ix_kzg_quotient_passes(
    int device, const QuotientParameters* parameters, const ConstraintPass* passes, size_t pass_count,
    const fr_t* publics, size_t public_count, const fr_t* shifts, const fr_t* inverse_vanishing,
    fr_t* const* outputs
) {
    ProfileRange range("kzg/quotient-passes");
    try {
        if (!parameters || !publics || public_count < 4 || !shifts || !inverse_vanishing || !outputs)
            return cudaErrorInvalidValue;
        const auto p = *parameters;
        if (p.trace_log < 10 || p.trace_log > 27 || p.quotient_log < p.trace_log || p.quotient_log > 28
            || !p.blocks || p.blocks > 256 || !p.group_size || p.group_size > 8)
            return cudaErrorInvalidValue;
        const size_t n = size_t(1) << p.trace_log, ratio = size_t(1) << (p.quotient_log - p.trace_log);
        const PassShape shape(device, passes, pass_count, n);
        const size_t columns = passes[0].column_count;
        if (p.stage2_start >= columns) return cudaErrorInvalidValue;
        const size_t groups = columns - p.stage2_start;
        for (size_t i = 0; i < ratio; ++i) if (!outputs[i]) return cudaErrorInvalidValue;
        for (size_t i = 0; i < pass_count; ++i) {
            const auto& pass = passes[i];
            if (pass.column_count != columns || pass.lookup_count > p.group_size
                || (pass.group == SIZE_MAX ? (pass.root_count != 1 || pass.lookup_count != 0)
                                          : (pass.group >= groups || pass.root_count != 0)))
                return cudaErrorInvalidValue;
        }
        const auto& gpu = device_gpu(device);
        auto& stream = gpu[0];
        auto& transfer = transfer_lane(gpu);
        TransferStats stats;
        const auto started = std::chrono::steady_clock::now();
        {
            PassBuffers buffers(shape, n, p.blocks, stream);
            dev_ptr_t<fr_t> first(n, stream), quotient(n * ratio, stream), d_publics(public_count, stream);
            transfer.upload.upload(gpu, stream, d_publics.data(), publics, public_count * sizeof(fr_t), stats);
            CUDA_OK(cudaMemsetAsync(quotient.data(), 0, n * ratio * sizeof(fr_t), stream));
            for (size_t coset = 0; coset < ratio; ++coset) {
                buffers.timed(stream, [&] {
                    quotient_ones<<<gpu.sm_count() * 4, 256, 0, stream>>>(first, n);
                    CUDA_OK(cudaGetLastError());
                    transform(gpu, stream, first, p.trace_log, false, shifts[coset]);
                });
                for (size_t i = 0; i < pass_count; ++i) {
                    const auto& pass = passes[i];
                    auto local = p;
                    local.slots = uint32_t(pass.slots);
                    buffers.load(gpu, stream, pass, p.trace_log, shifts[coset], stats);
                    buffers.timed(stream, [&] {
                        quotient_pass_sweep<<<p.blocks, 128, 0, stream>>>(quotient, buffers.evaluations, first,
                            buffers.columns, buffers.nodes, pass.node_count, buffers.roots, buffers.lookups,
                            pass.lookup_count, buffers.args, d_publics, buffers.scratch, local, groups,
                            pass.group, pass.weight, shifts[coset], inverse_vanishing[coset], uint32_t(coset));
                        CUDA_OK(cudaGetLastError());
                    });
                }
            }
            buffers.timed(stream, [&] { transform(gpu, stream, quotient, p.quotient_log, true, p.quotient_shift_inverse); });
            for (size_t i = 0; i < ratio; ++i)
                transfer.download.download(gpu, stream, outputs[i], quotient.data() + i * n, n * sizeof(fr_t), stats);
            stream.sync();
            transfer.upload.finish_upload(stats);
            buffers.collect(stats);
        }
        stream.sync();
        stats.call_ms = std::chrono::duration<double, std::milli>(std::chrono::steady_clock::now() - started).count();
        stats.report(device, "quotient-passes", n * ratio);
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}
