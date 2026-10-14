#pragma once

namespace {

struct alignas(32) QuotientInstruction {
    fr_t value;
    uint32_t a, b, op, out;
};

struct QuotientLookup {
    uint32_t multiplicity, arg_start, arg_count;
};

struct alignas(32) QuotientColumn {
    const fr_t* input;
    const ResidentPolynomial* resident;
    size_t count;
    uint64_t padding;
    fr_t constant;
    uint32_t slot, reserved;
};

struct alignas(32) QuotientParameters {
    fr_t alpha, generator, generator_inverse, delta, quotient_shift_inverse;
    uint32_t trace_log, quotient_log, slots, stage2_start, group_size, blocks;
};

static_assert(sizeof(QuotientInstruction) == 64);
static_assert(sizeof(QuotientLookup) == 12);
static_assert(sizeof(QuotientColumn) == 96);
static_assert(offsetof(QuotientColumn, constant) == 32);
static_assert(sizeof(QuotientParameters) == 192);

__global__ void quotient_ones(fr_t* values, size_t count) {
    for (size_t i = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
         i < count; i += size_t(gridDim.x) * blockDim.x)
        values[i] = fr_t::one();
}

__device__ __forceinline__ fr_t quotient_column(
    const fr_t* evaluations, const QuotientColumn* columns,
    size_t n, uint32_t column, size_t row
) {
    const auto& descriptor = columns[column];
    return descriptor.slot == UINT32_MAX ? descriptor.constant
        : evaluations[size_t(descriptor.slot) * n + row];
}

__device__ __forceinline__ void evaluate_constraint_nodes(
    fr_t* values, const fr_t* evaluations, const QuotientColumn* columns,
    const QuotientInstruction* nodes, size_t node_count, const fr_t* publics,
    size_t n, size_t row, size_t next, const fr_t& first, const fr_t& last,
    const fr_t& transition
) {
        for (size_t i = 0; i < node_count; ++i) {
            const auto& node = nodes[i];
            fr_t value;
            switch (node.op) {
                case 0: value = node.value; break;
                case 1: value = quotient_column(evaluations, columns, n, node.a, node.b ? next : row); break;
                case 2: value = publics[node.a]; break;
                case 3: value = first; break;
                case 4: value = last; break;
                case 5: value = transition; break;
                case 6: value = values[size_t(node.a) * blockDim.x] + values[size_t(node.b) * blockDim.x]; break;
                case 7: value = values[size_t(node.a) * blockDim.x] - values[size_t(node.b) * blockDim.x]; break;
                case 8: value = values[size_t(node.a) * blockDim.x] * values[size_t(node.b) * blockDim.x]; break;
                case 9: value = -values[size_t(node.a) * blockDim.x]; break;
                default: value.zero(); break;
            }
            values[size_t(node.out) * blockDim.x] = value;
        }
}

__device__ __forceinline__ fr_t quotient_lookup_group(
    fr_t* values, const fr_t* evaluations, const QuotientColumn* columns,
    const QuotientLookup* lookups, size_t lookup_count, const uint32_t* args,
    const fr_t* publics, QuotientParameters parameters, size_t groups, size_t group,
    size_t n, size_t row, size_t next, fr_t last
) {
    const fr_t target = group + 1 == groups
        ? quotient_column(evaluations, columns, n, parameters.stage2_start, next) + last * parameters.delta
        : quotient_column(evaluations, columns, n, parameters.stage2_start + uint32_t(group + 1), row);
    fr_t constraint = target - quotient_column(evaluations, columns, n, parameters.stage2_start + uint32_t(group), row);
    fr_t messages[8], prefix[9], suffix[9];
    prefix[0] = suffix[lookup_count] = fr_t::one();
    for (size_t i = 0; i < lookup_count; ++i) {
        const auto& lookup = lookups[i];
        fr_t fingerprint;
        fingerprint.zero();
        for (size_t j = lookup.arg_count; j > 0; --j)
            fingerprint = fingerprint * publics[1] + values[size_t(args[lookup.arg_start + j - 1]) * blockDim.x];
        messages[i] = fingerprint + publics[0];
        prefix[i + 1] = prefix[i] * messages[i];
    }
    for (size_t i = lookup_count; i > 0; --i) suffix[i - 1] = messages[i - 1] * suffix[i];
    constraint *= prefix[lookup_count];
    for (size_t i = 0; i < lookup_count; ++i)
        constraint -= prefix[i] * suffix[i + 1] * values[size_t(lookups[i].multiplicity) * blockDim.x];
    return constraint;
}

__device__ __forceinline__ fr_t quotient_row(
    fr_t* values, const fr_t* evaluations, const QuotientColumn* columns,
    const QuotientInstruction* nodes, size_t node_count, const uint32_t* roots,
    size_t root_count, const QuotientLookup* lookups, size_t lookup_count,
    const uint32_t* arguments, const fr_t* publics, QuotientParameters parameters,
    size_t n, size_t row, size_t next, const fr_t& first, const fr_t& last,
    const fr_t& transition
) {
    evaluate_constraint_nodes(values, evaluations, columns, nodes, node_count,
        publics, n, row, next, first, last, transition);
    fr_t accumulator;
    accumulator.zero();
    for (size_t i = 0; i < root_count; ++i)
        accumulator = accumulator * parameters.alpha + values[size_t(roots[i]) * blockDim.x];
    const size_t groups = lookup_count ? (lookup_count + parameters.group_size - 1) / parameters.group_size : 1;
    for (size_t group = 0; group < groups; ++group) {
        const size_t start = group * parameters.group_size;
        const size_t remaining = lookup_count - start;
        const size_t count = remaining < parameters.group_size ? remaining : parameters.group_size;
        const fr_t constraint = quotient_lookup_group(values, evaluations, columns,
            count ? lookups + start : nullptr, count, arguments, publics, parameters,
            groups, group, n, row, next, last);
        accumulator = accumulator * parameters.alpha + constraint;
    }
    return accumulator;
}

__global__ __launch_bounds__(128) void quotient_sweep(
    fr_t* output, const fr_t* evaluations, const fr_t* first_selector,
    const QuotientColumn* columns, const QuotientInstruction* nodes, size_t node_count,
    const uint32_t* roots, size_t root_count, const QuotientLookup* lookups, size_t lookup_count,
    const uint32_t* arguments, const fr_t* publics, fr_t* scratch,
    QuotientParameters parameters, fr_t shift, fr_t inverse_vanishing, uint32_t coset
) {
    const size_t n = size_t(1) << parameters.trace_log;
    const size_t ratio = size_t(1) << (parameters.quotient_log - parameters.trace_log);
    const size_t stride = size_t(gridDim.x) * blockDim.x;
    size_t row = size_t(blockIdx.x) * blockDim.x + threadIdx.x;
    fr_t point = shift * (parameters.generator ^ uint32_t(row));
    const fr_t point_step = parameters.generator ^ uint32_t(stride);
    fr_t* values = scratch + size_t(blockIdx.x) * parameters.slots * blockDim.x + threadIdx.x;
    for (; row < n; row += stride, point *= point_step) {
        const size_t next = (row + 1) & (n - 1);
        const fr_t first = first_selector[row];
        // These selectors are unnormalized: L_last(X) = g * L_first(gX).
        const fr_t last = parameters.generator * first_selector[next];
        const fr_t transition = point - parameters.generator_inverse;
        output[row * ratio + coset] = quotient_row(values, evaluations, columns,
            nodes, node_count, roots, root_count, lookups, lookup_count, arguments,
            publics, parameters, n, row, next, first, last, transition) * inverse_vanishing;
    }
}

} // namespace

extern "C" int ix_kzg_quotient(
    int device, const QuotientParameters* parameters,
    const QuotientColumn* columns, size_t column_count, size_t evaluation_columns,
    const QuotientInstruction* nodes, size_t node_count,
    const uint32_t* roots, size_t root_count, const QuotientLookup* lookups, size_t lookup_count,
    const uint32_t* args, size_t arg_count, const fr_t* publics, size_t public_count,
    const fr_t* coset_shifts, const fr_t* inverse_vanishing, fr_t* const* outputs
) {
    ProfileRange range("kzg/quotient-resident");
    try {
        if (!parameters || !columns || !publics || !outputs || !coset_shifts || !inverse_vanishing)
            return cudaErrorInvalidValue;
        const auto p = *parameters;
        if (p.trace_log < 10 || p.trace_log > p.quotient_log || p.quotient_log > MAX_LG_DOMAIN_SIZE
            || !p.slots || !p.blocks || p.blocks > 256 || !p.group_size || p.group_size > 8
            || p.stage2_start >= column_count || public_count < 4)
            return cudaErrorInvalidValue;
        const size_t n = size_t(1) << p.trace_log;
        const size_t ratio = size_t(1) << (p.quotient_log - p.trace_log);
        for (size_t i = 0; i < ratio; ++i)
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
            dev_ptr_t<fr_t> first(n, stream), quotient(n * ratio, stream);
            dev_ptr_t<fr_t> scratch(size_t(p.blocks) * 128 * p.slots, stream);
            dev_ptr_t<QuotientColumn> d_columns(column_count, stream);
            dev_ptr_t<QuotientInstruction> d_nodes(node_count, stream);
            dev_ptr_t<uint32_t> d_roots(root_count, stream), d_args(arg_count, stream);
            dev_ptr_t<QuotientLookup> d_lookups(lookup_count, stream);
            dev_ptr_t<fr_t> d_publics(public_count, stream);
            auto upload = [&](void* dst, const void* src, size_t bytes) {
                if (bytes) transfer.upload.upload(gpu, stream, dst, src, bytes, stats);
            };
            upload(d_columns, columns, column_count * sizeof(*columns));
            upload(d_nodes, nodes, node_count * sizeof(*nodes));
            upload(d_roots, roots, root_count * sizeof(*roots));
            upload(d_lookups, lookups, lookup_count * sizeof(*lookups));
            upload(d_args, args, arg_count * sizeof(*args));
            upload(d_publics, publics, public_count * sizeof(*publics));
            std::vector<std::unique_ptr<TimedKernel>> kernels;
            auto timed = [&](auto operation) {
                auto timer = std::make_unique<TimedKernel>();
                timer->start(stream);
                operation();
                timer->end(stream);
                kernels.push_back(std::move(timer));
            };
            for (size_t coset = 0; coset < ratio; ++coset) {
                for (size_t i = 0; i < column_count; ++i) {
                    const auto& column = columns[i];
                    if (column.slot == UINT32_MAX) continue;
                    fr_t* destination = &evaluations[size_t(column.slot) * n];
                    const size_t bytes = column.count * sizeof(fr_t);
                    if (column.resident) {
                        CUDA_OK(cudaMemcpyAsync(destination, column.resident->data, bytes, cudaMemcpyDeviceToDevice, stream));
                        stats.device_copy_bytes += bytes;
                    } else {
                        upload(destination, column.input, bytes);
                    }
                    if (column.count < n)
                        CUDA_OK(cudaMemsetAsync(destination + column.count, 0, (n - column.count) * sizeof(fr_t), stream));
                    timed([&] { transform(gpu, stream, destination, p.trace_log, false, coset_shifts[coset]); });
                }
                timed([&] {
                    quotient_ones<<<gpu.sm_count() * 4, 256, 0, stream>>>(first, n);
                    CUDA_OK(cudaGetLastError());
                    transform(gpu, stream, first, p.trace_log, false, coset_shifts[coset]);
                    quotient_sweep<<<p.blocks, 128, 0, stream>>>(quotient, evaluations, first,
                        d_columns, d_nodes, node_count, d_roots, root_count, d_lookups, lookup_count,
                        d_args, d_publics, scratch, p, coset_shifts[coset], inverse_vanishing[coset], uint32_t(coset));
                    CUDA_OK(cudaGetLastError());
                });
            }
            timed([&] { transform(gpu, stream, quotient, p.quotient_log, true, p.quotient_shift_inverse); });
            for (size_t k = 0; k < ratio; ++k)
                transfer.download.download(gpu, stream, outputs[k], &quotient[k * n], n * sizeof(fr_t), stats);
            stream.sync();
            transfer.upload.finish_upload(stats);
            for (auto& timer : kernels) timer->collect(stats);
        }
        // Complete cudaFreeAsync before a later lease performs admission.
        stream.sync();
        stats.call_ms = std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now() - started).count();
        stats.report(device, "quotient-resident", n * ratio);
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}
