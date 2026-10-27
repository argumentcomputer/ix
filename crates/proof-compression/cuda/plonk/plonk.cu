#include "ix_plonk_bn254.h"
#include <ff/alt_bn128.hpp>
// Complete host Jacobian addition depends on BLST's alias-safe vec_select.
#include <blst_t.hpp>
#include <ec/jacobian_t.hpp>
#include <ec/xyzz_t.hpp>
#include <ntt/ntt.cuh>
#define SPPARK_DONT_INSTANTIATE_TEMPLATES
#define TAKE_RESPONSIBILITY_FOR_ERROR_MESSAGE
#include <msm/pippenger.cuh>
#include "../kzg_transfer.cuh"

#include <algorithm>
#include <atomic>
#include <cstdio>
#include <cstring>
#include <limits>
#include <memory>
#include <mutex>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using point_t = jacobian_t<fp_t>;
using bucket_t = xyzz_t<fp_t>;
using affine_t = bucket_t::affine_t;
using msm_impl = msm_t<bucket_t, point_t, affine_t, fr_t>;

static_assert(sizeof(fr_t) == 32 && sizeof(fp_t) == 32);
static_assert(sizeof(affine_t) == 64 && sizeof(point_t) == 96);
static_assert(sizeof(ix_plonk_bn254_fr) == sizeof(fr_t));
static_assert(sizeof(ix_plonk_bn254_affine) == sizeof(affine_t));
static_assert(sizeof(ix_plonk_bn254_jacobian) == sizeof(point_t));
static_assert(sizeof(ix_plonk_bn254_config) == 32);
static_assert(MAX_LG_DOMAIN_SIZE == 28);

namespace {
constexpr uint64_t NTT_BYTES = 2 * (512 * 32 + 512 * 512 * 32 + 2 * 2 * 16384 * 32);
constexpr uint64_t MAX_M = UINT64_C(1) << 26;
constexpr uint32_t MAX_COMMITMENTS = 16;
constexpr uint32_t MAX_SLOTS = 12 + 2 * MAX_COMMITMENTS;
constexpr uint64_t MASK_THRESHOLD = 4096;
constexpr uint64_t MASK_SEED = UINT64_C(0x243f6a8885a308d3);
constexpr size_t MAX_MASK_SUMS = 256;

__host__ __device__ uint64_t mix_counter(uint64_t value) {
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

struct Failure : std::runtime_error {
    int code;
    Failure(int code, const char* text) : std::runtime_error(text), code(code) {}
};

void require(bool condition, const char* message) {
    if (!condition) throw Failure(IX_PLONK_BN254_INVALID, message);
}

uint64_t multiply(uint64_t a, uint64_t b) {
    if (b && a > std::numeric_limits<uint64_t>::max() / b)
        throw Failure(IX_PLONK_BN254_INVALID, "allocation size overflow");
    return a * b;
}

bool power_of_two(uint64_t n) { return n && !(n & (n - 1)); }
uint32_t log_size(uint64_t n) {
    require(power_of_two(n) && n <= MAX_M, "unsupported polynomial length");
    uint32_t log = 0;
    while (n >>= 1) ++log;
    return log;
}

fr_t field(const ix_plonk_bn254_fr& value) {
    constexpr uint64_t modulus[4] = {
        UINT64_C(0x43e1f593f0000001), UINT64_C(0x2833e84879b97091),
        UINT64_C(0xb85045b68181585d), UINT64_C(0x30644e72e131a029),
    };
    bool less = false;
    for (int i = 3; i >= 0; --i) {
        if (value.limbs[i] != modulus[i]) {
            less = value.limbs[i] < modulus[i];
            break;
        }
    }
    require(less, "noncanonical Montgomery field parameter");
    fr_t result;
    std::memcpy(&result, &value, sizeof(result));
    return result;
}

void copy_field(ix_plonk_bn254_fr* out, const fr_t& value) {
    std::memcpy(out, &value, sizeof(value));
}

struct MsmPlan {
    uint32_t window;
    uint64_t persistent, temporary;
};

MsmPlan msm_plan(const gpu_t& gpu, uint64_t count, bool split) {
    require(count && count <= IX_PLONK_BN254_MAX_MSM_POINTS, "unsupported MSM size");
    const uint64_t original_count = count;
    count = (count + 31) & ~UINT64_C(31);
    uint32_t bits = 0;
    for (uint64_t n = count + count / 2; n >>= 1;) ++bits;
    uint32_t window = count <= 192 ? 10 : std::max(10u, std::min(bits - 8, 18u));
    uint64_t windows = (fr_t::bit_length() - 1) / window + 1;
    uint64_t row = UINT64_C(1) << (window - 1);
    uint64_t persistent = (windows * row + gpu.sm_count() * BATCH_ADD_BLOCK_SIZE / WARP_SZ)
                         * sizeof(bucket_t::mem_t) + windows * row * sizeof(uint32_t);
    uint32_t invocation_bits = 0;
    for (uint64_t n = original_count + original_count / 2; n >>= 1;) ++invocation_bits;
    uint64_t batch = std::max(UINT64_C(1), (UINT64_C(1) << (std::max(invocation_bits, window) - window)) >> 6);
    uint64_t stride = ((original_count + batch - 1) / batch + 31) & ~UINT64_C(31);
    uint64_t temporary = stride * (2 * sizeof(uint2) + windows * sizeof(uint32_t))
                       + count * sizeof(fr_t);
    if (split) temporary += msm_impl::split_scratch_bytes(original_count, window, static_cast<uint32_t>(windows));
    return {window, persistent, temporary};
}

class Buffer {
    void* data_ = nullptr;
    const gpu_t* gpu_ = nullptr;
  public:
    Buffer() = default;
    Buffer(const gpu_t& gpu, uint64_t bytes) : gpu_(&gpu) {
        if (bytes) data_ = gpu.Dmalloc(bytes);
    }
    Buffer(const Buffer&) = delete;
    Buffer& operator=(const Buffer&) = delete;
    ~Buffer() {
        if (data_) {
            gpu_->select();
            (void)cudaFreeAsync(data_, *gpu_);
            (void)cudaStreamSynchronize(*gpu_);
        }
    }
    template<typename T> T* as() const { return static_cast<T*>(data_); }
};

struct Basis;
struct Quotient;
struct Workspace;
std::mutex contexts_mutex;
std::unordered_set<int> owned_devices;
}

struct ix_plonk_bn254_context {
    const gpu_t& gpu;
    uint64_t budget, headroom, accounted = 0, high = 0, next = 1;
    uint32_t msm_strategy;
    std::mutex mutex;
    std::atomic<bool> cancelled{false};
    std::atomic<bool> poisoned{false};
    std::unique_ptr<TransferLane> transfer;
    std::unordered_map<uint64_t, std::unique_ptr<Basis>> bases;
    std::unordered_map<uint64_t, std::unique_ptr<Quotient>> quotients;
    std::unique_ptr<Workspace> workspace;
    ix_plonk_bn254_stats stats{};

    ix_plonk_bn254_context(const gpu_t& gpu, uint64_t budget, uint64_t headroom, uint32_t strategy)
        : gpu(gpu), budget(budget), headroom(headroom), msm_strategy(strategy) {}
    ~ix_plonk_bn254_context();

    void ready() {
        gpu.select();
        if (poisoned) throw Failure(IX_PLONK_BN254_POISONED, "CUDA context is poisoned");
        if (cancelled.load()) throw Failure(IX_PLONK_BN254_CANCELLED, "CUDA proof cancelled");
    }

    void reserve(uint64_t bytes) {
        ready();
        if (bytes > budget - std::min(accounted, budget))
            throw Failure(IX_PLONK_BN254_MEMORY, "CUDA allocation budget exceeded");
        size_t free = 0, total = 0;
        CUDA_OK(cudaMemGetInfo(&free, &total));
        cudaMemPool_t pool;
        CUDA_OK(cudaDeviceGetMemPool(&pool, gpu.cid()));
        uint64_t reserved = 0, used = 0;
        CUDA_OK(cudaMemPoolGetAttribute(pool, cudaMemPoolAttrReservedMemCurrent, &reserved));
        CUDA_OK(cudaMemPoolGetAttribute(pool, cudaMemPoolAttrUsedMemCurrent, &used));
        uint64_t available = std::min<uint64_t>(total, free + (reserved > used ? reserved - used : 0));
        if (headroom > available || bytes > available - headroom)
            throw Failure(IX_PLONK_BN254_MEMORY, "insufficient CUDA memory with required headroom");
        accounted += bytes;
        high = std::max(high, accounted);
    }

    void upload(void* destination, const void* source, uint64_t bytes) {
        ready();
        const auto started = std::chrono::steady_clock::now();
        TransferStats sample;
        transfer->upload.upload(gpu, gpu, destination, source, bytes, sample);
        gpu.sync();
        transfer->upload.finish_upload(sample);
        stats.upload_wall_ms += std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now() - started).count();
        stats.transfer_host_copy_ms += sample.host_copy_ms;
        stats.upload_dma_ms += sample.upload_ms;
        stats.upload_bytes += bytes;
        ++stats.upload_calls;
    }

    void download(void* destination, const void* source, uint64_t bytes) {
        ready();
        const auto started = std::chrono::steady_clock::now();
        TransferStats sample;
        transfer->download.download(gpu, gpu, destination, source, bytes, sample);
        gpu.sync();
        stats.download_wall_ms += std::chrono::duration<double, std::milli>(
            std::chrono::steady_clock::now() - started).count();
        stats.transfer_host_copy_ms += sample.host_copy_ms;
        stats.download_dma_ms += sample.download_ms;
        stats.download_bytes += bytes;
        ++stats.download_calls;
    }

    uint64_t handle() {
        if (next == std::numeric_limits<uint64_t>::max())
            throw Failure(IX_PLONK_BN254_INVALID, "CUDA handle generation exhausted");
        return next++;
    }
};

namespace {
struct Reservation {
    ix_plonk_bn254_context& context;
    uint64_t bytes;
    Reservation(ix_plonk_bn254_context& context, uint64_t bytes) : context(context), bytes(bytes) {
        context.reserve(bytes);
    }
    ~Reservation() { context.accounted -= bytes; }
};

struct Basis {
    Reservation reservation;
    Buffer points;
    uint64_t count;
    uint64_t mask_seed = 0;
    struct Range {
        uint64_t offset, count;
        bool operator==(const Range& other) const {
            return offset == other.offset && count == other.count;
        }
    };
    struct RangeHash {
        size_t operator()(const Range& range) const {
            return static_cast<size_t>(mix_counter(range.offset) ^ mix_counter(range.count));
        }
    };
    std::unordered_map<Range, point_t, RangeHash> mask_sums;
    Basis(ix_plonk_bn254_context& context, uint64_t count)
        : reservation(context, multiply(count, sizeof(affine_t))),
          points(context.gpu, reservation.bytes), count(count) {}
};

struct Workspace {
    Reservation reservation;
    uint32_t window;
    msm_impl* msm;
    Workspace(ix_plonk_bn254_context& context, uint64_t count, const MsmPlan& plan)
        : reservation(context, plan.persistent), window(plan.window),
          msm(new msm_impl(nullptr, count, sizeof(affine_t), context.gpu.id())) {
        msm->set_split_buckets(context.msm_strategy == IX_PLONK_BN254_MSM_SPLIT);
    }
    ~Workspace() {
        // A sticky device fault makes sppark's throwing destructor unsafe.
        // The poisoned worker must exit so CUDA can reclaim that context.
        if (cudaDeviceSynchronize() == cudaSuccess) delete msm;
    }
};

struct alignas(32) NumeratorParameters {
    fr_t omega, coset, identity_coset, alpha, beta, gamma, vanishing, vanishing_inverse;
    fr_t bl[2], br[2], bo[2], bz[3];
    const fr_t* columns[MAX_SLOTS];
    const fr_t* boundary;
    fr_t* output;
    uint64_t n;
    uint32_t commitments, ratio, coset_index, log_m, fused;
};

struct Quotient {
    Reservation reservation;
    Buffer canonical, evaluations, boundary, output;
    ix_plonk_bn254_quotient_config config;
    std::vector<bool> present;
    bool finished = false;

    Quotient(ix_plonk_bn254_context& context, const ix_plonk_bn254_quotient_config& config)
        : reservation(context, multiply(2 * (12 + 2 * uint64_t(config.commitments)) + 1, multiply(config.n, 32)) + multiply(config.m, 32)),
          canonical(context.gpu, multiply(12 + 2 * uint64_t(config.commitments), multiply(config.n, 32))),
          evaluations(context.gpu, multiply(12 + 2 * uint64_t(config.commitments), multiply(config.n, 32))),
          boundary(context.gpu, multiply(config.n, 32)),
          output(context.gpu, multiply(config.m, 32)), config(config),
          present(12 + 2 * config.commitments, false) {}
};

__global__ void copy_scaled(fr_t* output, const fr_t* input, uint64_t count,
                            fr_t shift, uint32_t reverse_log, fr_t constant, bool fill) {
    uint64_t i = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    const uint64_t stride = uint64_t(gridDim.x) * blockDim.x;
    fr_t step = shift ^ static_cast<uint32_t>(stride);
    fr_t power = shift ^ static_cast<uint32_t>(i);
    for (; i < count; i += stride) {
        fr_t scale = reverse_log ? shift ^ (__brev(static_cast<uint32_t>(i)) >> (32 - reverse_log)) : power;
        output[i] = (fill ? constant : input[i]) * scale;
        power *= step;
    }
}

__device__ fr_t mask_scalar(uint64_t seed, uint64_t index) {
    constexpr uint64_t step = UINT64_C(0x9e3779b97f4a7c15);
    constexpr uint64_t modulus[4] = {
        UINT64_C(0x43e1f593f0000001), UINT64_C(0x2833e84879b97091),
        UINT64_C(0xb85045b68181585d), UINT64_C(0x30644e72e131a029),
    };
    uint64_t words[4];
    for (unsigned i = 0; i < 4; ++i)
        words[i] = mix_counter(seed + (4 * index + i + 1) * step);
    // Reduced raw Montgomery residues have the same full-width distribution
    // as field elements. These masks balance digits; they are not randomness
    // for the proof protocol and need no cryptographic pseudorandomness.
    for (;;) {
        bool greater_or_equal = true;
        for (int i = 3; i >= 0; --i) {
            if (words[i] != modulus[i]) {
                greater_or_equal = words[i] > modulus[i];
                break;
            }
        }
        if (!greater_or_equal) break;
        uint64_t borrow = 0;
        for (unsigned i = 0; i < 4; ++i) {
            uint64_t difference = words[i] - modulus[i];
            uint64_t next_borrow = (words[i] < modulus[i]) | (difference < borrow);
            words[i] = difference - borrow;
            borrow = next_borrow;
        }
    }
    fr_t result;
    memcpy(&result, words, sizeof(result));
    return result;
}

__global__ void mask_scalars(fr_t* values, uint64_t count, uint64_t seed, bool add) {
    for (uint64_t i = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
         i < count; i += uint64_t(gridDim.x) * blockDim.x) {
        fr_t mask = mask_scalar(seed, i);
        values[i] = add ? values[i] + mask : mask;
    }
}

void scale(ix_plonk_bn254_context& context, fr_t* out, const fr_t* in,
           uint64_t n, const fr_t& shift, uint32_t reverse_log = 0,
           bool fill = false, const fr_t& constant = fr_t::one()) {
    copy_scaled<<<context.gpu.sm_count() * 4, 256, 0, context.gpu>>>(
        out, in, n, shift, reverse_log, constant, fill);
    CUDA_OK(cudaGetLastError());
}

void transform(ix_plonk_bn254_context& context, fr_t* data, uint64_t count,
               bool inverse, bool bit_reversed, const fr_t& coset) {
    context.ready();
    uint32_t log = log_size(count);
    require(!coset.is_zero(), "zero FFT coset");
    if (count == 1) { ++context.stats.fft_calls; return; }
    if (!inverse && !coset.is_one())
        scale(context, data, data, count, coset, bit_reversed ? log : 0);
    NTT::Base_dev_ptr(context.gpu, data, log,
        bit_reversed ? NTT::InputOutputOrder::RN : NTT::InputOutputOrder::NN,
        inverse ? NTT::Direction::inverse : NTT::Direction::forward,
        NTT::Type::standard);
    if (inverse && !coset.is_one())
        scale(context, data, data, count, coset.reciprocal());
    CUDA_OK(cudaGetLastError());
    ++context.stats.fft_calls;
}

__device__ fr_t linear_blinder(const fr_t* coefficients, const fr_t& x) {
    return coefficients[0] + coefficients[1] * x;
}

__device__ fr_t quadratic_blinder(const fr_t* coefficients, const fr_t& x) {
    return coefficients[0] + (coefficients[1] + coefficients[2] * x) * x;
}

__global__ void numerator(NumeratorParameters p) {
    uint64_t j = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x;
    const uint64_t stride = uint64_t(gridDim.x) * blockDim.x;
    fr_t x = p.coset * (p.omega ^ static_cast<uint32_t>(j));
    const fr_t step = p.omega ^ static_cast<uint32_t>(stride);
    for (; j < p.n; j += stride) {
        const uint64_t next = (j + 1) & (p.n - 1);
        fr_t l = p.columns[0][j] + p.vanishing * linear_blinder(p.bl, x);
        fr_t r = p.columns[1][j] + p.vanishing * linear_blinder(p.br, x);
        fr_t o = p.columns[2][j] + p.vanishing * linear_blinder(p.bo, x);
        fr_t z = p.columns[3][j] + p.vanishing * quadratic_blinder(p.bz, x);
        fr_t zs = p.columns[3][next] + p.vanishing * quadratic_blinder(p.bz, p.omega * x);
        fr_t gate = p.columns[5][j] * l + p.columns[6][j] * r
                  + p.columns[7][j] * l * r + p.columns[8][j] * o + p.columns[4][j];
        for (uint32_t i = 0; i < p.commitments; ++i)
            gate += p.columns[12 + 2*i][j] * p.columns[13 + 2*i][j];
        fr_t left = zs * (l + p.beta * p.columns[9][j] + p.gamma)
                          * (r + p.beta * p.columns[10][j] + p.gamma)
                          * (o + p.beta * p.columns[11][j] + p.gamma);
        // The permutation's three identity cosets use the domain's fixed
        // multiplicative generator, not the current quotient coset shift.
        fr_t id = p.beta * x;
        const fr_t u = p.identity_coset;
        fr_t right = z * (l + id + p.gamma) * (r + u * id + p.gamma)
                        * (o + u * u * id + p.gamma);
        fr_t boundary = (z - fr_t::one()) * p.boundary[j];
        fr_t value = gate + p.alpha * (left - right + p.alpha * boundary);
        if (p.fused) value *= p.vanishing_inverse;
        uint32_t destination = __brev(static_cast<uint32_t>(p.ratio*j + p.coset_index)) >> (32-p.log_m);
        p.output[destination] = value;
        x *= step;
    }
}

int error_result(ix_plonk_bn254_error* out, int code, const char* message) noexcept {
    if (out) {
        out->code = code;
        std::snprintf(out->message, sizeof(out->message), "%s", message ? message : "CUDA failure");
    }
    return code;
}

template<typename Function>
int guarded(ix_plonk_bn254_context* context, ix_plonk_bn254_error* error,
            Function&& function, bool cleanup = false) noexcept {
    if (error) { error->code = 0; error->message[0] = 0; }
    try {
        require(context != nullptr, "null CUDA context");
        std::lock_guard<std::mutex> lock(context->mutex);
        context->gpu.select();
        if (!cleanup) context->ready();
        function();
        context->gpu.sync();
        if (!cleanup) context->ready();
        return 0;
    } catch (const Failure& failure) {
        if (context && failure.code == IX_PLONK_BN254_RUNTIME) context->poisoned = true;
        if (context) (void)cudaDeviceSynchronize();
        return error_result(error, failure.code, failure.what());
    } catch (const cuda_error& failure) {
        if (context) { context->poisoned = true; (void)cudaDeviceSynchronize(); }
        return error_result(error, IX_PLONK_BN254_RUNTIME, failure.what());
    } catch (const std::exception& failure) {
        if (context) { context->poisoned = true; (void)cudaDeviceSynchronize(); }
        return error_result(error, IX_PLONK_BN254_RUNTIME, failure.what());
    } catch (...) {
        if (context) { context->poisoned = true; (void)cudaDeviceSynchronize(); }
        return error_result(error, IX_PLONK_BN254_RUNTIME, "unknown CUDA adapter exception");
    }
}

Quotient& session(ix_plonk_bn254_context& context, uint64_t id) {
    auto found = context.quotients.find(id);
    require(found != context.quotients.end(), "unknown quotient handle");
    return *found->second;
}
}

ix_plonk_bn254_context::~ix_plonk_bn254_context() {
    gpu.select();
    (void)cudaDeviceSynchronize();
    quotients.clear();
    bases.clear();
    workspace.reset();
    transfer.reset();
    (void)cudaDeviceSynchronize();
    std::lock_guard<std::mutex> lock(contexts_mutex);
    owned_devices.erase(gpu.cid());
}

#ifndef __CUDA_ARCH__
extern "C" int ix_plonk_bn254_check_field_abi(const uint64_t fq[3][4],
    const uint64_t fr[3][4], ix_plonk_bn254_error* error) {
    if (!fq || !fr) return error_result(error, IX_PLONK_BN254_INVALID, "null field ABI parameters");
    const fp_t fq_one = fp_t::one();
    const fr_t fr_one = fr_t::one();
    if (std::memcmp(fq[0], alt_bn128::ALT_BN128_P, 32) || std::memcmp(fq[1], &fq_one, 32)
        || std::memcmp(fq[2], alt_bn128::ALT_BN128_RR, 32)
        || std::memcmp(fr[0], alt_bn128::ALT_BN128_r, 32) || std::memcmp(fr[1], &fr_one, 32)
        || std::memcmp(fr[2], alt_bn128::ALT_BN128_rRR, 32))
        return error_result(error, IX_PLONK_BN254_INVALID, "BN254 Montgomery ABI mismatch");
    return error_result(error, 0, "");
}
#endif

extern "C" int ix_plonk_bn254_ntt_parameters(uint32_t log,
    ix_plonk_bn254_fr* root, ix_plonk_bn254_fr* inverse,
    ix_plonk_bn254_fr* size_inverse, ix_plonk_bn254_error* error) {
    if (log > 26 || !root || !inverse || !size_inverse)
        return error_result(error, IX_PLONK_BN254_INVALID, "unsupported NTT parameter request");
    copy_field(root, forward_roots_of_unity[log]);
    copy_field(inverse, inverse_roots_of_unity[log]);
    copy_field(size_inverse, domain_size_inverse[log]);
    return error_result(error, 0, "");
}

extern "C" int ix_plonk_bn254_context_create(const ix_plonk_bn254_config* config,
    ix_plonk_bn254_context** out, ix_plonk_bn254_error* error) {
    if (out) *out = nullptr;
    bool claimed = false;
    int ordinal = -1;
    try {
        require(config && out, "missing CUDA context configuration");
        require(config->abi_version == IX_PLONK_BN254_ABI_VERSION
            && config->struct_bytes == sizeof(*config)
            && config->msm_strategy <= IX_PLONK_BN254_MSM_MASK,
            "CUDA context ABI mismatch");
        require(config->budget_bytes > NTT_BYTES, "CUDA budget is too small");
        const gpu_t* gpu = nullptr;
        for (const auto* candidate : all_gpus())
            if (candidate->cid() == config->device) gpu = candidate;
        if (!gpu) throw Failure(IX_PLONK_BN254_UNSUPPORTED, "no compatible CUDA device");
        ordinal = gpu->cid();
        {
            std::lock_guard<std::mutex> lock(contexts_mutex);
            require(owned_devices.insert(ordinal).second, "CUDA device already has an adapter context");
            claimed = true;
        }
        gpu->select();
        auto context = std::make_unique<ix_plonk_bn254_context>(*gpu, config->budget_bytes, config->driver_headroom_bytes, config->msm_strategy);
        claimed = false;
        context->reserve(NTT_BYTES);
        (void)NTTParameters::all();
        context->transfer = std::make_unique<TransferLane>();
        gpu->sync();
        *out = context.release();
        return error_result(error, 0, "");
    } catch (const Failure& failure) {
        if (claimed) { std::lock_guard<std::mutex> lock(contexts_mutex); owned_devices.erase(ordinal); }
        return error_result(error, failure.code, failure.what());
    } catch (const std::exception& failure) {
        if (claimed) { std::lock_guard<std::mutex> lock(contexts_mutex); owned_devices.erase(ordinal); }
        return error_result(error, IX_PLONK_BN254_RUNTIME, failure.what());
    } catch (...) {
        if (claimed) { std::lock_guard<std::mutex> lock(contexts_mutex); owned_devices.erase(ordinal); }
        return error_result(error, IX_PLONK_BN254_RUNTIME, "CUDA context initialization failed");
    }
}

extern "C" int ix_plonk_bn254_context_destroy(ix_plonk_bn254_context* context,
    ix_plonk_bn254_error* error) {
    if (!context) return error_result(error, 0, "");
    int result = guarded(context, error, [&] {
        context->cancelled.store(true);
        context->quotients.clear(); context->bases.clear(); context->workspace.reset();
    }, true);
    delete context;
    return result;
}

extern "C" int ix_plonk_bn254_context_cancel(ix_plonk_bn254_context* context,
    ix_plonk_bn254_error* error) {
    if (!context) return error_result(error, IX_PLONK_BN254_INVALID, "null CUDA context");
    context->cancelled.store(true);
    return error_result(error, 0, "");
}

extern "C" int ix_plonk_bn254_get_stats(ix_plonk_bn254_context* context,
    ix_plonk_bn254_stats* out, ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        require(out, "null CUDA statistics output");
        *out = context->stats;
        out->transfer_timing_enabled = transfer_profiling() ? 1 : 0;
        size_t free, total;
        CUDA_OK(cudaMemGetInfo(&free, &total));
        out->driver_free_bytes = free; out->driver_total_bytes = total;
        cudaMemPool_t pool;
        CUDA_OK(cudaDeviceGetMemPool(&pool, context->gpu.cid()));
        CUDA_OK(cudaMemPoolGetAttribute(pool, cudaMemPoolAttrUsedMemCurrent, &out->pool_used_bytes));
        CUDA_OK(cudaMemPoolGetAttribute(pool, cudaMemPoolAttrUsedMemHigh, &out->pool_used_high_bytes));
        CUDA_OK(cudaMemPoolGetAttribute(pool, cudaMemPoolAttrReservedMemCurrent, &out->pool_reserved_bytes));
        CUDA_OK(cudaMemPoolGetAttribute(pool, cudaMemPoolAttrReservedMemHigh, &out->pool_reserved_high_bytes));
        out->accounted_bytes = context->accounted; out->accounted_high_bytes = context->high;
        out->budget_bytes = context->budget;
    }, true);
}

extern "C" int ix_plonk_bn254_basis_upload(ix_plonk_bn254_context* context,
    const ix_plonk_bn254_affine* points, uint64_t count,
    ix_plonk_bn254_basis* out, ix_plonk_bn254_error* error) {
    if (out) *out = 0;
    return guarded(context, error, [&] {
        require(points && out && count && count <= IX_PLONK_BN254_MAX_MSM_POINTS, "invalid CUDA basis upload");
        auto basis = std::make_unique<Basis>(*context, count);
        context->upload(basis->points.as<void>(), points, count * sizeof(affine_t));
        uint64_t id = context->handle();
        basis->mask_seed = mix_counter(MASK_SEED ^ id);
        context->bases.emplace(id, std::move(basis)); *out = id;
    });
}

extern "C" int ix_plonk_bn254_basis_destroy(ix_plonk_bn254_context* context,
    ix_plonk_bn254_basis basis, ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        require(context->bases.erase(basis) == 1, "unknown CUDA basis handle");
    }, true);
}

namespace {
point_t invoke_msm(ix_plonk_bn254_context& context, affine_t* points,
                   fr_t* scalars, uint64_t count) {
    dev_ptr_t<affine_t> point_view(points, count);
    dev_ptr_t<fr_t> scalar_view(scalars, count);
    point_t result;
    RustError status = context.workspace->msm->invoke(result, point_view, count, scalar_view, true);
    if (status.code) {
        std::string message = status.message ? status.message : "sppark MSM failed";
        std::free(status.message);
        throw Failure(IX_PLONK_BN254_RUNTIME, message.c_str());
    }
    std::free(status.message);
    context.gpu.sync();
    context.ready();
    if (context.msm_strategy == IX_PLONK_BN254_MSM_SPLIT) {
        const auto& statistics = context.workspace->msm->split_statistics();
        ++context.stats.split_msm_calls;
        context.stats.split_unit_points += statistics.unit_points;
        for (unsigned window = 0; window < 32; ++window) {
            context.stats.split_max_bucket[window] = std::max(context.stats.split_max_bucket[window], statistics.max_bucket[window]);
            context.stats.split_chunk_count[window] += statistics.chunk_count[window];
            context.stats.split_nonzero_digits[window] += statistics.nonzero_digits[window];
            context.stats.split_zero_digits[window] += statistics.zero_digits[window];
        }
        context.stats.split_classify_ms += statistics.classify_ms;
        context.stats.split_chunks_ms += statistics.chunks_ms;
        context.stats.split_reduce_ms += statistics.reduce_ms;
    }
    if (result.is_inf()) {
        fp_t zero; zero.zero();
        result = point_t(fp_t::one(), fp_t::one(), zero);
    }
    return result;
}

void run_msm(ix_plonk_bn254_context* context,
    ix_plonk_bn254_basis basis, uint64_t offset,
    const ix_plonk_bn254_fr* scalars, uint64_t count,
    ix_plonk_bn254_jacobian* out) {
    require(scalars && out && count, "missing MSM operands");
    auto found = context->bases.find(basis);
    require(found != context->bases.end(), "unknown CUDA basis handle");
    require(offset <= found->second->count && count <= found->second->count - offset,
            "CUDA MSM range exceeds basis");
    auto plan = msm_plan(context->gpu, count, context->msm_strategy == IX_PLONK_BN254_MSM_SPLIT);
    if (context->workspace && context->workspace->window != plan.window) context->workspace.reset();
    if (!context->workspace) context->workspace = std::make_unique<Workspace>(*context, count, plan);
    Reservation temporary(*context, plan.temporary);
    Buffer values(context->gpu, multiply((count + 31) & ~UINT64_C(31), 32));
    Basis& owner = *found->second;
    affine_t* points = owner.points.as<affine_t>() + offset;
    const bool masked = context->msm_strategy == IX_PLONK_BN254_MSM_MASK && count >= MASK_THRESHOLD;
    const Basis::Range range{offset, count};
    const uint64_t mask_seed = mix_counter(owner.mask_seed ^ mix_counter(offset)
                                          ^ mix_counter(count + UINT64_C(0x13198a2e03707344)));
    point_t mask_sum;
    if (masked) {
        auto cached = owner.mask_sums.find(range);
        if (cached != owner.mask_sums.end()) {
            mask_sum = cached->second;
            ++context->stats.mask_cache_hits;
        } else {
            mask_scalars<<<context->gpu.sm_count() * 4, 256, 0, context->gpu>>>(
                values.as<fr_t>(), count, mask_seed, false);
            CUDA_OK(cudaGetLastError());
            context->gpu.sync();
            mask_sum = invoke_msm(*context, points, values.as<fr_t>(), count);
            if (owner.mask_sums.size() >= MAX_MASK_SUMS) owner.mask_sums.clear();
            owner.mask_sums.emplace(range, mask_sum);
            ++context->stats.mask_sum_calls;
        }
    }
    context->upload(values.as<void>(), scalars, count * 32);
    if (masked) {
        mask_scalars<<<context->gpu.sm_count() * 4, 256, 0, context->gpu>>>(
            values.as<fr_t>(), count, mask_seed, true);
        CUDA_OK(cudaGetLastError());
        context->gpu.sync();
    }
    point_t result = invoke_msm(*context, points, values.as<fr_t>(), count);
    if (masked) {
        mask_sum.cneg(true);
        result.dadd(mask_sum);
        ++context->stats.masked_msm_calls;
    }
    if (result.is_inf()) {
        std::memset(out, 0, sizeof(*out));
        const fp_t one = fp_t::one();
        std::memcpy(&out->x, &one, sizeof(one));
        std::memcpy(&out->y, &one, sizeof(one));
    } else {
        std::memcpy(out, &result, sizeof(result));
    }
    ++context->stats.msm_calls;
}
}

extern "C" int ix_plonk_bn254_msm(ix_plonk_bn254_context* context,
    ix_plonk_bn254_basis basis, uint64_t offset,
    const ix_plonk_bn254_fr* scalars, uint64_t count,
    ix_plonk_bn254_jacobian* out, ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        run_msm(context, basis, offset, scalars, count, out);
    });
}

extern "C" int ix_plonk_bn254_fft(ix_plonk_bn254_context* context,
    ix_plonk_bn254_fr* values, uint64_t count, uint32_t inverse,
    uint32_t reversed, const ix_plonk_bn254_fr* coset,
    ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        require(values && coset && inverse <= 1 && reversed <= 1, "invalid FFT arguments");
        (void)log_size(count);
        fr_t shift = field(*coset);
        require(!shift.is_zero(), "zero FFT coset");
        Reservation reservation(*context, multiply(count, 32));
        Buffer buffer(context->gpu, reservation.bytes);
        context->upload(buffer.as<void>(), values, reservation.bytes);
        transform(*context, buffer.as<fr_t>(), count, inverse, reversed, shift);
        context->download(values, buffer.as<void>(), reservation.bytes);
    });
}

extern "C" int ix_plonk_bn254_quotient_begin(ix_plonk_bn254_context* context,
    const ix_plonk_bn254_quotient_config* config,
    ix_plonk_bn254_quotient* out, ix_plonk_bn254_error* error) {
    if (out) *out = 0;
    return guarded(context, error, [&] {
        require(config && out && !config->reserved, "invalid quotient configuration");
        uint32_t lg_n = log_size(config->n), lg_m = log_size(config->m);
        require(config->n >= 2 && config->m >= config->n &&
                (config->m / config->n == 4 || config->m / config->n == 8)
                && config->commitments <= MAX_COMMITMENTS, "unsupported quotient dimensions");
        require((field(config->omega) - forward_roots_of_unity[lg_n]).is_zero()
             && (field(config->omega_big) - forward_roots_of_unity[lg_m]).is_zero(), "quotient domain root mismatch");
        require((field(config->coset) - group_gen).is_zero(), "unsupported quotient coset multiplier");
        (void)field(config->alpha); (void)field(config->beta); (void)field(config->gamma);
        for (const auto& x : config->bl) (void)field(x);
        for (const auto& x : config->br) (void)field(x);
        for (const auto& x : config->bo) (void)field(x);
        for (const auto& x : config->bz) (void)field(x);
        require(context->quotients.empty(), "one quotient session is allowed per context");
        auto quotient = std::make_unique<Quotient>(*context, *config);
        uint64_t id = context->handle(); context->quotients.emplace(id, std::move(quotient)); *out = id;
    });
}

extern "C" int ix_plonk_bn254_quotient_put(ix_plonk_bn254_context* context,
    ix_plonk_bn254_quotient id, uint32_t slot, ix_plonk_bn254_fr* values,
    uint64_t count, ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        auto& q = session(*context, id);
        require(values && !q.finished && slot < q.present.size() && !q.present[slot]
                && count == q.config.n, "invalid quotient polynomial slot");
        fr_t* destination = q.canonical.as<fr_t>() + uint64_t(slot) * count;
        context->upload(destination, values, count * 32);
        transform(*context, destination, count, true, false, fr_t::one());
        context->download(values, destination, count * 32);
        q.present[slot] = true;
    });
}

extern "C" int ix_plonk_bn254_quotient_finish(ix_plonk_bn254_context* context,
    ix_plonk_bn254_quotient id, uint32_t fused, ix_plonk_bn254_fr* output,
    uint64_t count, ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        auto& q = session(*context, id);
        require(output && !q.finished && fused <= 1 && count == q.config.m
                && std::all_of(q.present.begin(), q.present.end(), [](bool v) { return v; }),
                "incomplete quotient session");
        NumeratorParameters p{};
        p.omega = field(q.config.omega);
        p.identity_coset = field(q.config.coset);
        p.alpha = field(q.config.alpha); p.beta = field(q.config.beta); p.gamma = field(q.config.gamma);
        for (unsigned i = 0; i < 2; ++i) {
            p.bl[i] = field(q.config.bl[i]); p.br[i] = field(q.config.br[i]); p.bo[i] = field(q.config.bo[i]);
        }
        for (unsigned i = 0; i < 3; ++i) p.bz[i] = field(q.config.bz[i]);
        p.n = q.config.n; p.commitments = q.config.commitments;
        p.ratio = static_cast<uint32_t>(q.config.m / q.config.n);
        p.log_m = log_size(q.config.m); p.fused = fused;
        p.output = q.output.as<fr_t>(); p.boundary = q.boundary.as<fr_t>();
        for (uint32_t i = 0; i < q.present.size(); ++i)
            p.columns[i] = q.evaluations.as<fr_t>() + uint64_t(i) * p.n;
        fr_t coset = field(q.config.coset);
        const fr_t omega_big = field(q.config.omega_big);
        for (uint32_t i = 0; i < p.ratio; ++i) {
            context->ready(); p.coset_index = i; p.coset = coset;
            p.vanishing = (coset ^ static_cast<uint32_t>(p.n)) - fr_t::one();
            require(!p.vanishing.is_zero(), "quotient coset intersects the base domain");
            p.vanishing_inverse = p.vanishing.reciprocal();
            for (uint32_t slot = 0; slot < q.present.size(); ++slot) {
                context->ready();
                fr_t* destination = q.evaluations.as<fr_t>() + uint64_t(slot) * p.n;
                scale(*context, destination, q.canonical.as<fr_t>() + uint64_t(slot) * p.n, p.n, coset);
                transform(*context, destination, p.n, false, false, fr_t::one());
            }
            scale(*context, q.boundary.as<fr_t>(), nullptr, p.n, coset, 0, true,
                  domain_size_inverse[log_size(p.n)]);
            transform(*context, q.boundary.as<fr_t>(), p.n, false, false, fr_t::one());
            numerator<<<context->gpu.sm_count() * 4, 256, 0, context->gpu>>>(p);
            CUDA_OK(cudaGetLastError());
            coset *= omega_big;
        }
        if (fused) {
            transform(*context, q.output.as<fr_t>(), q.config.m, true, true, field(q.config.coset));
            ++context->stats.quotient_calls;
        } else { ++context->stats.numerator_calls; }
        context->download(output, q.output.as<void>(), q.config.m * 32);
        q.finished = true;
    });
}

extern "C" int ix_plonk_bn254_quotient_destroy(ix_plonk_bn254_context* context,
    ix_plonk_bn254_quotient id, ix_plonk_bn254_error* error) {
    return guarded(context, error, [&] {
        require(context->quotients.erase(id) == 1, "unknown quotient handle");
    }, true);
}
