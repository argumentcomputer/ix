#include <util/gpu_t.cuh>

namespace {
constexpr bool cubin_compatible(int architecture, int major, int minor) {
    // Native cubins can run on newer minor revisions of the same major ISA.
    return architecture / 10 == major && architecture % 10 <= minor;
}

static_assert(cubin_compatible(70, 7, 5));
static_assert(cubin_compatible(75, 7, 5));
static_assert(!cubin_compatible(75, 7, 0));
static_assert(!cubin_compatible(80, 7, 5));
static_assert(cubin_compatible(120, 12, 1));
static_assert(!cubin_compatible(120, 13, 0));

bool has_compiled_kernel(const cudaDeviceProp& properties) {
    constexpr int architectures[] = IX_KZG_CUDA_ARCHITECTURES;
    for (int architecture : architectures)
        if (cubin_compatible(architecture, properties.major, properties.minor))
            return true;
    return false;
}

class Devices {
public:
    std::vector<const gpu_t*> values;

    Devices() {
        int count = 0, saved = 0;
        if (cudaGetDeviceCount(&count) != cudaSuccess || count == 0) return;
        CUDA_OK(cudaGetDevice(&saved));
        for (int id = 0; id < count; ++id) {
            cudaDeviceProp properties;
            CUDA_OK(cudaGetDeviceProperties(&properties, id));
            if (properties.major < 7 || !properties.cooperativeLaunch ||
                !has_compiled_kernel(properties)) continue;
            CUDA_OK(cudaSetDevice(id));
            values.push_back(new gpu_t(static_cast<int>(values.size()), id, properties));
        }
        CUDA_OK(cudaSetDevice(saved));
    }

    ~Devices() {
        int saved = 0;
        (void)cudaGetDevice(&saved);
        for (const auto* gpu : values) {
            // CUDA stream destruction requires the stream's owning context.
            gpu->select();
            delete gpu;
        }
        (void)cudaSetDevice(saved);
    }
};
}

const std::vector<const gpu_t*>& all_gpus() {
    static Devices devices;
    return devices.values;
}

size_t ngpus() { return all_gpus().size(); }

const gpu_t& select_gpu(int id) {
    if (id < 0 || static_cast<size_t>(id) >= ngpus())
        CUDA_OK(cudaErrorInvalidDevice);
    const auto* gpu = all_gpus()[id];
    gpu->select();
    return *gpu;
}

const cudaDeviceProp& gpu_props(int id) { return all_gpus().at(id)->props(); }
