#include <util/gpu_t.cuh>

namespace {
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
            if (properties.major < 7 || !properties.cooperativeLaunch) continue;
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
