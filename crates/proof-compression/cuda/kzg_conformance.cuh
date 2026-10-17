#pragma once

#ifndef __CUDA_ARCH__
extern "C" int ix_kzg_ntt_parameters(uint32_t lg, fr_t* output) {
    if (!output || lg > KZG_MAX_FFT_LOG) return cudaErrorInvalidValue;
    output[0] = forward_roots_of_unity[lg];
    output[1] = inverse_roots_of_unity[lg];
    output[2] = domain_size_inverse[lg];
    return 0;
}
#endif

namespace {

template<class F> __global__ void field_conformance(const F* input, F* output) {
    const size_t i = threadIdx.x;
    const F a = input[i], b = input[(i + 1) % 32];
    const F one = F::one();
    const F zero = one - one;
    // Reciprocal cooperates with the adjacent lane; every lane participates,
    // including zero inputs, whose output follows the inverse(0) = 0 convention.
    const F safe = F::csel(one, a, a.is_zero());
    const F inverse = safe.reciprocal();
    output[6 * i] = one;
    output[6 * i + 1] = a + b;
    output[6 * i + 2] = a - b;
    output[6 * i + 3] = a * b;
    output[6 * i + 4] = -a;
    output[6 * i + 5] = F::csel(zero, inverse, a.is_zero());
}

} // namespace

// Fixed-size conformance vectors exercise both device fields independently
// of the MSM and FFT algorithms that consume their Montgomery representation.
extern "C" int ix_kzg_field_conformance(int device, const fp_t* fq, const fr_t* fr,
                                        fp_t* fq_output, fr_t* fr_output) {
    try {
        if (!fq || !fr || !fq_output || !fr_output) return cudaErrorInvalidValue;
        const auto& gpu = device_gpu(device);
        {
            dev_ptr_t<fp_t> fq_input(32, gpu), fq_result(32 * 6, gpu);
            dev_ptr_t<fr_t> fr_input(32, gpu), fr_result(32 * 6, gpu);
            gpu.HtoD(fq_input.data(), fq, 32);
            gpu.HtoD(fr_input.data(), fr, 32);
            field_conformance<<<1, 32, 0, gpu>>>(fq_input.data(), fq_result.data());
            CUDA_OK(cudaGetLastError());
            field_conformance<<<1, 32, 0, gpu>>>(fr_input.data(), fr_result.data());
            CUDA_OK(cudaGetLastError());
            gpu.DtoH(fq_output, fq_result.data(), 32 * 6);
            gpu.DtoH(fr_output, fr_result.data(), 32 * 6);
            gpu.sync();
        }
        gpu.sync();
        return 0;
    } catch (const cuda_error& e) { return failure(e.code(), e.what()); }
      catch (const std::exception& e) { return failure(cudaErrorUnknown, e.what()); }
}
