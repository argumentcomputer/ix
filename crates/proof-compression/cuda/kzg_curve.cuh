#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>

#include <ff/alt_bn128.hpp>
constexpr size_t KZG_FQ_LIMBS = 4;
static_assert(MAX_LG_DOMAIN_SIZE == 28);

// The NTT domain stride is 32 bits even when the field has a 2^32 root.
constexpr uint32_t KZG_MAX_FFT_LOG = MAX_LG_DOMAIN_SIZE < 31 ? MAX_LG_DOMAIN_SIZE : 31;

static_assert(sizeof(fr_t) == 4 * sizeof(uint64_t));
static_assert(sizeof(fp_t) == KZG_FQ_LIMBS * sizeof(uint64_t));

#ifndef __CUDA_ARCH__
static_assert(alignof(fr_t) == alignof(uint64_t));
static_assert(alignof(fp_t) == alignof(uint64_t));

// Raw Montgomery storage crosses the FFI without conversion. Check the
// modulus, representation of one and R^2 before accepting host limb buffers.
extern "C" int ix_kzg_check_field_abi(const uint64_t* fq, size_t fq_bytes,
                                      const uint64_t* fr, size_t fr_bytes) {
    if (!fq || !fr || fq_bytes != 3 * sizeof(fp_t) || fr_bytes != 3 * sizeof(fr_t))
        return 1;
    const auto& fq_modulus = alt_bn128::ALT_BN128_P;
    const auto& fq_r2 = alt_bn128::ALT_BN128_RR;
    const auto& fr_modulus = alt_bn128::ALT_BN128_r;
    const auto& fr_r2 = alt_bn128::ALT_BN128_rRR;
    const fp_t fq_one = fp_t::one();
    const fr_t fr_one = fr_t::one();
    return std::memcmp(fq, fq_modulus, sizeof(fp_t)) != 0
        || std::memcmp(fq + KZG_FQ_LIMBS, &fq_one, sizeof(fp_t)) != 0
        || std::memcmp(fq + 2 * KZG_FQ_LIMBS, fq_r2, sizeof(fp_t)) != 0
        || std::memcmp(fr, fr_modulus, sizeof(fr_t)) != 0
        || std::memcmp(fr + 4, &fr_one, sizeof(fr_t)) != 0
        || std::memcmp(fr + 8, fr_r2, sizeof(fr_t)) != 0;
}
#endif
