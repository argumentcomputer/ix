#ifndef IX_PLONK_BLS12_381_H
#define IX_PLONK_BLS12_381_H

#include <stdint.h>

#if defined(__GNUC__)
#pragma GCC visibility push(default)
#endif
#ifdef __cplusplus
extern "C" {
#endif

#define IX_PLONK_BLS12_381_MAX_MSM_POINTS (UINT64_C(1) << 25)

typedef struct { uint64_t limbs[4]; } ix_plonk_bls12_381_fr;
typedef struct { uint64_t limbs[6]; } ix_plonk_bls12_381_fq;
typedef struct { ix_plonk_bls12_381_fq x, y; } ix_plonk_bls12_381_affine;
/* Jacobian affine coordinates are (X/Z^2,Y/Z^3); Z=0 is infinity. */
typedef struct { ix_plonk_bls12_381_fq x, y, z; } ix_plonk_bls12_381_jacobian;
typedef struct ix_plonk_bls12_381_context ix_plonk_bls12_381_context;
typedef uint64_t ix_plonk_bls12_381_basis;
typedef uint64_t ix_plonk_bls12_381_quotient;

enum ix_plonk_bls12_381_status {
    IX_PLONK_BLS12_381_OK = 0,
    IX_PLONK_BLS12_381_INVALID = 1,
    IX_PLONK_BLS12_381_UNSUPPORTED = 2,
    IX_PLONK_BLS12_381_MEMORY = 3,
    IX_PLONK_BLS12_381_RUNTIME = 4,
    IX_PLONK_BLS12_381_CANCELLED = 5,
    IX_PLONK_BLS12_381_POISONED = 6
};

typedef struct {
    int32_t code;
    char message[256];
} ix_plonk_bls12_381_error;

typedef struct {
    int32_t device;
    uint32_t msm_strategy;
    uint64_t budget_bytes;
    uint64_t driver_headroom_bytes;
} ix_plonk_bls12_381_config;

enum ix_plonk_bls12_381_msm_strategy {
    IX_PLONK_BLS12_381_MSM_SPLIT = 0,
    IX_PLONK_BLS12_381_MSM_MASK = 1
};

typedef struct {
    uint64_t n, m;
    uint32_t commitments;
    uint32_t reserved;
    ix_plonk_bls12_381_fr omega, omega_big, coset;
    ix_plonk_bls12_381_fr alpha, beta, gamma;
    ix_plonk_bls12_381_fr bl[2], br[2], bo[2], bz[3];
} ix_plonk_bls12_381_quotient_config;

typedef struct {
    uint64_t driver_free_bytes, driver_total_bytes;
    uint64_t pool_used_bytes, pool_used_high_bytes;
    uint64_t pool_reserved_bytes, pool_reserved_high_bytes;
    uint64_t accounted_bytes, accounted_high_bytes, budget_bytes;
    uint64_t msm_calls, fft_calls, numerator_calls;
    uint64_t upload_bytes, download_bytes;
    /* Successful logical transfers; each can contain multiple DMA chunks. */
    uint64_t upload_calls, download_calls;
    /* Inclusive boundaries: queued predecessor GPU work can delay transfers. */
    double upload_wall_ms, download_wall_ms;
    /* Existing ring events measure DMA only when transfer_timing_enabled=1. */
    double upload_dma_ms, download_dma_ms;
    uint64_t transfer_timing_enabled;
    /* Host staging copies are included in the transfer wall times. */
    double transfer_host_copy_ms;
    uint64_t masked_msm_calls, mask_sum_calls, mask_cache_hits;
    uint64_t split_msm_calls, split_unit_points;
    uint64_t split_max_bucket[32], split_chunk_count[32];
    uint64_t split_nonzero_digits[32], split_zero_digits[32];
    double split_classify_ms, split_chunks_ms, split_reduce_ms;
} ix_plonk_bls12_381_stats;

/* All field records contain reduced little-endian Montgomery limbs. */
int ix_plonk_bls12_381_check_field_abi(
    const uint64_t fq[3][6], const uint64_t fr[3][4],
    ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_ntt_parameters(uint32_t log_size,
    ix_plonk_bls12_381_fr *root, ix_plonk_bls12_381_fr *inverse_root,
    ix_plonk_bls12_381_fr *inverse_size, ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_context_create(const ix_plonk_bls12_381_config *config,
    ix_plonk_bls12_381_context **out, ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_context_destroy(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_context_cancel(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_get_stats(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_stats *out, ix_plonk_bls12_381_error *error);

int ix_plonk_bls12_381_basis_upload(ix_plonk_bls12_381_context *context,
    const ix_plonk_bls12_381_affine *points, uint64_t count,
    ix_plonk_bls12_381_basis *out, ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_basis_destroy(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_basis basis, ix_plonk_bls12_381_error *error);
/* Both strategies preserve the original scalar vector and resulting MSM. */
int ix_plonk_bls12_381_msm(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_basis basis, uint64_t point_offset,
    const ix_plonk_bls12_381_fr *scalars, uint64_t count,
    ix_plonk_bls12_381_jacobian *out, ix_plonk_bls12_381_error *error);

/* Regular or bit-reversed input, always regular output. coset is the FORWARD
 * coset multiplier in both directions; inverse transforms undo its powers. */
int ix_plonk_bls12_381_fft(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_fr *values, uint64_t count, uint32_t inverse,
    uint32_t input_bit_reversed, const ix_plonk_bls12_381_fr *coset,
    ix_plonk_bls12_381_error *error);

/* Slots: L,R,O,Z,Qk_complete,Ql,Qr,Qm,Qo,S1,S2,S3,Qcp0,Pi0,... .
 * put accepts Lagrange/regular input, replaces the host slice with canonical/
 * regular coefficients synchronously, and retains a private device copy.
 * Sessions support n>=2 and m/n=4 or 8, with m<=2^27 and <=16 commitments. */
int ix_plonk_bls12_381_quotient_begin(ix_plonk_bls12_381_context *context,
    const ix_plonk_bls12_381_quotient_config *config,
    ix_plonk_bls12_381_quotient *out, ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_quotient_put(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_quotient quotient, uint32_t slot,
    ix_plonk_bls12_381_fr *values, uint64_t count,
    ix_plonk_bls12_381_error *error);
/* Yields the numerator in LagrangeCoset/BitReverse form. */
int ix_plonk_bls12_381_quotient_finish(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_quotient quotient,
    ix_plonk_bls12_381_fr *output, uint64_t count,
    ix_plonk_bls12_381_error *error);
int ix_plonk_bls12_381_quotient_destroy(ix_plonk_bls12_381_context *context,
    ix_plonk_bls12_381_quotient quotient, ix_plonk_bls12_381_error *error);

#ifdef __cplusplus
}
#endif
#if defined(__GNUC__)
#pragma GCC visibility pop
#endif
#endif
