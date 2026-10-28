//go:build cuda

package cuda

/*
#cgo LDFLAGS: -lix_plonk_bn254_cuda -lstdc++
#include <ix_plonk_bn254.h>
*/
import "C"

import (
	"fmt"
	"math/big"
	"runtime"
	"strings"
	"unsafe"

	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fp"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

type nativeContext struct{ pointer *C.ix_plonk_bn254_context }
type basisHandle uint64
type quotientHandle uint64

type nativeParameters struct{ root, inverseRoot, inverseSize fr.Element }

type quotientConfig struct {
	n, m                                       uint64
	commitments                                int
	omega, omegaBig, coset, alpha, beta, gamma fr.Element
	bl, br, bo                                 [2]fr.Element
	bz                                         [3]fr.Element
}

func nativeError(operation string, status C.int, detail *C.ix_plonk_bn254_error) error {
	if status == 0 {
		return nil
	}
	message := C.GoBytes(unsafe.Pointer(&detail.message[0]), C.int(len(detail.message)))
	return fmt.Errorf("CUDA PLONK %s: status %d: %s", operation, int(status), strings.TrimRight(string(message), "\x00"))
}

func fieldRecord(modulus *big.Int, one [4]uint64) [3][4]uint64 {
	var result [3][4]uint64
	result[1] = one
	r2 := new(big.Int).Lsh(big.NewInt(1), 512)
	r2.Mod(r2, modulus)
	for index, value := range map[int]*big.Int{0: modulus, 2: r2} {
		var bytes [32]byte
		value.FillBytes(bytes[:])
		for limb := range 4 {
			for octet := range 8 {
				result[index][limb] |= uint64(bytes[31-8*limb-octet]) << (8 * octet)
			}
		}
	}
	return result
}

func checkFieldABI() error {
	var affine curve.G1Affine
	var jacobian curve.G1Jac
	var word uint64 = 1
	if *(*byte)(unsafe.Pointer(&word)) != 1 || unsafe.Sizeof(fr.Element{}) != 32 || unsafe.Sizeof(fp.Element{}) != 32 || unsafe.Alignof(fr.Element{}) != 8 || unsafe.Alignof(fp.Element{}) != 8 || unsafe.Sizeof(affine) != 64 || unsafe.Offsetof(affine.Y) != 32 || unsafe.Sizeof(jacobian) != 96 || unsafe.Offsetof(jacobian.Y) != 32 || unsafe.Offsetof(jacobian.Z) != 64 {
		return fmt.Errorf("CUDA PLONK requires the canonical little-endian Montgomery limb ABI")
	}
	fqRecord := fieldRecord(fp.Modulus(), [4]uint64(fp.One()))
	frRecord := fieldRecord(fr.Modulus(), [4]uint64(fr.One()))
	var detail C.ix_plonk_bn254_error
	return nativeError("field ABI", C.ix_plonk_bn254_check_field_abi(
		(*[4]C.uint64_t)(unsafe.Pointer(&fqRecord[0][0])),
		(*[4]C.uint64_t)(unsafe.Pointer(&frRecord[0][0])), &detail), &detail)
}

func getNativeParameters(logSize int) (nativeParameters, error) {
	var result nativeParameters
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_ntt_parameters(C.uint32_t(logSize),
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&result.root)),
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&result.inverseRoot)),
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&result.inverseSize)), &detail)
	return result, nativeError("NTT parameters", status, &detail)
}

func createNativeContext(config Config) (*nativeContext, error) {
	c := C.ix_plonk_bn254_config{
		device:                C.int32_t(config.Device),
		msm_strategy:          C.uint32_t(config.MSMStrategy),
		budget_bytes:          C.uint64_t(config.MemoryBytes),
		driver_headroom_bytes: C.uint64_t(config.HeadroomBytes),
	}
	var pointer *C.ix_plonk_bn254_context
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_context_create(&c, &pointer, &detail)
	if err := nativeError("context creation", status, &detail); err != nil {
		return nil, err
	}
	if pointer == nil {
		return nil, fmt.Errorf("CUDA PLONK returned an empty context")
	}
	return &nativeContext{pointer: pointer}, nil
}

func (c *nativeContext) close() error {
	var detail C.ix_plonk_bn254_error
	return nativeError("context destruction", C.ix_plonk_bn254_context_destroy(c.pointer, &detail), &detail)
}

func (c *nativeContext) uploadBasis(points []curve.G1Affine) (basisHandle, error) {
	var handle C.ix_plonk_bn254_basis
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_basis_upload(c.pointer,
		(*C.ix_plonk_bn254_affine)(unsafe.Pointer(&points[0])), C.uint64_t(len(points)), &handle, &detail)
	runtime.KeepAlive(points)
	return basisHandle(handle), nativeError("basis upload", status, &detail)
}

func checkedAffine(jacobian *curve.G1Jac) (curve.G1Affine, error) {
	if jacobian.Z.IsZero() {
		return curve.G1Affine{}, nil
	}
	if !jacobian.IsOnCurve() {
		return curve.G1Affine{}, fmt.Errorf("CUDA PLONK MSM returned an off-curve point")
	}
	var result curve.G1Affine
	result.FromJacobian(jacobian)
	return result, nil
}

func (c *nativeContext) msm(handle basisHandle, offset int, scalars []fr.Element) (curve.G1Affine, error) {
	var jacobian curve.G1Jac
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_msm(c.pointer, C.ix_plonk_bn254_basis(handle), C.uint64_t(offset),
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&scalars[0])), C.uint64_t(len(scalars)),
		(*C.ix_plonk_bn254_jacobian)(unsafe.Pointer(&jacobian)), &detail)
	runtime.KeepAlive(scalars)
	if err := nativeError("MSM", status, &detail); err != nil {
		return curve.G1Affine{}, err
	}
	return checkedAffine(&jacobian)
}

func (c *nativeContext) fft(values []fr.Element, inverse, bitReversed bool, coset fr.Element) error {
	var inverseFlag, reversedFlag C.uint32_t
	if inverse {
		inverseFlag = 1
	}
	if bitReversed {
		reversedFlag = 1
	}
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_fft(c.pointer, (*C.ix_plonk_bn254_fr)(unsafe.Pointer(&values[0])),
		C.uint64_t(len(values)), inverseFlag, reversedFlag,
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&coset)), &detail)
	runtime.KeepAlive(values)
	return nativeError("FFT", status, &detail)
}

func toNativeFr(value fr.Element) C.ix_plonk_bn254_fr {
	var result C.ix_plonk_bn254_fr
	for i := range 4 {
		result.limbs[i] = C.uint64_t(value[i])
	}
	return result
}

func (c *nativeContext) beginQuotient(config quotientConfig) (quotientHandle, error) {
	native := C.ix_plonk_bn254_quotient_config{
		n: C.uint64_t(config.n), m: C.uint64_t(config.m), commitments: C.uint32_t(config.commitments),
		omega: toNativeFr(config.omega), omega_big: toNativeFr(config.omegaBig), coset: toNativeFr(config.coset),
		alpha: toNativeFr(config.alpha), beta: toNativeFr(config.beta), gamma: toNativeFr(config.gamma),
	}
	for i := range 2 {
		native.bl[i] = toNativeFr(config.bl[i])
		native.br[i] = toNativeFr(config.br[i])
		native.bo[i] = toNativeFr(config.bo[i])
	}
	for i := range 3 {
		native.bz[i] = toNativeFr(config.bz[i])
	}
	var handle C.ix_plonk_bn254_quotient
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_quotient_begin(c.pointer, &native, &handle, &detail)
	return quotientHandle(handle), nativeError("quotient preparation", status, &detail)
}

func (c *nativeContext) putQuotient(handle quotientHandle, slot int, values []fr.Element) error {
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_quotient_put(c.pointer, C.ix_plonk_bn254_quotient(handle), C.uint32_t(slot),
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&values[0])), C.uint64_t(len(values)), &detail)
	runtime.KeepAlive(values)
	return nativeError("quotient polynomial upload", status, &detail)
}

func (c *nativeContext) finishQuotient(handle quotientHandle, values []fr.Element) error {
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_quotient_finish(c.pointer, C.ix_plonk_bn254_quotient(handle),
		(*C.ix_plonk_bn254_fr)(unsafe.Pointer(&values[0])), C.uint64_t(len(values)), &detail)
	runtime.KeepAlive(values)
	return nativeError("quotient computation", status, &detail)
}

func (c *nativeContext) destroyQuotient(handle quotientHandle) error {
	var detail C.ix_plonk_bn254_error
	return nativeError("quotient destruction", C.ix_plonk_bn254_quotient_destroy(c.pointer, C.ix_plonk_bn254_quotient(handle), &detail), &detail)
}

func (c *nativeContext) stats() (Stats, error) {
	var native C.ix_plonk_bn254_stats
	var detail C.ix_plonk_bn254_error
	status := C.ix_plonk_bn254_get_stats(c.pointer, &native, &detail)
	stats := Stats{
		DriverFreeBytes: uint64(native.driver_free_bytes), DriverTotalBytes: uint64(native.driver_total_bytes),
		PoolUsedBytes: uint64(native.pool_used_bytes), PoolUsedHighBytes: uint64(native.pool_used_high_bytes),
		PoolReservedBytes: uint64(native.pool_reserved_bytes), PoolReservedHighBytes: uint64(native.pool_reserved_high_bytes),
		AccountedBytes: uint64(native.accounted_bytes), AccountedHighBytes: uint64(native.accounted_high_bytes), BudgetBytes: uint64(native.budget_bytes),
		MSMCalls: uint64(native.msm_calls), FFTCalls: uint64(native.fft_calls), NumeratorCalls: uint64(native.numerator_calls),
		UploadBytes: uint64(native.upload_bytes), DownloadBytes: uint64(native.download_bytes),
		UploadCalls: uint64(native.upload_calls), DownloadCalls: uint64(native.download_calls),
		UploadWallMS: float64(native.upload_wall_ms), DownloadWallMS: float64(native.download_wall_ms),
		TransferHostCopyMS: float64(native.transfer_host_copy_ms),
		UploadDMAMS:        float64(native.upload_dma_ms), DownloadDMAMS: float64(native.download_dma_ms),
		TransferTimingEnabled: native.transfer_timing_enabled != 0,
		MaskedMSMCalls:        uint64(native.masked_msm_calls), MaskSumCalls: uint64(native.mask_sum_calls), MaskCacheHits: uint64(native.mask_cache_hits),
		SplitMSMCalls: uint64(native.split_msm_calls), SplitUnitPoints: uint64(native.split_unit_points),
		SplitClassifyMS: float64(native.split_classify_ms), SplitChunksMS: float64(native.split_chunks_ms), SplitReduceMS: float64(native.split_reduce_ms),
	}
	for i := range 32 {
		stats.SplitMaxBucket[i] = uint64(native.split_max_bucket[i])
		stats.SplitChunkCount[i] = uint64(native.split_chunk_count[i])
		stats.SplitNonzeroDigits[i] = uint64(native.split_nonzero_digits[i])
		stats.SplitZeroDigits[i] = uint64(native.split_zero_digits[i])
	}
	return stats, nativeError("statistics", status, &detail)
}
