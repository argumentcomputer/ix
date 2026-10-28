//go:build cuda

package cuda

import (
	"errors"
	"fmt"
	"math"
	"math/big"
	"math/bits"
	"os"
	"runtime"
	"sync"
	"time"
	"unsafe"

	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/iop"
	native "github.com/consensys/gnark/backend/plonk/bn254"
)

const AllFeatures = native.AcceleratorFeatureMSMV1 | native.AcceleratorFeatureToCanonicalV1 | native.AcceleratorFeatureNumeratorV1 | native.AcceleratorFeatureQuotientV1

type MSMStrategy uint32

const (
	MSMSplit MSMStrategy = iota
	MSMMask
)

func (strategy MSMStrategy) String() string {
	if strategy == MSMMask {
		return "mask"
	}
	return "split"
}

type Config struct {
	MSMStrategy                MSMStrategy
	Device                     int
	MemoryBytes, HeadroomBytes uint64
	Features                   native.AcceleratorFeatureFlagsV1
}

type Stats struct {
	DriverFreeBytes, DriverTotalBytes                                          uint64
	PoolUsedBytes, PoolUsedHighBytes, PoolReservedBytes, PoolReservedHighBytes uint64
	AccountedBytes, AccountedHighBytes, BudgetBytes                            uint64
	MSMCalls, FFTCalls, NumeratorCalls, QuotientCalls                          uint64
	UploadBytes, DownloadBytes                                                 uint64
	UploadCalls, DownloadCalls                                                 uint64
	// Wall times include waiting for queued predecessor GPU work.
	UploadWallMS, DownloadWallMS, TransferHostCopyMS                     float64
	UploadDMAMS, DownloadDMAMS                                           float64
	TransferTimingEnabled                                                bool
	SmallCPUCalls, CPUTailPoints                                         uint64
	MSMCallbackSeconds, CanonicalCallbackSeconds                         float64
	NumeratorCallbackSeconds, QuotientCallbackSeconds                    float64
	QueueWaitSeconds                                                     float64
	MaskedMSMCalls, MaskSumCalls, MaskCacheHits                          uint64
	SplitMSMCalls, SplitUnitPoints                                       uint64
	SplitMaxBucket, SplitChunkCount, SplitNonzeroDigits, SplitZeroDigits [32]uint64
	SplitClassifyMS, SplitChunksMS, SplitReduceMS                        float64
}

type registeredBasis struct {
	name       string
	points     []curve.G1Affine
	start, end uintptr
	cached     int
	handle     basisHandle
}

// Accelerator serializes mutable native workspaces. The proving key keeps both
// registered host arrays alive until every borrowed native call has returned.
type Accelerator struct {
	mu                                                              sync.Mutex
	pk                                                              *native.ProvingKey
	context                                                         *nativeContext
	bases                                                           [2]registeredBasis
	features                                                        native.AcceleratorFeatureFlagsV1
	domain                                                          uint64
	parameters                                                      [27]nativeParameters
	closed                                                          bool
	closeErr                                                        error
	finalStats                                                      Stats
	smallCPUCalls, cpuTailPoints                                    uint64
	msmSeconds, canonicalSeconds, numeratorSeconds, quotientSeconds float64
	queueWaitSeconds                                                float64
	trace                                                           bool
	strategy                                                        MSMStrategy
}

var _ native.Accelerator = (*Accelerator)(nil)
var _ native.AcceleratorFeaturesV1 = (*Accelerator)(nil)
var _ native.QuotientAcceleratorV1 = (*Accelerator)(nil)

func Attach(pk *native.ProvingKey, config Config) (*Accelerator, error) {
	if pk == nil || pk.Vk == nil || pk.Accelerator() != nil {
		return nil, fmt.Errorf("CUDA PLONK needs an unattached proving key")
	}
	n := pk.Vk.Size
	if n < 2 || n > 1<<24 || n&(n-1) != 0 || uint64(len(pk.Kzg.G1)) != n+3 || uint64(len(pk.KzgLagrange.G1)) != n {
		return nil, fmt.Errorf("CUDA PLONK requires N<=2^24 and exact N+3/N proving bases")
	}
	if config.Device < 0 || config.Device > math.MaxInt32 || config.Features & ^AllFeatures != 0 || config.MSMStrategy > MSMMask {
		return nil, fmt.Errorf("invalid CUDA PLONK device or features")
	}
	if config.MemoryBytes == 0 {
		config.MemoryBytes = 64 << 30
	}
	if config.HeadroomBytes == 0 {
		config.HeadroomBytes = 8 << 30
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	if err := checkFieldABI(); err != nil {
		return nil, err
	}
	a := &Accelerator{pk: pk, features: config.Features, domain: n, trace: os.Getenv("IX_PLONK_CUDA_TRACE") == "1", strategy: config.MSMStrategy}
	for logSize := range a.parameters {
		parameters, err := getNativeParameters(logSize)
		if err != nil {
			return nil, err
		}
		root, err := fft.Generator(uint64(1) << logSize)
		if err != nil {
			return nil, err
		}
		var inverse, size fr.Element
		inverse.Inverse(&root)
		size.SetUint64(uint64(1) << logSize).Inverse(&size)
		if parameters.root != root || parameters.inverseRoot != inverse || parameters.inverseSize != size {
			return nil, fmt.Errorf("CUDA PLONK NTT parameters differ at log size %d", logSize)
		}
		a.parameters[logSize] = parameters
	}
	context, err := createNativeContext(config)
	if err != nil {
		return nil, err
	}
	a.context = context
	for i, points := range [][]curve.G1Affine{pk.Kzg.G1, pk.KzgLagrange.G1} {
		handle, err := context.uploadBasis(points[:int(n)])
		if err != nil {
			return nil, errors.Join(err, context.close())
		}
		start := uintptr(unsafe.Pointer(&points[0]))
		end := start + uintptr(len(points))*unsafe.Sizeof(points[0])
		if end < start {
			return nil, errors.Join(fmt.Errorf("CUDA PLONK basis address overflow"), context.close())
		}
		a.bases[i] = registeredBasis{name: []string{"monomial", "lagrange"}[i], points: points, start: start, end: end, cached: int(n), handle: handle}
	}
	pk.SetAccelerator(a)
	return a, nil
}

func (a *Accelerator) FeaturesV1() native.AcceleratorFeatureFlagsV1 { return a.features }

func (a *Accelerator) withContext(fn func(*nativeContext) error) error {
	queued := time.Now()
	a.mu.Lock()
	defer a.mu.Unlock()
	if a.closed {
		return fmt.Errorf("CUDA PLONK accelerator is closed")
	}
	a.queueWaitSeconds += time.Since(queued).Seconds()
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	err := fn(a.context)
	runtime.KeepAlive(a.pk)
	return err
}

func (a *Accelerator) hostStats(stats Stats) Stats {
	stats.SmallCPUCalls, stats.CPUTailPoints = a.smallCPUCalls, a.cpuTailPoints
	stats.MSMCallbackSeconds, stats.CanonicalCallbackSeconds = a.msmSeconds, a.canonicalSeconds
	stats.NumeratorCallbackSeconds, stats.QuotientCallbackSeconds = a.numeratorSeconds, a.quotientSeconds
	stats.QueueWaitSeconds = a.queueWaitSeconds
	return stats
}

func (a *Accelerator) Close() error {
	a.mu.Lock()
	defer a.mu.Unlock()
	if a.closed {
		return a.closeErr
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	stats, statsErr := a.context.stats()
	a.finalStats = a.hostStats(stats)
	a.closeErr = errors.Join(statsErr, a.context.close())
	a.closed = true
	if a.pk.Accelerator() == native.Accelerator(a) {
		a.pk.SetAccelerator(nil)
	}
	a.bases = [2]registeredBasis{}
	a.context, a.pk = nil, nil
	return a.closeErr
}

func (a *Accelerator) Stats() (Stats, error) {
	a.mu.Lock()
	defer a.mu.Unlock()
	if a.closed {
		return a.finalStats, a.closeErr
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	stats, err := a.context.stats()
	return a.hostStats(stats), err
}

func (a *Accelerator) resolve(points []curve.G1Affine) (*registeredBasis, int, error) {
	start := uintptr(unsafe.Pointer(&points[0]))
	width := unsafe.Sizeof(points[0])
	end := start + uintptr(len(points))*width
	if end < start {
		return nil, 0, fmt.Errorf("CUDA PLONK MSM address overflow")
	}
	for i := range a.bases {
		basis := &a.bases[i]
		if start >= basis.start && end <= basis.end && (start-basis.start)%width == 0 {
			return basis, int((start - basis.start) / width), nil
		}
	}
	return nil, 0, fmt.Errorf("CUDA PLONK MSM uses an unregistered basis")
}

func (a *Accelerator) MultiExp(points []curve.G1Affine, scalars []fr.Element) (result curve.G1Affine, err error) {
	if len(points) != len(scalars) {
		return result, fmt.Errorf("CUDA PLONK MSM length mismatch")
	}
	err = a.withContext(func(context *nativeContext) (err error) {
		transfers := a.startTransferTrace(context)
		started := time.Now()
		fields := map[string]any{"count": len(points), "strategy": a.strategy.String()}
		defer func() {
			elapsed := time.Since(started).Seconds()
			a.msmSeconds += elapsed
			fields["elapsed_seconds"] = elapsed
			fields["failed"] = err != nil
			transfers.finish(context, fields)
			a.traceEvent("end", "msm", fields)
		}()
		if len(points) == 0 {
			a.traceEvent("start", "msm", fields)
			a.smallCPUCalls++
			return nil
		}
		basis, offset, err := a.resolve(points)
		if err != nil {
			return err
		}
		fields["basis"], fields["offset"] = basis.name, offset
		if len(points) <= 3 {
			fields["cpu_small"] = true
			a.traceEvent("start", "msm", fields)
			a.smallCPUCalls++
			_, err := result.MultiExp(points, scalars, ecc.MultiExpConfig{})
			return err
		}
		cached := min(len(points), max(0, basis.cached-offset))
		if len(points)-cached > 3 {
			return fmt.Errorf("CUDA PLONK MSM exceeds its cached range and tail")
		}
		if cached > 0 {
			a.traceEvent("start", "msm", fields)
			result, err = context.msm(basis.handle, offset, scalars[:cached])
			if err != nil {
				return err
			}
		}
		if cached < len(points) {
			var tail curve.G1Affine
			if _, err := tail.MultiExp(points[cached:], scalars[cached:], ecc.MultiExpConfig{}); err != nil {
				return err
			}
			result.Add(&result, &tail)
			a.cpuTailPoints += uint64(len(points) - cached)
		}
		return nil
	})
	runtime.KeepAlive(points)
	runtime.KeepAlive(scalars)
	return
}

func (a *Accelerator) checkDomain(domain *fft.Domain) error {
	if domain == nil || domain.Cardinality < 2 || domain.Cardinality > 1<<26 || domain.Cardinality&(domain.Cardinality-1) != 0 {
		return fmt.Errorf("unsupported CUDA PLONK domain")
	}
	parameters := a.parameters[bits.TrailingZeros64(domain.Cardinality)]
	if domain.Generator != parameters.root || domain.GeneratorInv != parameters.inverseRoot || domain.CardinalityInv != parameters.inverseSize {
		return fmt.Errorf("CUDA PLONK domain parameters differ")
	}
	return nil
}

func (a *Accelerator) ToCanonical(domain *fft.Domain, p *iop.Polynomial) error {
	if err := a.checkDomain(domain); err != nil {
		return err
	}
	if p == nil || uint64(len(p.Coefficients())) != domain.Cardinality || (p.Basis != iop.Lagrange && p.Basis != iop.LagrangeCoset) || (p.Layout != iop.Regular && p.Layout != iop.BitReverse) {
		return fmt.Errorf("unsupported CUDA PLONK canonical conversion input")
	}
	coset := fr.One()
	if p.Basis == iop.LagrangeCoset {
		coset = domain.FrMultiplicativeGen
	}
	if coset.IsZero() {
		return fmt.Errorf("zero CUDA PLONK coset")
	}
	return a.withContext(func(context *nativeContext) (err error) {
		transfers := a.startTransferTrace(context)
		started := time.Now()
		fields := map[string]any{"count": len(p.Coefficients())}
		a.traceEvent("start", "canonical", fields)
		defer func() {
			elapsed := time.Since(started).Seconds()
			a.canonicalSeconds += elapsed
			fields["elapsed_seconds"] = elapsed
			fields["failed"] = err != nil
			transfers.finish(context, fields)
			a.traceEvent("end", "canonical", fields)
		}()
		if err := context.fft(p.Coefficients(), true, p.Layout == iop.BitReverse, coset); err != nil {
			return err
		}
		p.Basis, p.Layout = iop.Canonical, iop.Regular
		return nil
	})
}

func numeratorPolynomials(in *native.NumeratorInput) []*iop.Polynomial {
	result := []*iop.Polynomial{in.L, in.R, in.O, in.Z, in.Qk, in.Ql, in.Qr, in.Qm, in.Qo, in.S1, in.S2, in.S3}
	for i := range in.Qcp {
		result = append(result, in.Qcp[i], in.Pi[i])
	}
	return result
}

func (a *Accelerator) numeratorConfig(in *native.NumeratorInput) (quotientConfig, error) {
	var config quotientConfig
	if in == nil {
		return config, fmt.Errorf("missing CUDA PLONK numerator input")
	}
	if err := a.checkDomain(in.Domain0); err != nil {
		return config, err
	}
	if err := a.checkDomain(in.Domain1); err != nil {
		return config, err
	}
	n, m := in.Domain0.Cardinality, in.Domain1.Cardinality
	if n != a.domain || n > 1<<24 || m%n != 0 || (m/n != 4 && m/n != 8) || len(in.Qcp) != len(in.Pi) || len(in.Qcp) > 16 {
		return config, fmt.Errorf("unsupported CUDA PLONK quotient shape")
	}
	var root fr.Element
	root.Exp(in.Domain1.Generator, new(big.Int).SetUint64(m/n))
	if root != in.Domain0.Generator || in.Domain0.FrMultiplicativeGen != in.Domain1.FrMultiplicativeGen || in.Domain1.FrMultiplicativeGen.IsZero() {
		return config, fmt.Errorf("CUDA PLONK quotient roots or cosets differ")
	}
	config = quotientConfig{n: n, m: m, commitments: len(in.Qcp), omega: in.Domain0.Generator, omegaBig: in.Domain1.Generator, coset: in.Domain1.FrMultiplicativeGen, alpha: in.Alpha, beta: in.Beta, gamma: in.Gamma}
	var ranges [][2]uintptr
	for _, polynomial := range numeratorPolynomials(in) {
		if polynomial == nil || uint64(len(polynomial.Coefficients())) != n || polynomial.Basis != iop.Lagrange || polynomial.Layout != iop.Regular {
			return config, fmt.Errorf("CUDA PLONK numerator requires Lagrange/regular inputs of size N")
		}
		start := uintptr(unsafe.Pointer(&polynomial.Coefficients()[0]))
		end := start + uintptr(n)*unsafe.Sizeof(fr.Element{})
		if end < start {
			return config, fmt.Errorf("CUDA PLONK polynomial address overflow")
		}
		for _, prior := range ranges {
			if start < prior[1] && end > prior[0] {
				return config, fmt.Errorf("aliased CUDA PLONK numerator inputs")
			}
		}
		ranges = append(ranges, [2]uintptr{start, end})
	}
	for _, blind := range []struct {
		p   *iop.Polynomial
		out []fr.Element
	}{{in.Bl, config.bl[:]}, {in.Br, config.br[:]}, {in.Bo, config.bo[:]}, {in.Bz, config.bz[:]}} {
		if blind.p == nil || len(blind.p.Coefficients()) < 1 || len(blind.p.Coefficients()) > len(blind.out) || blind.p.Basis != iop.Canonical || blind.p.Layout != iop.Regular {
			return config, fmt.Errorf("invalid CUDA PLONK blinding polynomial")
		}
		copy(blind.out, blind.p.Coefficients())
	}
	return config, nil
}

func (a *Accelerator) compute(in *native.NumeratorInput, fused bool) (*iop.Polynomial, error) {
	config, err := a.numeratorConfig(in)
	if err != nil {
		return nil, err
	}
	var output []fr.Element
	err = a.withContext(func(context *nativeContext) (err error) {
		transfers := a.startTransferTrace(context)
		started := time.Now()
		operation := "numerator"
		if fused {
			operation = "quotient"
		}
		fields := map[string]any{"n": config.n, "m": config.m, "commitments": config.commitments}
		a.traceEvent("start", operation, fields)
		defer func() {
			elapsed := time.Since(started).Seconds()
			fields["elapsed_seconds"] = elapsed
			fields["failed"] = err != nil
			if fused {
				a.quotientSeconds += elapsed
			} else {
				a.numeratorSeconds += elapsed
			}
			transfers.finish(context, fields)
			a.traceEvent("end", operation, fields)
		}()
		handle, err := context.beginQuotient(config)
		if err != nil {
			return err
		}
		defer func() { err = errors.Join(err, context.destroyQuotient(handle)) }()
		for index, polynomial := range numeratorPolynomials(in) {
			if err := context.putQuotient(handle, index, polynomial.Coefficients()); err != nil {
				return err
			}
			polynomial.Basis, polynomial.Layout = iop.Canonical, iop.Regular
		}
		output = make([]fr.Element, int(config.m))
		return context.finishQuotient(handle, fused, output)
	})
	if err != nil {
		return nil, err
	}
	form := iop.Form{Basis: iop.LagrangeCoset, Layout: iop.BitReverse}
	if fused {
		form = iop.Form{Basis: iop.Canonical, Layout: iop.Regular}
	}
	return iop.NewPolynomial(&output, form), nil
}

func (a *Accelerator) ComputeNumerator(in *native.NumeratorInput) (*iop.Polynomial, error) {
	return a.compute(in, false)
}
func (a *Accelerator) ComputeQuotientV1(in *native.NumeratorInput) (*iop.Polynomial, error) {
	return a.compute(in, true)
}
