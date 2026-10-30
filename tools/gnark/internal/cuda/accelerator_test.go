//go:build cuda

package cuda

import (
	"fmt"
	"math/big"
	"os"
	"slices"
	"strconv"
	"sync"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/iop"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	native "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

func gpuConfig(t *testing.T) Config {
	t.Helper()
	if os.Getenv("IX_PLONK_CUDA_TEST") != "1" {
		t.Skip("set IX_PLONK_CUDA_TEST=1 for bounded native CUDA tests")
	}
	config := Config{MemoryBytes: 8 << 30, HeadroomBytes: 8 << 30}
	if value := os.Getenv("IX_PLONK_CUDA_DEVICE"); value != "" {
		device, err := strconv.Atoi(value)
		if err != nil {
			t.Fatal(err)
		}
		config.Device = device
	}
	return config
}

func shiftedSRS(count int) *kzg.SRS {
	_, _, g1, g2 := curve.Generators()
	var tau, power fr.Element
	tau.SetUint64(7)
	power = tau
	srs := &kzg.SRS{Pk: kzg.ProvingKey{G1: make([]curve.G1Affine, count)}}
	var scalar big.Int
	for i := range srs.Pk.G1 {
		power.BigInt(&scalar)
		srs.Pk.G1[i].ScalarMultiplication(&g1, &scalar)
		power.Mul(&power, &tau)
	}
	srs.Vk.G1 = srs.Pk.G1[0]
	srs.Vk.G2[0] = g2
	srs.Vk.G2[1].ScalarMultiplication(&g2, big.NewInt(7))
	for i := range srs.Vk.G2 {
		srs.Vk.Lines[i] = curve.PrecomputeLines(srs.Vk.G2[i])
	}
	return srs
}

func kernelKey(t *testing.T, n int) *native.ProvingKey {
	t.Helper()
	srs := shiftedSRS(n + 3)
	lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:n])
	if err != nil {
		t.Fatal(err)
	}
	return &native.ProvingKey{Kzg: srs.Pk, KzgLagrange: kzg.ProvingKey{G1: lagrange}, Vk: &native.VerifyingKey{Size: uint64(n), Kzg: srs.Vk}}
}

func attachForTest(t *testing.T, pk *native.ProvingKey) *Accelerator {
	t.Helper()
	accelerator, err := Attach(pk, gpuConfig(t))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := accelerator.Close(); err != nil {
			t.Error(err)
		}
	})
	return accelerator
}

func TestCUDAMSMRangesTailsConcurrencyAndLifecycle(t *testing.T) {
	gpuConfig(t)
	pk := kernelKey(t, 64)
	a := attachForTest(t, pk)
	for _, basis := range [][]curve.G1Affine{pk.Kzg.G1, pk.KzgLagrange.G1} {
		for _, span := range [][2]int{{0, len(basis)}, {2, 17}, {len(basis) - 4, 4}, {len(basis) - 3, 3}, {0, 0}} {
			points := basis[span[0] : span[0]+span[1]]
			scalars := make([]fr.Element, len(points))
			for i := range scalars {
				scalars[i].SetUint64(uint64(11*i + 1))
			}
			var want curve.G1Affine
			if _, err := want.MultiExp(points, scalars, ecc.MultiExpConfig{}); err != nil {
				t.Fatal(err)
			}
			got, err := a.MultiExp(points, scalars)
			if err != nil || !got.Equal(&want) {
				t.Fatalf("MSM span %v differs: %v", span, err)
			}
		}
	}
	zeros := make([]fr.Element, 64)
	result, err := a.MultiExp(pk.Kzg.G1[:64], zeros)
	if err != nil || !result.IsInfinity() {
		t.Fatalf("zero MSM: %v", err)
	}
	zeros[0].SetUint64(7)
	zeros[1].SetInt64(-1)
	result, err = a.MultiExp(pk.Kzg.G1[:64], zeros)
	if err != nil || !result.IsInfinity() {
		t.Fatalf("cancelled MSM: %v", err)
	}
	if _, err := a.MultiExp(append([]curve.G1Affine(nil), pk.Kzg.G1[:4]...), zeros[:4]); err == nil {
		t.Fatal("accepted copied unregistered bases")
	}
	if _, err := a.MultiExp(pk.Kzg.G1[:4], zeros[:3]); err == nil {
		t.Fatal("accepted mismatched MSM lengths")
	}
	var wait sync.WaitGroup
	errors := make(chan error, 4)
	for i := range 4 {
		wait.Add(1)
		go func(offset int) {
			defer wait.Done()
			points := pk.Kzg.G1[offset : offset+32]
			scalars := make([]fr.Element, 32)
			for j := range scalars {
				scalars[j].SetUint64(uint64(j + offset + 2))
			}
			var want curve.G1Affine
			if _, err := want.MultiExp(points, scalars, ecc.MultiExpConfig{}); err != nil {
				errors <- err
				return
			}
			got, err := a.MultiExp(points, scalars)
			if err != nil {
				errors <- err
			} else if !got.Equal(&want) {
				errors <- fmt.Errorf("concurrent MSM mismatch")
			}
		}(i)
	}
	wait.Wait()
	close(errors)
	for err := range errors {
		t.Error(err)
	}
	stats, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	if stats.MSMCalls == 0 || stats.CPUTailPoints == 0 || stats.SmallCPUCalls == 0 {
		t.Fatalf("missing dispatch evidence: %+v", stats)
	}
	if stats.MSMCallbackSeconds <= 0 || stats.QueueWaitSeconds < 0 {
		t.Fatalf("invalid callback timing: %+v", stats)
	}
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	finalStats, err := a.Stats()
	if err != nil || finalStats.MSMCallbackSeconds != stats.MSMCallbackSeconds || finalStats.QueueWaitSeconds != stats.QueueWaitSeconds {
		t.Fatalf("callback timings changed at close: %+v, %v", finalStats, err)
	}
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	if pk.Accelerator() != nil {
		t.Fatal("closed accelerator is still attached")
	}
	if _, err := a.MultiExp(pk.Kzg.G1[:4], zeros[:4]); err == nil {
		t.Fatal("accepted MSM after close")
	}
}

func TestCUDAFFTCanonicalFormsAndRoots(t *testing.T) {
	gpuConfig(t)
	a := attachForTest(t, kernelKey(t, 64))
	for _, n := range []int{2, 8, 64, 512, 4096} {
		domain := fft.NewDomain(uint64(n))
		coefficients := make([]fr.Element, n)
		for i := range coefficients {
			coefficients[i].SetUint64(uint64(i*i + 3*i + 9))
		}
		for _, coset := range []bool{false, true} {
			for _, reversed := range []bool{false, true} {
				values := append([]fr.Element(nil), coefficients...)
				p := iop.NewPolynomial(&values, iop.Form{Basis: iop.Canonical, Layout: iop.Regular})
				if coset {
					p.ToLagrangeCoset(domain).ToRegular()
				} else {
					p.ToLagrange(domain).ToRegular()
				}
				if reversed {
					fft.BitReverse(p.Coefficients())
					p.Layout = iop.BitReverse
				}
				want := p.Clone().ToCanonical(domain).ToRegular()
				if err := a.ToCanonical(domain, p); err != nil {
					t.Fatal(err)
				}
				if p.Basis != iop.Canonical || p.Layout != iop.Regular || !slices.Equal(p.Coefficients(), want.Coefficients()) || !slices.Equal(p.Coefficients(), coefficients) {
					t.Fatalf("N=%d coset=%t reversed=%t inverse differs", n, coset, reversed)
				}
			}
			got := append([]fr.Element(nil), coefficients...)
			shift := fr.One()
			wantValues := append([]fr.Element(nil), coefficients...)
			want := iop.NewPolynomial(&wantValues, iop.Form{Basis: iop.Canonical, Layout: iop.Regular})
			if coset {
				shift = domain.FrMultiplicativeGen
				want.ToLagrangeCoset(domain).ToRegular()
			} else {
				want.ToLagrange(domain).ToRegular()
			}
			if err := a.withContext(func(context *nativeContext) error { return context.fft(got, false, false, shift) }); err != nil {
				t.Fatal(err)
			}
			if !slices.Equal(got, want.Coefficients()) {
				t.Fatalf("N=%d coset=%t forward differs", n, coset)
			}
		}
	}
	stats, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	if stats.FFTCalls == 0 {
		t.Fatal("FFT tests dispatched no CUDA FFTs")
	}
}

func numeratorFixture(n, rho, commitments int) (*native.NumeratorInput, [][]fr.Element) {
	domain := fft.NewDomain(uint64(n))
	in := &native.NumeratorInput{Domain0: domain, Domain1: fft.NewDomain(uint64(n * rho))}
	in.Alpha.SetUint64(19)
	in.Beta.SetUint64(23)
	in.Gamma.SetUint64(29)
	var canonical [][]fr.Element
	polynomials := make([]*iop.Polynomial, 12+2*commitments)
	for slot := range polynomials {
		coefficients := make([]fr.Element, n)
		for i := range coefficients {
			coefficients[i].SetUint64(uint64(3 + slot*17 + i*i + slot*i))
		}
		canonical = append(canonical, append([]fr.Element(nil), coefficients...))
		polynomials[slot] = iop.NewPolynomial(&coefficients, iop.Form{Basis: iop.Canonical, Layout: iop.Regular}).ToLagrange(domain).ToRegular()
	}
	in.L, in.R, in.O, in.Z, in.Qk = polynomials[0], polynomials[1], polynomials[2], polynomials[3], polynomials[4]
	in.Ql, in.Qr, in.Qm, in.Qo = polynomials[5], polynomials[6], polynomials[7], polynomials[8]
	in.S1, in.S2, in.S3 = polynomials[9], polynomials[10], polynomials[11]
	for i := range commitments {
		in.Qcp = append(in.Qcp, polynomials[12+2*i])
		in.Pi = append(in.Pi, polynomials[13+2*i])
	}
	blinder := func(values ...uint64) *iop.Polynomial {
		coefficients := make([]fr.Element, len(values))
		for i := range coefficients {
			coefficients[i].SetUint64(values[i])
		}
		return iop.NewPolynomial(&coefficients, iop.Form{Basis: iop.Canonical, Layout: iop.Regular})
	}
	in.Bl, in.Br, in.Bo, in.Bz = blinder(31, 37), blinder(41, 43), blinder(47, 53), blinder(59, 61, 67)
	return in, canonical
}

func evaluate(coefficients []fr.Element, x fr.Element) fr.Element {
	var value fr.Element
	for i := len(coefficients) - 1; i >= 0; i-- {
		value.Mul(&value, &x).Add(&value, &coefficients[i])
	}
	return value
}

func numeratorOracle(in *native.NumeratorInput, canonical [][]fr.Element) []fr.Element {
	result := make([]fr.Element, int(in.Domain1.Cardinality))
	x := in.Domain1.FrMultiplicativeGen
	one := fr.One()
	for row := range result {
		values := make([]fr.Element, len(canonical))
		for i := range canonical {
			values[i] = evaluate(canonical[i], x)
		}
		var zh, shiftedX, shiftedZ fr.Element
		zh.Exp(x, new(big.Int).SetUint64(in.Domain0.Cardinality)).Sub(&zh, &one)
		shiftedX.Mul(&x, &in.Domain0.Generator)
		shiftedZ = evaluate(canonical[3], shiftedX)
		blinders := []*iop.Polynomial{in.Bl, in.Br, in.Bo, in.Bz}
		for i, p := range blinders {
			b := evaluate(p.Coefficients(), x)
			b.Mul(&b, &zh)
			values[i].Add(&values[i], &b)
		}
		b := evaluate(in.Bz.Coefficients(), shiftedX)
		b.Mul(&b, &zh)
		shiftedZ.Add(&shiftedZ, &b)
		var gate, tmp fr.Element
		gate.Mul(&values[5], &values[0])
		tmp.Mul(&values[6], &values[1])
		gate.Add(&gate, &tmp)
		tmp.Mul(&values[7], &values[0]).Mul(&tmp, &values[1])
		gate.Add(&gate, &tmp)
		tmp.Mul(&values[8], &values[2])
		gate.Add(&gate, &tmp).Add(&gate, &values[4])
		for i := range in.Pi {
			tmp.Mul(&values[12+2*i], &values[13+2*i])
			gate.Add(&gate, &tmp)
		}
		left, right := shiftedZ, values[3]
		identity := x
		for i := range 3 {
			tmp.Mul(&in.Beta, &values[9+i]).Add(&tmp, &values[i]).Add(&tmp, &in.Gamma)
			left.Mul(&left, &tmp)
			tmp.Mul(&in.Beta, &identity).Add(&tmp, &values[i]).Add(&tmp, &in.Gamma)
			right.Mul(&right, &tmp)
			identity.Mul(&identity, &in.Domain1.FrMultiplicativeGen)
		}
		var ordering, boundary, denominator fr.Element
		ordering.Sub(&left, &right)
		denominator.Sub(&x, &one)
		boundary.Div(&zh, &denominator).Mul(&boundary, &in.Domain0.CardinalityInv)
		tmp.Sub(&values[3], &one)
		boundary.Mul(&boundary, &tmp)
		boundary.Mul(&boundary, &in.Alpha).Add(&boundary, &ordering).Mul(&boundary, &in.Alpha).Add(&boundary, &gate)
		result[row] = boundary
		x.Mul(&x, &in.Domain1.Generator)
	}
	return result
}

func TestCUDANumeratorAgainstDirectOracle(t *testing.T) {
	gpuConfig(t)
	for _, shape := range [][3]int{{2, 8, 0}, {4, 8, 1}, {8, 4, 0}, {16, 4, 1}, {32, 4, 2}} {
		n, rho, commitments := shape[0], shape[1], shape[2]
		t.Run(fmt.Sprint(shape), func(t *testing.T) {
			a := attachForTest(t, kernelKey(t, n))
			in, canonical := numeratorFixture(n, rho, commitments)
			blinds := [][]fr.Element{append([]fr.Element(nil), in.Bl.Coefficients()...), append([]fr.Element(nil), in.Br.Coefficients()...), append([]fr.Element(nil), in.Bo.Coefficients()...), append([]fr.Element(nil), in.Bz.Coefficients()...)}
			want := numeratorOracle(in, canonical)
			fft.BitReverse(want)
			got, err := a.ComputeNumerator(in)
			if err != nil {
				t.Fatal(err)
			}
			if !slices.Equal(got.Coefficients(), want) {
				t.Fatal("numerator differs from direct oracle")
			}
			if got.Form != (iop.Form{Basis: iop.LagrangeCoset, Layout: iop.BitReverse}) {
				t.Fatalf("false result form: %+v", got.Form)
			}
			for i, p := range numeratorPolynomials(in) {
				if p.Basis != iop.Canonical || p.Layout != iop.Regular || !slices.Equal(p.Coefficients(), canonical[i]) {
					t.Fatalf("input %d not restored", i)
				}
			}
			for i, p := range []*iop.Polynomial{in.Bl, in.Br, in.Bo, in.Bz} {
				if p.Basis != iop.Canonical || p.Layout != iop.Regular || !slices.Equal(p.Coefficients(), blinds[i]) {
					t.Fatalf("blinding polynomial %d changed", i)
				}
			}
			stats, err := a.Stats()
			if err != nil {
				t.Fatal(err)
			}
			if stats.NumeratorCalls != 1 {
				t.Fatalf("wrong numerator dispatch: %+v", stats)
			}
		})
	}
}

func TestCUDARejectsMalformedInputBeforeMutation(t *testing.T) {
	config := gpuConfig(t)
	pk := kernelKey(t, 16)
	a := attachForTest(t, pk)
	before, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	for _, mutate := range []func(*native.NumeratorInput){
		func(in *native.NumeratorInput) { in.Pi = nil },
		func(in *native.NumeratorInput) { in.L.Layout = iop.BitReverse },
		func(in *native.NumeratorInput) { in.R = in.L },
		func(in *native.NumeratorInput) { in.Domain1.Generator.SetOne() },
		func(in *native.NumeratorInput) { in.Domain1.FrMultiplicativeGen.SetZero() },
		func(in *native.NumeratorInput) { in.Bl.Basis = iop.Lagrange },
	} {
		in, _ := numeratorFixture(16, 4, 1)
		domainCopy := *in.Domain1
		in.Domain1 = &domainCopy
		mutate(in)
		original := append([]fr.Element(nil), in.L.Coefficients()...)
		if _, err := a.ComputeNumerator(in); err == nil {
			t.Fatal("accepted malformed numerator input")
		}
		if !slices.Equal(original, in.L.Coefficients()) {
			t.Fatal("rejected input was mutated")
		}
	}
	after, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	if after.MSMCalls != before.MSMCalls || after.FFTCalls != before.FFTCalls || after.NumeratorCalls != before.NumeratorCalls {
		t.Fatal("malformed input reached a native computation")
	}
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	config.MemoryBytes = 1
	if unexpected, err := Attach(pk, config); err == nil {
		unexpected.Close()
		t.Fatal("accepted insufficient device budget")
	}
}

type proofCircuit struct {
	Claim       [2]frontend.Variable `gnark:",public"`
	X, Y        frontend.Variable
	Commitments int `gnark:"-"`
}

func (c *proofCircuit) Define(api frontend.API) error {
	api.AssertIsEqual(api.Mul(c.X, c.X), c.Claim[0])
	api.AssertIsEqual(api.Mul(c.Y, c.Y), c.Claim[1])
	for i := range c.Commitments {
		value := api.Add(c.X, api.Mul(c.Y, i+1))
		challenge, err := api.(frontend.Committer).Commit(value)
		if err != nil {
			return err
		}
		api.AssertIsDifferent(challenge, 0)
	}
	return nil
}

func TestCUDAShiftedPLONKProofsVerifyOnCPU(t *testing.T) {
	gpuConfig(t)
	for commitments := range 3 {
		ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &proofCircuit{Commitments: commitments})
		if err != nil {
			t.Fatal(err)
		}
		if len(ccs.GetCommitments().CommitmentIndexes()) != commitments {
			t.Fatalf("fixture compiled %d commitments instead of %d", len(ccs.GetCommitments().CommitmentIndexes()), commitments)
		}
		n := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables()))
		srs := shiftedSRS(int(n) + 3)
		lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:int(n)])
		if err != nil {
			t.Fatal(err)
		}
		pk, vk, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: lagrange}, Vk: srs.Vk})
		if err != nil {
			t.Fatal(err)
		}
		w, err := frontend.NewWitness(&proofCircuit{Claim: [2]frontend.Variable{49, 121}, X: 7, Y: 11, Commitments: commitments}, ecc.BN254.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		public, err := frontend.NewWitness(&proofCircuit{Claim: [2]frontend.Variable{49, 121}}, ecc.BN254.ScalarField(), frontend.PublicOnly())
		if err != nil {
			t.Fatal(err)
		}
		wrong, err := frontend.NewWitness(&proofCircuit{Claim: [2]frontend.Variable{50, 121}}, ecc.BN254.ScalarField(), frontend.PublicOnly())
		if err != nil {
			t.Fatal(err)
		}
		for _, zk := range []bool{false, true} {
			opts := []backend.ProverOption{solidity.WithProverTargetSolidityVerifier(backend.PLONK)}
			if zk {
				opts = append(opts, backend.WithStatisticalZeroKnowledge())
			}
			cpu, err := plonk.Prove(ccs, pk, w, opts...)
			if err != nil {
				t.Fatal(err)
			}
			if err := plonk.Verify(cpu, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
				t.Fatal(err)
			}
			t.Run(fmt.Sprintf("commitments%d-zk%t", commitments, zk), func(t *testing.T) {
				a := attachForTest(t, pk.(*native.ProvingKey))
				proof, err := plonk.Prove(ccs, pk, w, opts...)
				if err != nil {
					t.Fatal(err)
				}
				if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
					t.Fatal(err)
				}
				if err := plonk.Verify(proof, vk, wrong, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
					t.Fatal("accepted wrong expected public inputs")
				}
				stats, err := a.Stats()
				if err != nil {
					t.Fatal(err)
				}
				if stats.MSMCalls == 0 || stats.FFTCalls == 0 || stats.NumeratorCalls != 1 {
					t.Fatalf("proof dispatched incorrectly: %+v", stats)
				}
			})
		}
	}
}
