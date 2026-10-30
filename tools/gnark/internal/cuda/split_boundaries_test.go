//go:build cuda

package cuda

import (
	"fmt"
	"math/big"
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	native "github.com/consensys/gnark/backend/plonk/bn254"
)

func splitBoundaryKey(n int) *native.ProvingKey {
	_, _, generator, _ := curve.Generators()
	var negativeGenerator curve.G1Affine
	negativeGenerator.Neg(&generator)
	pattern := make([]curve.G1Affine, 263)
	for i := range pattern {
		if i%17 == 0 {
			continue
		}
		scalar := big.NewInt(int64((i+1)*(i+1)*(i+1) + 11))
		pattern[i].ScalarMultiplication(&generator, scalar)
		if i%7 == 0 {
			pattern[i].Neg(&pattern[i])
		}
	}
	pk := &native.ProvingKey{
		Kzg:         kzg.ProvingKey{G1: make([]curve.G1Affine, n+3)},
		KzgLagrange: kzg.ProvingKey{G1: make([]curve.G1Affine, n)},
		Vk:          &native.VerifyingKey{Size: uint64(n)},
	}
	for i := range pk.Kzg.G1 {
		pk.Kzg.G1[i] = pattern[i%len(pattern)]
	}
	for i := range pk.KzgLagrange.G1 {
		pk.KzgLagrange.G1[i] = pattern[(17*i+7)%len(pattern)]
	}
	// Equal, inverse, and infinity partials exercise every projective addition
	// branch. These are kernel test bases, not a polynomial commitment setup.
	for i := range 256 {
		pk.Kzg.G1[i] = generator
		pk.Kzg.G1[i+256] = negativeGenerator
		pk.Kzg.G1[i+512] = curve.G1Affine{}
	}
	return pk
}

func checkSplitMSM(t *testing.T, accelerator *Accelerator, points []curve.G1Affine, scalars []fr.Element) {
	t.Helper()
	original := slices.Clone(scalars)
	var want curve.G1Affine
	if _, err := want.MultiExp(points, scalars, ecc.MultiExpConfig{}); err != nil {
		t.Fatal(err)
	}
	got, err := accelerator.MultiExp(points, scalars)
	if err != nil {
		t.Fatal(err)
	}
	if !got.Equal(&want) {
		t.Fatal("split-bucket MSM differs from the complete CPU MSM")
	}
	if !slices.Equal(scalars, original) {
		t.Fatal("split-bucket MSM changed caller scalars")
	}
}

func TestCUDASplitBucketBoundariesAndSignedDigits(t *testing.T) {
	config := gpuConfig(t)
	if config.MSMStrategy != MSMSplit {
		t.Fatal("default CUDA MSM policy is not split-bucket accumulation")
	}
	const domain = 1 << 17
	pk := splitBoundaryKey(domain)
	a, err := Attach(pk, config)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := a.Close(); err != nil {
			t.Error(err)
		}
	})
	var high fr.Element
	high.SetBigInt(new(big.Int).Lsh(big.NewInt(1), 252))
	for _, count := range []int{255, 256, 257, 511, 512, 513, 65535, 65536, 65537} {
		for _, kind := range []string{"positive", "negative", "top-window"} {
			t.Run(fmt.Sprintf("count_%d/%s", count, kind), func(t *testing.T) {
				values := make([]fr.Element, count)
				for i := range values {
					switch kind {
					case "positive":
						values[i].SetUint64(2)
					case "negative":
						values[i].SetInt64(-2)
					case "top-window":
						values[i] = high
					}
				}
				checkSplitMSM(t, a, pk.Kzg.G1[:count], values)
			})
		}
	}
	for _, kind := range []string{"zero", "one", "negative-one", "signed-small", "powers-of-two", "half-modulus", "distinct-concentrated"} {
		t.Run(kind, func(t *testing.T) {
			const count = 4099
			values := make([]fr.Element, count)
			half := new(big.Int).Rsh(fr.Modulus(), 1)
			for i := range values {
				switch kind {
				case "one":
					values[i].SetOne()
				case "negative-one":
					values[i].SetInt64(-1)
				case "signed-small":
					values[i].SetInt64(int64(i%31 - 15))
				case "powers-of-two":
					values[i].SetBigInt(new(big.Int).Lsh(big.NewInt(1), uint(i%253)))
					if i%2 != 0 {
						values[i].Neg(&values[i])
					}
				case "half-modulus":
					value := new(big.Int).Add(half, big.NewInt(int64(i%7-3)))
					values[i].SetBigInt(value)
				case "distinct-concentrated":
					values[i].SetUint64((uint64(i) << 32) | 2)
					if i%2 != 0 {
						values[i].Neg(&values[i])
					}
				}
			}
			before, err := a.Stats()
			if err != nil {
				t.Fatal(err)
			}
			checkSplitMSM(t, a, pk.KzgLagrange.G1[3:3+count], values)
			if kind == "zero" || kind == "one" || kind == "negative-one" {
				after, err := a.Stats()
				if err != nil {
					t.Fatal(err)
				}
				var expectedUnits uint64
				if kind != "zero" {
					expectedUnits = count
				}
				if after.SplitChunkCount != before.SplitChunkCount || after.SplitUnitPoints-before.SplitUnitPoints != expectedUnits {
					t.Fatalf("zero/±1 input did not retain its sparse path: before=%+v after=%+v", before, after)
				}
			}
		})
	}
	t.Run("multiple-batches-and-offset", func(t *testing.T) {
		points := pk.Kzg.G1[3:domain]
		values := make([]fr.Element, len(points))
		for i := range values {
			values[i].SetUint64((uint64(i) << 32) | 2)
			if i%5 == 0 {
				values[i].Neg(&values[i])
			}
		}
		checkSplitMSM(t, a, points, values)
	})
	t.Run("infinity-points", func(t *testing.T) {
		values := make([]fr.Element, 256)
		for i := range values {
			values[i].SetInt64(int64(i + 2))
		}
		checkSplitMSM(t, a, pk.Kzg.G1[512:768], values)
	})
	t.Run("unchanged-monomial-tail", func(t *testing.T) {
		values := make([]fr.Element, domain+3)
		for i := range values {
			values[i].SetInt64(int64(i%9 - 4))
		}
		checkSplitMSM(t, a, pk.Kzg.G1, values)
	})
	stats, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	if stats.MSMCalls == 0 || stats.CPUTailPoints != 3 {
		t.Fatalf("missing split MSM or tail dispatch evidence: %+v", stats)
	}
	if stats.SplitMSMCalls != stats.MSMCalls || slices.Max(stats.SplitMaxBucket[:]) < 65537 || slices.Max(stats.SplitChunkCount[:]) == 0 {
		t.Fatalf("concentrated inputs did not exercise split-bucket accumulation: %+v", stats)
	}
	if stats.MaskedMSMCalls != 0 || stats.MaskSumCalls != 0 || stats.MaskCacheHits != 0 {
		t.Fatalf("default split policy performed scalar masking: %+v", stats)
	}
}
