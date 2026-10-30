//go:build cuda

package cuda

import (
	"crypto/sha256"
	"encoding/binary"
	"slices"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
)

func structuredScalars(count int, kind string) []fr.Element {
	values := make([]fr.Element, count)
	var c, d, minusC fr.Element
	c.SetString("837628908879347212334541733913009433")
	d.SetUint64(7919)
	minusC.Neg(&c)
	one := fr.One()
	for i := range values {
		switch kind {
		case "shifted-binary":
			values[i] = minusC
			if i%4 == 0 {
				values[i].Add(&values[i], &one)
			}
		case "signed-zero":
			switch i % 3 {
			case 0:
				values[i] = c
			case 1:
				values[i] = minusC
			}
		case "three-hot":
			values[i] = c
			switch i % 3 {
			case 0:
				values[i].Sub(&values[i], &d)
			case 1:
				values[i].Add(&values[i], &d)
			}
		}
		if i%17 == 0 {
			var input [8]byte
			binary.LittleEndian.PutUint64(input[:], uint64(i))
			digest := sha256.Sum256(input[:])
			values[i].SetBytes(digest[:])
		}
	}
	return values
}

func TestCUDAStructuredMSMMatchesRegisteredArrays(t *testing.T) {
	gpuConfig(t)
	pk := kernelKey(t, 128)
	// The generic MSM contract applies to the registered arrays independently of
	// whether their labels satisfy a proving-key basis relation.
	pk.KzgLagrange.G1[0].Neg(&pk.KzgLagrange.G1[0])
	a := attachForTest(t, pk)
	ranges := [][]curve.G1Affine{pk.KzgLagrange.G1, pk.Kzg.G1, pk.KzgLagrange.G1[:64], pk.KzgLagrange.G1[1:65], pk.KzgLagrange.G1[:96]}
	for _, points := range ranges {
		for _, kind := range []string{"shifted-binary", "signed-zero", "three-hot"} {
			values := structuredScalars(len(points), kind)
			original := append([]fr.Element(nil), values...)
			var want curve.G1Affine
			if _, err := want.MultiExp(points, values, ecc.MultiExpConfig{}); err != nil {
				t.Fatal(err)
			}
			for range 2 {
				got, err := a.MultiExp(points, values)
				if err != nil || !got.Equal(&want) {
					t.Fatalf("%s MSM differs: %v", kind, err)
				}
				if !slices.Equal(values, original) {
					t.Fatal("MSM changed caller scalars")
				}
			}
		}
	}
	stats, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	if stats.MSMCalls == 0 || stats.SplitMSMCalls != stats.MSMCalls || stats.MaskedMSMCalls != 0 {
		t.Fatalf("split MSM used an unexpected scalar transformation: %+v", stats)
	}
}
