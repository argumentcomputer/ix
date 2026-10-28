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

func TestCUDAMaskedMSMTransparencyAndRangeCache(t *testing.T) {
	config := gpuConfig(t, AllFeatures)
	config.MSMStrategy = MSMMask
	pk := kernelKey(t, 8192)
	a, err := Attach(pk, config)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := a.Close(); err != nil {
			t.Error(err)
		}
	})
	ranges := [][]curve.G1Affine{pk.Kzg.G1[:4096], pk.Kzg.G1[1:4097], pk.Kzg.G1[:4097]}
	kinds := []string{"zero", "cancellation", "distinct-shifted", "narrow-small", "shifted-binary"}
	var shift fr.Element
	if _, err := shift.SetString("837628908879347212334541733913009433"); err != nil {
		t.Fatal(err)
	}
	for _, points := range ranges {
		for _, kind := range kinds {
			values := make([]fr.Element, len(points))
			switch kind {
			case "cancellation":
				values[0].SetUint64(7)
				values[1].SetInt64(-1)
			case "shifted-binary":
				values = structuredScalars(len(points), kind)
			case "distinct-shifted", "narrow-small":
				for i := range values {
					if kind == "distinct-shifted" {
						values[i].SetUint64(uint64(i)).Add(&values[i], &shift)
					} else {
						values[i].SetUint64(uint64(i % 256))
					}
					if i%17 == 0 {
						var seed [8]byte
						binary.LittleEndian.PutUint64(seed[:], uint64(i))
						digest := sha256.Sum256(seed[:])
						values[i].SetBytes(digest[:])
					}
				}
			}
			original := append([]fr.Element(nil), values...)
			var want curve.G1Affine
			if _, err := want.MultiExp(points, values, ecc.MultiExpConfig{}); err != nil {
				t.Fatal(err)
			}
			for range 2 {
				got, err := a.MultiExp(points, values)
				if err != nil || !got.Equal(&want) {
					t.Fatalf("masked %s MSM differs: %v", kind, err)
				}
				if !slices.Equal(values, original) {
					t.Fatal("masking changed caller scalars")
				}
			}
		}
	}
	stats, err := a.Stats()
	if err != nil {
		t.Fatal(err)
	}
	calls := uint64(len(ranges) * len(kinds) * 2)
	if stats.MaskedMSMCalls != calls || stats.MaskSumCalls != uint64(len(ranges)) || stats.MaskCacheHits != calls-uint64(len(ranges)) {
		t.Fatalf("mask/correction range cache was not exercised: %+v", stats)
	}
}
