//go:build bn254 && cuda

package main

import (
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"testing"
	"time"

	"github.com/argumentcomputer/ix/tools/bls-plonk-wrapper/internal/cuda"
	"github.com/consensys/gnark-crypto/ecc"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	native "github.com/consensys/gnark/backend/plonk/bn254"
)

func TestCUDAStructuredMSMBenchmark(t *testing.T) {
	if os.Getenv("IX_PLONK_CUDA_MSM_BENCH") != "1" {
		t.Skip("set IX_PLONK_CUDA_MSM_BENCH=1 and explicit artifact pins for 2^20 structured MSM comparisons")
	}
	if os.Getenv("GOMAXPROCS") != "" {
		t.Fatal("unset GOMAXPROCS to keep default CPU parallelism")
	}
	required := func(name string) string {
		value := os.Getenv("IX_PLONK_CUDA_MSM_BENCH_" + name)
		if value == "" {
			t.Fatalf("IX_PLONK_CUDA_MSM_BENCH_%s must be explicit", name)
		}
		return value
	}
	dir, out := required("ARTIFACTS"), required("OUTPUT")
	pin, err := cpuProfileDigest(required("MANIFEST_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(out, 0700); err != nil {
		t.Fatal(err)
	}
	started := time.Now()
	m, err := cpuProfileManifest(dir, pin)
	if err != nil {
		t.Fatal(err)
	}
	validationSeconds := time.Since(started).Seconds()
	started = time.Now()
	pk := new(native.ProvingKey)
	if err := cpuProfileReadBinary(filepath.Join(dir, "proving-key.bin"), m.Files["proving-key.bin"], pk); err != nil {
		t.Fatal(err)
	}
	loadSeconds := time.Since(started).Seconds()
	config, err := provingCUDAConfig()
	if err != nil {
		t.Fatal(err)
	}
	config.Features = native.AcceleratorFeatureMSMV1
	started = time.Now()
	a, err := cuda.Attach(pk, config)
	if err != nil {
		t.Fatal(err)
	}
	setupSeconds := time.Since(started).Seconds()
	defer func() {
		if err := a.Close(); err != nil {
			t.Error(err)
		}
	}()
	const count = 1 << 20
	const offset = 2
	points := pk.KzgLagrange.G1[offset : offset+count]
	report := map[string]any{"format": "ix-bn254-cuda-structured-msm-v1", "complete": false, "scope": "Synthetic structured scalars and authenticated production Lagrange bases; exact CPU/GPU MSM comparison, not a PLONK proof or full Init benchmark.", "manifestSHA256": pin, "provingKeySHA256": m.Files["proving-key.bin"].SHA256, "count": count, "offset": offset, "strategy": config.MSMStrategy.String(), "validationSeconds": validationSeconds, "keyLoadSeconds": loadSeconds, "gpuSetupSeconds": setupSeconds}
	var rows []map[string]any
	defer func() {
		report["rows"] = rows
		if err := writeJSON(filepath.Join(out, "report.json"), report); err != nil {
			t.Error(err)
		}
	}()
	var c, d, minusC fr.Element
	if _, err := c.SetString("837628908879347212334541733913009433"); err != nil {
		t.Fatal(err)
	}
	d.SetUint64(7919)
	minusC.Neg(&c)
	one := fr.One()
	for _, kind := range []string{"shifted-binary", "signed-zero", "three-hot", "distinct-shifted", "narrow-shifted", "narrow-small"} {
		started = time.Now()
		values := make([]fr.Element, count)
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
			case "distinct-shifted":
				values[i].SetUint64(uint64(i)).Add(&values[i], &c)
			case "narrow-shifted":
				values[i].SetUint64(uint64(i%65536)).Add(&values[i], &c)
			case "narrow-small":
				values[i].SetUint64(uint64(i % 65536))
			}
			if i%17 == 0 {
				var seed [8]byte
				binary.LittleEndian.PutUint64(seed[:], uint64(i))
				digest := sha256.Sum256(seed[:])
				values[i].SetBytes(digest[:])
			}
		}
		generationSeconds := time.Since(started).Seconds()
		original := append([]fr.Element(nil), values...)
		started = time.Now()
		var want curve.G1Affine
		if _, err := want.MultiExp(points, values, ecc.MultiExpConfig{}); err != nil {
			t.Fatal(err)
		}
		cpuSeconds := time.Since(started).Seconds()
		before, err := a.Stats()
		if err != nil {
			t.Fatal(err)
		}
		var gpuSeconds []float64
		for iteration := range 2 {
			started = time.Now()
			got, err := a.MultiExp(points, values)
			elapsed := time.Since(started).Seconds()
			if err != nil || !got.Equal(&want) {
				t.Fatalf("%s iteration %d differs from CPU: %v", kind, iteration, err)
			}
			if !slices.Equal(original, values) {
				t.Fatal("structured MSM changed caller scalars")
			}
			gpuSeconds = append(gpuSeconds, elapsed)
			t.Logf("kind=%s count=%d iteration=%d cpu_seconds=%.6f gpu_seconds=%.6f", kind, count, iteration, cpuSeconds, elapsed)
		}
		after, err := a.Stats()
		if err != nil {
			t.Fatal(err)
		}
		if config.MSMStrategy == cuda.MSMMask {
			if after.MaskedMSMCalls-before.MaskedMSMCalls != 2 || after.MaskCacheHits-before.MaskCacheHits < 1 {
				t.Fatal("mask comparison did not exercise mask cache")
			}
		} else if after.MaskedMSMCalls != before.MaskedMSMCalls {
			t.Fatal("split strategy applied masking")
		}
		rows = append(rows, map[string]any{"kind": kind, "generationSeconds": generationSeconds, "cpuSeconds": cpuSeconds, "gpuSeconds": gpuSeconds, "before": before, "after": after, "resultSHA256": fmt.Sprintf("%x", sha256.Sum256(want.Marshal())), "matchesCPU": true, "hostScalarsUnchanged": true})
		report["rows"] = rows
		if err := writeJSON(filepath.Join(out, "report.json"), report); err != nil {
			t.Fatal(err)
		}
	}
	if err := a.Close(); err != nil {
		t.Fatal(err)
	}
	report["complete"] = true
}
