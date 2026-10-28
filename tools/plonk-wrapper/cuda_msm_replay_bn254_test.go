//go:build cuda

package main

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"testing"
	"time"

	"github.com/argumentcomputer/ix/tools/plonk-wrapper/internal/cuda"
	curve "github.com/consensys/gnark-crypto/ecc/bn254"
	native "github.com/consensys/gnark/backend/plonk/bn254"
)

func TestReplayActualInitMSMs(t *testing.T) {
	if os.Getenv("IX_PLONK_CUDA_MSM_REPLAY") != "1" {
		t.Skip("set IX_PLONK_CUDA_MSM_REPLAY=1 with explicit artifact and capture pins")
	}
	if os.Getenv("GOMAXPROCS") != "" {
		t.Fatal("unset GOMAXPROCS for default CPU parallelism")
	}
	if err := checkRawMontgomeryABI(); err != nil {
		t.Fatal(err)
	}
	const prefix = "IX_PLONK_CUDA_MSM_REPLAY_"
	dir, out, source := msmTestRequired(t, prefix, "ARTIFACTS"), msmTestRequired(t, prefix, "OUTPUT"), msmTestRequired(t, prefix, "CAPTURES")
	pin, err := cpuProfileDigest(msmTestRequired(t, prefix, "MANIFEST_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	capturePin, err := cpuProfileDigest(msmTestRequired(t, prefix, "CAPTURE_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	claim, err := cpuProfileDigest(msmTestRequired(t, prefix, "EXPECTED_CLAIM"))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(out, 0700); err != nil {
		t.Fatal(err)
	}
	capture, err := readCaptureManifest(filepath.Join(source, "capture.json"), capturePin)
	if err != nil {
		t.Fatal(err)
	}
	m, pk, validationSeconds, loadSeconds := authenticatedMSMKey(t, dir, pin)
	if err := validateCapture(capture, m); err != nil {
		t.Fatal(err)
	}
	if capture.ArtifactManifestSHA256 != pin || capture.ExpectedClaim != claim {
		t.Fatal("capture artifact/claim binding differs")
	}
	config, err := provingCUDAConfig()
	if err != nil {
		t.Fatal(err)
	}
	config.Features = native.AcceleratorFeatureMSMV1
	replayBinary, err := executableHash()
	if err != nil {
		t.Fatal(err)
	}
	report := map[string]any{"format": "ix-bn254-actual-init-msm-replay-v1", "complete": false, "scope": "Authenticated captured Init MSMs, compared with captured CPU results; one fresh GPU context per vector, two invocations per context; no PLONK proof produced.", "captureSHA256": capturePin, "artifactManifestSHA256": pin, "expectedClaim": claim, "strategy": config.MSMStrategy.String(), "validationSeconds": validationSeconds, "keyLoadSeconds": loadSeconds}
	report["testBinarySHA256"], report["goVersion"] = replayBinary, runtime.Version()
	report["numCPU"], report["gomaxprocs"] = runtime.NumCPU(), runtime.GOMAXPROCS(0)
	var rows []map[string]any
	defer func() {
		report["rows"] = rows
		if err := writeJSON(filepath.Join(out, "report.json"), report); err != nil {
			t.Error(err)
		}
	}()
	for _, row := range capture.Records {
		started := time.Now()
		path := filepath.Join(source, row.ScalarsFile)
		identity, err := fileHash(path)
		if err != nil || identity != row.Scalars {
			t.Fatalf("scalar capture %d failed authentication", row.Index)
		}
		values := make(rawScalarVector, int(row.Count))
		if err := cpuProfileReadBinary(path, row.Scalars, values); err != nil {
			t.Fatal(err)
		}
		decodeSeconds := time.Since(started).Seconds()
		encoded, err := unhex(row.CPUResult, 32)
		if err != nil {
			t.Fatal(err)
		}
		var expected curve.G1Affine
		n, err := expected.SetBytes(encoded)
		if err != nil || n != len(encoded) || !expected.IsOnCurve() || !expected.IsInSubGroup() {
			t.Fatal("invalid captured CPU result")
		}
		started = time.Now()
		a, err := cuda.Attach(pk, config)
		if err != nil {
			t.Fatal(err)
		}
		setupSeconds := time.Since(started).Seconds()
		var operations []map[string]any
		func() {
			defer func() {
				if err := a.Close(); err != nil {
					t.Error(err)
				}
			}()
			for iteration := range 2 {
				before, err := a.Stats()
				if err != nil {
					t.Fatal(err)
				}
				started = time.Now()
				got, err := a.MultiExp(pk.KzgLagrange.G1[row.Offset:row.Offset+row.Count], values)
				elapsed := time.Since(started).Seconds()
				if err != nil || !got.Equal(&expected) {
					t.Fatalf("capture %d iteration %d differs from CPU: %v", row.Index, iteration, err)
				}
				after, err := a.Stats()
				if err != nil {
					t.Fatal(err)
				}
				if config.MSMStrategy == cuda.MSMSplit {
					if after.MaskedMSMCalls != 0 || after.SplitMSMCalls-before.SplitMSMCalls != 1 {
						t.Fatal("default replay did not execute the split MSM path")
					}
				} else if after.MaskedMSMCalls-before.MaskedMSMCalls != 1 {
					t.Fatal("mask replay did not execute masked MSM")
				}
				operations = append(operations, map[string]any{"iteration": iteration, "seconds": elapsed, "before": before, "after": after, "matchesCPU": true})
				t.Logf("capture=%d caller=%s count=%d strategy=%s iteration=%d seconds=%.6f matches_cpu=true", row.Index, row.Caller, row.Count, config.MSMStrategy.String(), iteration, elapsed)
			}
		}()
		if t.Failed() {
			return
		}
		if fmt.Sprintf("%x", sha256.Sum256(rawMontgomery(values))) != row.Scalars.SHA256 {
			t.Fatal("replay changed caller scalar bytes")
		}
		rows = append(rows, map[string]any{"capture": row.Index, "caller": row.Caller, "basis": row.Basis, "offset": row.Offset, "count": row.Count, "scalarSHA256": row.Scalars.SHA256, "cpuResultSHA256": row.CPUResultSHA256, "captureCPUSeconds": row.CPUSeconds, "scalarLoadSeconds": decodeSeconds, "gpuSetupSeconds": setupSeconds, "operations": operations})
		report["rows"] = rows
		if err := writeJSON(filepath.Join(out, "report.json"), report); err != nil {
			t.Fatal(err)
		}
	}
	report["complete"] = true
}
