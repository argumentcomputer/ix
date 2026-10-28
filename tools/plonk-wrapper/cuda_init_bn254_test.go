//go:build cuda

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/argumentcomputer/ix/tools/plonk-wrapper/internal/cuda"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	native "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
)

func TestBN254CUDAInit(t *testing.T) {
	if os.Getenv("IX_PLONK_CUDA_INIT") != "1" {
		t.Skip("set IX_PLONK_CUDA_INIT=1 with explicit artifact and claim pins for full Init proofs")
	}
	repeats := 1
	if value := os.Getenv("IX_PLONK_CUDA_INIT_REPEATS"); value != "" {
		parsed, err := strconv.Atoi(value)
		if err != nil || parsed < 1 || parsed > 10 {
			t.Fatal("IX_PLONK_CUDA_INIT_REPEATS must be an integer in 1..10")
		}
		repeats = parsed
	}
	modes := []string{"cpu", "cuda-unfused", "cuda-fused"}
	if value := os.Getenv("IX_PLONK_CUDA_INIT_MODES"); value != "" {
		selected := make(map[string]bool)
		for _, mode := range strings.Split(value, ",") {
			mode = strings.TrimSpace(mode)
			if (mode != "cpu" && mode != "cuda-unfused" && mode != "cuda-fused") || selected[mode] {
				t.Fatal("IX_PLONK_CUDA_INIT_MODES must be a unique comma-separated subset of cpu,cuda-unfused,cuda-fused")
			}
			selected[mode] = true
		}
		filtered := make([]string, 0, len(selected))
		for _, mode := range modes {
			if selected[mode] {
				filtered = append(filtered, mode)
			}
		}
		modes = filtered
	}
	flag := func(name string) bool {
		switch os.Getenv(name) {
		case "", "0":
			return false
		case "1":
			return true
		default:
			t.Fatalf("%s must be 0 or 1", name)
			return false
		}
	}
	cpuProfile := flag("IX_PLONK_CUDA_INIT_CPU_PROFILE")
	stageProfile := flag("IX_PLONK_CUDA_INIT_STAGE_PROFILE")
	required := func(name string) string {
		value := os.Getenv("IX_PLONK_CUDA_INIT_" + name)
		if value == "" {
			t.Fatalf("IX_PLONK_CUDA_INIT_%s must be explicit", name)
		}
		return value
	}
	dir, witnessPath, output := required("ARTIFACTS"), required("WITNESS"), required("OUTPUT")
	manifestPin, err := cpuProfileDigest(required("MANIFEST_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	claim, err := cpuProfileDigest(required("EXPECTED_CLAIM"))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(output, 0700); err != nil {
		t.Fatal(err)
	}
	started := time.Now()
	m, err := cpuProfileManifest(dir, manifestPin)
	if err != nil {
		t.Fatal(err)
	}
	ccs, pk, vk := plonk.NewCS(curveID), plonk.NewProvingKey(curveID), plonk.NewVerifyingKey(curveID)
	if err := cpuProfileReadBinary(filepath.Join(dir, "circuit.bin"), m.Files["circuit.bin"], ccs); err != nil {
		t.Fatal(err)
	}
	if err := cpuProfileReadBinary(filepath.Join(dir, "proving-key.bin"), m.Files["proving-key.bin"], pk); err != nil {
		t.Fatal(err)
	}
	if err := cpuProfileReadBinary(filepath.Join(dir, "verifying-key.bin"), m.Files["verifying-key.bin"], vk); err != nil {
		t.Fatal(err)
	}
	p, err := loadVerifyingKey(filepath.Join(dir, "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := m.checkFile(dir, "vk.json"); err != nil {
		t.Fatal(err)
	}
	assignment, err := witnessAssignment(p, witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	witness, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	digest, _ := hex.DecodeString(claim)
	public, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, curveID.ScalarField(), frontend.PublicOnly())
	if err != nil {
		t.Fatal(err)
	}
	actualPublic, err := witness.Public()
	if err != nil {
		t.Fatal(err)
	}
	actualBytes, err := actualPublic.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	expectedBytes, err := public.MarshalBinary()
	if err != nil || !bytes.Equal(actualBytes, expectedBytes) {
		t.Fatal("witness differs from independently expected claim")
	}
	nativePK := pk.(*native.ProvingKey)
	var embedded bytes.Buffer
	if _, err := nativePK.Vk.WriteTo(&embedded); err != nil {
		t.Fatal(err)
	}
	if fmt.Sprintf("%x", sha256.Sum256(embedded.Bytes())) != m.Files["verifying-key.bin"].SHA256 {
		t.Fatal("proving key embeds another verifying key")
	}
	executable, err := os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	identity, err := fileHash(executable)
	if err != nil {
		t.Fatal(err)
	}
	report := map[string]any{
		"format": "ix-bn254-plonk-cuda-init-v1", "complete": false,
		"scope":          "Externally pinned existing Init artifacts; same loaded circuit, keys and witness for CPU and CUDA, fresh gnark blinding. No compilation or key preparation.",
		"manifestSHA256": manifestPin, "manifest": m, "expectedClaim": claim,
		"testBinary": identity, "artifactAndWitnessSeconds": time.Since(started).Seconds(),
		"repeats": repeats, "modes": modes, "executionOrder": "iteration-major: " + strings.Join(modes, ", "),
		"numCPU": runtime.NumCPU(), "gomaxprocs": runtime.GOMAXPROCS(0),
		"freshCUDAContextPerProof": true, "forcedGC": false,
		"cpuProfile": cpuProfile, "stageProfile": stageProfile,
		"cpuProfileScope":   "Only the first selected run: CPU samples immediately around plonk.Prove, excluding artifact/witness loading, backend setup, serialization and verification. Profiler startup/shutdown are timed separately; subsequent runs are unprofiled.",
		"stageProfileScope": "Optional gnark spans from one monotonic Prove origin. Task, compute and wait intervals may nest or overlap and must not be summed as independent wall-clock stages.",
	}
	if stageProfile {
		t.Cleanup(func() { nativePK.SetStageObserverV1(nil) })
	}
	var runs []map[string]any
	for iteration := 1; iteration <= repeats; iteration++ {
		for _, mode := range modes {
			stem := mode
			if iteration > 1 {
				stem = fmt.Sprintf("%s-%02d", mode, iteration)
			}
			t.Logf("stage=%s iteration=%d repeats=%d", mode, iteration, repeats)
			setupStarted := time.Now()
			var accelerator *cuda.Accelerator
			var cudaConfig *cuda.Config
			if mode != "cpu" {
				config, err := provingCUDAConfig()
				if err != nil {
					t.Fatal(err)
				}
				if mode == "cuda-unfused" {
					config.Features &^= native.AcceleratorFeatureQuotientV1
				}
				cudaConfig = &config
				accelerator, err = cuda.Attach(nativePK, config)
				if err != nil {
					t.Fatal(err)
				}
				t.Cleanup(func() { _ = accelerator.Close() })
			}
			setupSeconds := time.Since(setupStarted).Seconds()
			var setupStats cuda.Stats
			if accelerator != nil {
				setupStats, err = accelerator.Stats()
				if err != nil {
					t.Fatal(err)
				}
			}
			var stageMu sync.Mutex
			var stageEvents []native.StageEventV1
			if stageProfile {
				nativePK.SetStageObserverV1(func(event native.StageEventV1) {
					stageMu.Lock()
					stageEvents = append(stageEvents, event)
					stageMu.Unlock()
				})
			}
			profileThisRun := cpuProfile && len(runs) == 0
			profilePath := ""
			var vkFile *os.File
			var profileStartSeconds, profileStopSeconds float64
			if profileThisRun {
				profileStarted := time.Now()
				profilePath = filepath.Join(output, stem+".cpu.pprof")
				vkFile, err = os.OpenFile(profilePath, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
				if err != nil {
					t.Fatal(err)
				}
				if err := pprof.StartCPUProfile(profileFile); err != nil {
					vkFile.Close()
					t.Fatal(err)
				}
				profileStartSeconds = time.Since(profileStarted).Seconds()
			}
			proveStarted := time.Now()
			var proof plonk.Proof
			var proveSeconds float64
			var profileErr error
			func() {
				if vkFile != nil {
					defer func() {
						profileStopped := time.Now()
						pprof.StopCPUProfile()
						profileErr = profileFile.Close()
						profileStopSeconds = time.Since(profileStopped).Seconds()
					}()
				}
				proof, err = plonk.Prove(ccs, pk, witness, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
				proveSeconds = time.Since(proveStarted).Seconds()
			}()
			var spans []map[string]any
			if stageProfile {
				nativePK.SetStageObserverV1(nil)
				stageMu.Lock()
				for _, event := range stageEvents {
					spans = append(spans, map[string]any{"stage": event.Stage, "phase": event.Phase, "startSeconds": event.Start.Seconds(), "endSeconds": event.End.Seconds(), "durationSeconds": (event.End - event.Start).Seconds(), "failed": event.Failed})
				}
				stageMu.Unlock()
			}
			if err != nil {
				t.Fatal(err)
			}
			if profileErr != nil {
				t.Fatal(profileErr)
			}
			if stageProfile && len(spans) == 0 {
				t.Fatal("enabled stage observer produced no spans")
			}
			var stats cuda.Stats
			if accelerator != nil {
				stats, err = accelerator.Stats()
				if err != nil {
					t.Fatal(err)
				}
				if err := accelerator.Close(); err != nil {
					t.Fatal(err)
				}
				if stats.MSMCalls == 0 || stats.FFTCalls == 0 {
					t.Fatal("CUDA arithmetic was not dispatched")
				}
				if mode == "cuda-fused" && (stats.QuotientCalls != 1 || stats.NumeratorCalls != 0) {
					t.Fatal("fused quotient was not dispatched exactly once")
				}
				if mode == "cuda-unfused" && (stats.QuotientCalls != 0 || stats.NumeratorCalls != 1) {
					t.Fatal("unfused numerator was not dispatched exactly once")
				}
			}
			var encoded bytes.Buffer
			if _, err := proof.WriteTo(&encoded); err != nil {
				t.Fatal(err)
			}
			decoded, err := decodeProof(encoded.Bytes(), m.Commitments)
			if err != nil {
				t.Fatal(err)
			}
			verifyStarted := time.Now()
			if err := plonk.Verify(decoded, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
				t.Fatal(err)
			}
			verifySeconds := time.Since(verifyStarted).Seconds()
			proofPath := filepath.Join(output, stem+".proof.bin")
			if err := os.WriteFile(proofPath, encoded.Bytes(), 0600); err != nil {
				t.Fatal(err)
			}
			solidityPath := filepath.Join(output, stem+".solidity.bin")
			if err := os.WriteFile(solidityPath, decoded.MarshalSolidity(), 0600); err != nil {
				t.Fatal(err)
			}
			run := map[string]any{"mode": mode, "iteration": iteration, "cudaConfig": cudaConfig, "startedUTC": setupStarted.UTC().Format(time.RFC3339Nano),
				"proveStartedUTC": proveStarted.UTC().Format(time.RFC3339Nano), "finishedUTC": time.Now().UTC().Format(time.RFC3339Nano),
				"backendSetupSeconds": setupSeconds, "proveSeconds": proveSeconds,
				"verifySeconds": verifySeconds, "proofPath": proofPath, "solidityPath": solidityPath, "proofBytes": encoded.Len(),
				"proofSHA256": fmt.Sprintf("%x", sha256.Sum256(encoded.Bytes())), "cudaStats": stats,
				"cudaSetupStats": setupStats}
			run["cpuProfiled"], run["cpuProfilePath"] = profileThisRun, profilePath
			run["profileStartSeconds"], run["profileStopSeconds"] = profileStartSeconds, profileStopSeconds
			run["stageProfiled"], run["stageSpans"] = stageProfile, spans
			if profileThisRun {
				profileIdentity, err := fileHash(profilePath)
				if err != nil {
					t.Fatal(err)
				}
				run["cpuProfileArtifact"] = profileIdentity
				report["profiledRun"] = map[string]any{"mode": mode, "iteration": iteration, "path": profilePath, "artifact": profileIdentity}
			}
			if cudaConfig != nil {
				run["msmStrategy"] = cudaConfig.MSMStrategy.String()
			}
			runs = append(runs, run)
			report["runs"] = runs
			if err := writeJSON(filepath.Join(output, "report.json"), report); err != nil {
				t.Fatal(err)
			}
			t.Logf("stage=%s iteration=%d prove_seconds=%.6f setup_seconds=%.6f verify_seconds=%.6f stats=%+v", mode, iteration, proveSeconds, setupSeconds, verifySeconds, stats)
		}
	}
	report["complete"], report["wallSeconds"] = true, time.Since(started).Seconds()
	if err := writeJSON(filepath.Join(output, "report.json"), report); err != nil {
		t.Fatal(err)
	}
}
