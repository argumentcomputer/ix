//go:build cuda

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"strconv"
	"strings"
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
	modes := []string{"cpu", "cuda"}
	if value := os.Getenv("IX_PLONK_CUDA_INIT_MODES"); value != "" {
		selected := make(map[string]bool)
		for _, mode := range strings.Split(value, ",") {
			mode = strings.TrimSpace(mode)
			if (mode != "cpu" && mode != "cuda") || selected[mode] {
				t.Fatal("IX_PLONK_CUDA_INIT_MODES must be a unique comma-separated subset of cpu,cuda")
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
	required := func(name string) string {
		value := os.Getenv("IX_PLONK_CUDA_INIT_" + name)
		if value == "" {
			t.Fatalf("IX_PLONK_CUDA_INIT_%s must be explicit", name)
		}
		return value
	}
	dir, witnessPath, output := required("ARTIFACTS"), required("WITNESS"), required("OUTPUT")
	manifestPin, err := initDigest(required("MANIFEST_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	claim, err := initDigest(required("EXPECTED_CLAIM"))
	if err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(output, 0700); err != nil {
		t.Fatal(err)
	}
	started := time.Now()
	m, err := initManifest(dir, manifestPin)
	if err != nil {
		t.Fatal(err)
	}
	ccs, pk, vk := plonk.NewCS(curveID), plonk.NewProvingKey(curveID), plonk.NewVerifyingKey(curveID)
	if err := initReadBinary(filepath.Join(dir, "circuit.bin"), m.Files["circuit.bin"], ccs); err != nil {
		t.Fatal(err)
	}
	if err := initReadBinary(filepath.Join(dir, "proving-key.bin"), m.Files["proving-key.bin"], pk); err != nil {
		t.Fatal(err)
	}
	if err := initReadBinary(filepath.Join(dir, "verifying-key.bin"), m.Files["verifying-key.bin"], vk); err != nil {
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
	wrongDigest := append([]byte(nil), digest...)
	wrongDigest[0] ^= 1
	wrongPublic, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(wrongDigest)}, curveID.ScalarField(), frontend.PublicOnly())
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
	if ccs.GetNbConstraints() != m.Constraints || ccs.GetNbPublicVariables() != m.PublicInputs || len(ccs.GetCommitments().CommitmentIndexes()) != m.Commitments || nativePK.Vk.Size != m.Domain {
		t.Fatal("decoded circuit or key dimensions differ from the manifest")
	}
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
		"complete":       false,
		"scope":          "Externally pinned existing Init artifacts; same loaded circuit, keys and witness for CPU and CUDA, fresh gnark blinding. No compilation or key preparation.",
		"manifestSHA256": manifestPin, "manifest": m, "expectedClaim": claim,
		"testBinary": identity, "artifactAndWitnessSeconds": time.Since(started).Seconds(),
		"repeats": repeats, "modes": modes, "executionOrder": "iteration-major: " + strings.Join(modes, ", "),
		"numCPU": runtime.NumCPU(), "gomaxprocs": runtime.GOMAXPROCS(0),
		"freshCUDAContextPerProof": true, "forcedGC": false,
		"cpuProfile":      cpuProfile,
		"cpuProfileScope": "Only the first selected run: CPU samples immediately around plonk.Prove, excluding artifact/witness loading, backend setup, serialization and verification. Profiler startup/shutdown are timed separately; subsequent runs are unprofiled.",
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
				config := cuda.Config{MemoryBytes: 64 << 30, HeadroomBytes: 8 << 30}
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
			profileThisRun := cpuProfile && len(runs) == 0
			profilePath := ""
			var profileFile *os.File
			var profileStartSeconds, profileStopSeconds float64
			if profileThisRun {
				profileStarted := time.Now()
				profilePath = filepath.Join(output, stem+".cpu.pprof")
				profileFile, err = os.OpenFile(profilePath, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
				if err != nil {
					t.Fatal(err)
				}
				if err := pprof.StartCPUProfile(profileFile); err != nil {
					profileFile.Close()
					t.Fatal(err)
				}
				profileStartSeconds = time.Since(profileStarted).Seconds()
			}
			proveStarted := time.Now()
			var proof plonk.Proof
			var proveSeconds float64
			var profileErr error
			func() {
				if profileFile != nil {
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
			if err != nil {
				t.Fatal(err)
			}
			if profileErr != nil {
				t.Fatal(profileErr)
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
				if stats.NumeratorCalls != 1 {
					t.Fatal("CUDA numerator was not dispatched exactly once")
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
			if err := plonk.Verify(decoded, vk, wrongPublic, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err == nil {
				t.Fatal("accepted an altered claim")
			}
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

func initDigest(text string) (string, error) {
	value, err := unhex(text, sha256.Size)
	if err != nil {
		return "", err
	}
	return hex.EncodeToString(value), nil
}

// Test executables have their own identity. This benchmark entry point trusts
// an externally pinned manifest; production loading retains its executable pin.
func initManifest(dir, expectedSHA256 string) (*manifest, error) {
	f, err := os.Open(filepath.Join(dir, "manifest.json"))
	if err != nil {
		return nil, err
	}
	defer f.Close()
	stat, err := f.Stat()
	if err != nil {
		return nil, err
	}
	if !stat.Mode().IsRegular() || stat.Size() > 1<<20 {
		return nil, fmt.Errorf("Init manifest must be a regular file of at most 1 MiB")
	}
	data, err := io.ReadAll(io.LimitReader(f, (1<<20)+1))
	if err != nil {
		return nil, err
	}
	if len(data) > 1<<20 || fmt.Sprintf("%x", sha256.Sum256(data)) != expectedSHA256 {
		return nil, fmt.Errorf("Init manifest differs from the explicitly trusted SHA-256")
	}
	var m manifest
	d := json.NewDecoder(bytes.NewReader(data))
	d.DisallowUnknownFields()
	if err := d.Decode(&m); err != nil {
		return nil, err
	}
	if err := d.Decode(new(any)); err != io.EOF {
		return nil, fmt.Errorf("trailing Init manifest data")
	}
	if !m.KeysReady || m.Constraints < 1 || m.Constraints > 1<<26 || m.Domain < uint64(m.Constraints+2) || m.Domain > 1<<26 || m.Domain&(m.Domain-1) != 0 || m.PublicInputs != 2 || m.Commitments < 0 || m.Commitments > 1024 || len(m.Files) != 5 {
		return nil, fmt.Errorf("Init requires prepared BN254 wrapper artifacts")
	}
	for _, digest := range []string{m.InnerVKSHA256, m.SRSBLAKE3} {
		if _, err := initDigest(digest); err != nil {
			return nil, fmt.Errorf("invalid Init manifest identity: %w", err)
		}
	}
	for _, name := range []string{"circuit.bin", "proving-key.bin", "verifying-key.bin", "vk.json", "PlonkVerifier.sol"} {
		want, ok := m.Files[name]
		if !ok || want.Bytes <= 0 {
			return nil, fmt.Errorf("missing Init artifact %s", name)
		}
		if _, err := initDigest(want.SHA256); err != nil {
			return nil, fmt.Errorf("invalid Init artifact digest for %s", name)
		}
		stat, err := os.Stat(filepath.Join(dir, name))
		if err != nil {
			return nil, err
		}
		if !stat.Mode().IsRegular() || stat.Size() != want.Bytes {
			return nil, fmt.Errorf("Init artifact %s has an invalid type or size", name)
		}
		if err := m.checkFile(dir, name); err != nil {
			return nil, err
		}
	}
	if m.Files["vk.json"].SHA256 != m.InnerVKSHA256 {
		return nil, fmt.Errorf("verifying key identity differs from its artifact digest")
	}
	return &m, nil
}

// Hash the bytes actually decoded as well as the prior authentication pass.
func initReadBinary(path string, want artifact, value io.ReaderFrom) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	h := sha256.New()
	n, err := value.ReadFrom(io.TeeReader(io.LimitReader(f, want.Bytes+1), h))
	if err != nil {
		return err
	}
	if n != want.Bytes || hex.EncodeToString(h.Sum(nil)) != want.SHA256 {
		return fmt.Errorf("decoded artifact %s differs from its pinned bytes", path)
	}
	var extra [1]byte
	if n, err := f.Read(extra[:]); n != 0 || err != io.EOF {
		return fmt.Errorf("trailing artifact data in %s", path)
	}
	return nil
}
