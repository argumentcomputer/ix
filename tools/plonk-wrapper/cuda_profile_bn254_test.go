package main

import (
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"runtime/debug"
	"runtime/pprof"
	"strconv"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
)

const cpuProfileEnvPrefix = "IX_PLONK_CPU_PROFILE_"

type cpuProfileMemory struct {
	HeapAlloc, HeapSys, TotalAlloc, Sys uint64
	NumGC                               uint32
}

func cpuProfileMemorySnapshot() cpuProfileMemory {
	var m runtime.MemStats
	runtime.ReadMemStats(&m)
	return cpuProfileMemory{m.HeapAlloc, m.HeapSys, m.TotalAlloc, m.Sys, m.NumGC}
}

type cpuProfileRun struct {
	Kind                                                 string
	Index                                                int
	CPUProfiled                                          bool
	StartedUTC                                           string
	ProveSeconds, SerializeSeconds, VerifySeconds        float64
	ProfileStartSeconds, ProfileStopSeconds, WallSeconds float64
	Proof, SolidityProof                                 artifact
	ProofPath, SolidityProofPath                         string
	Before, After                                        cpuProfileMemory
}

type cpuProfileReport struct {
	Format, Scope, Stage                                string
	StartedUTC                                          string
	Complete                                            bool
	Artifacts, ManifestSHA256, WitnessPath              string
	ExpectedClaim                                       string
	SourceManifest                                      *manifest
	Witness, TestBinary, CPUProfile                     artifact
	TestBinaryPath, CPUProfilePath, CPUProfileScope     string
	GoVersion                                           string
	NumCPU, GOMAXPROCS, WarmupRuns, MeasuredRuns        int
	BuildInfo                                           *debug.BuildInfo
	Environment                                         map[string]string
	ValidationSeconds, WitnessSetupSeconds, WallSeconds float64
	LoadSeconds                                         map[string]float64
	Runs                                                []cpuProfileRun
}

func cpuProfileRequired(t *testing.T, name string) string {
	t.Helper()
	value := os.Getenv(cpuProfileEnvPrefix + name)
	if value == "" {
		t.Fatalf("%s%s must be explicitly configured", cpuProfileEnvPrefix, name)
	}
	return value
}

func cpuProfileDigest(text string) (string, error) {
	value, err := unhex(text, sha256.Size)
	if err != nil {
		return "", err
	}
	return hex.EncodeToString(value), nil
}

// Test executables have their own identity. This benchmark entry point trusts
// an externally pinned manifest; production loading retains its executable pin.
func cpuProfileManifest(dir, expectedSHA256 string) (*manifest, error) {
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
		return nil, fmt.Errorf("profiling manifest must be a regular file of at most 1 MiB")
	}
	data, err := io.ReadAll(io.LimitReader(f, (1<<20)+1))
	if err != nil {
		return nil, err
	}
	if len(data) > 1<<20 || fmt.Sprintf("%x", sha256.Sum256(data)) != expectedSHA256 {
		return nil, fmt.Errorf("profiling manifest differs from the explicitly trusted SHA-256")
	}
	var m manifest
	d := json.NewDecoder(bytes.NewReader(data))
	d.DisallowUnknownFields()
	if err := d.Decode(&m); err != nil {
		return nil, err
	}
	if err := d.Decode(new(any)); err != io.EOF {
		return nil, fmt.Errorf("trailing profiling manifest data")
	}
	if m.Format != artifactFormat || !m.KeysReady || m.Domain != 1<<24 || m.Constraints != 14689440 || m.PublicInputs != 2 || m.Commitments != 1 || len(m.Files) != 5 {
		return nil, fmt.Errorf("profiling requires the prepared classic-GLV 2^24 BN254 wrapper")
	}
	for _, digest := range []string{m.ExecutableSHA256, m.InnerVKSHA256, m.SRSBLAKE3} {
		if _, err := cpuProfileDigest(digest); err != nil {
			return nil, fmt.Errorf("invalid profiling manifest identity: %w", err)
		}
	}
	for _, name := range []string{"circuit.bin", "proving-key.bin", "verifying-key.bin", "vk.json", "PlonkVerifier.sol"} {
		want, ok := m.Files[name]
		if !ok || want.Bytes <= 0 {
			return nil, fmt.Errorf("missing profiling artifact %s", name)
		}
		if _, err := cpuProfileDigest(want.SHA256); err != nil {
			return nil, fmt.Errorf("invalid profiling artifact digest for %s", name)
		}
		stat, err := os.Stat(filepath.Join(dir, name))
		if err != nil {
			return nil, err
		}
		if !stat.Mode().IsRegular() || stat.Size() != want.Bytes {
			return nil, fmt.Errorf("profiling artifact %s has an invalid type or size", name)
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
func cpuProfileReadBinary(path string, want artifact, value io.ReaderFrom) error {
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

func cpuProfileProve(ccs constraint.ConstraintSystem, pk plonk.ProvingKey, w witness.Witness, profilePath string, index int) (proof plonk.Proof, seconds, startSeconds, stopSeconds float64, err error) {
	var profileFile *os.File
	if profilePath != "" {
		started := time.Now()
		profileFile, err = os.OpenFile(profilePath, os.O_CREATE|os.O_EXCL|os.O_WRONLY, 0600)
		if err != nil {
			return
		}
		if err = pprof.StartCPUProfile(profileFile); err != nil {
			profileFile.Close()
			return
		}
		startSeconds = time.Since(started).Seconds()
		defer func() {
			started := time.Now()
			pprof.StopCPUProfile()
			if closeErr := profileFile.Close(); err == nil {
				err = closeErr
			}
			stopSeconds = time.Since(started).Seconds()
		}()
	}
	started := time.Now()
	pprof.Do(context.Background(), pprof.Labels("workload", "bn254-plonk-2p24", "run", strconv.Itoa(index)), func(context.Context) {
		proof, err = plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	})
	seconds = time.Since(started).Seconds()
	return
}

func TestBN254CPUProfile(t *testing.T) {
	if os.Getenv("IX_PLONK_CPU_PROFILE") != "1" {
		t.Skip("set IX_PLONK_CPU_PROFILE=1 and explicit artifact/claim pins for full 2^24 proving")
	}
	if os.Getenv("GOMAXPROCS") != "" {
		t.Fatal("unset GOMAXPROCS to retain the default CPU parallelism")
	}
	dir := cpuProfileRequired(t, "ARTIFACTS")
	expectedManifest, err := cpuProfileDigest(cpuProfileRequired(t, "MANIFEST_SHA256"))
	if err != nil {
		t.Fatal(err)
	}
	expectedClaim, err := cpuProfileDigest(cpuProfileRequired(t, "EXPECTED_CLAIM"))
	if err != nil {
		t.Fatal(err)
	}
	witnessPath := cpuProfileRequired(t, "WITNESS")
	out := cpuProfileRequired(t, "OUTPUT")
	measured := 3
	if value := os.Getenv(cpuProfileEnvPrefix + "RUNS"); value != "" {
		measured, err = strconv.Atoi(value)
		if err != nil || (measured != 2 && measured != 3) {
			t.Fatal("IX_PLONK_CPU_PROFILE_RUNS must be 2 or 3")
		}
	}
	if err := os.MkdirAll(filepath.Dir(out), 0700); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(out, 0700); err != nil {
		t.Fatalf("profiling output directory must be new: %v", err)
	}
	started := time.Now()
	report := cpuProfileReport{
		Format: "ix-bn254-plonk-cpu-verifying key-v1",
		Scope:  "Authenticated existing 2^24 artifacts; one unmeasured warmup, followed by measured proofs in one process. CS/PK/VK/witness reused; fresh gnark randomness each proof; default CPU parallelism and natural GC. No accelerator, circuit compilation, SRS conversion or key setup.",
		Stage:  "artifact-validation", StartedUTC: started.UTC().Format(time.RFC3339Nano),
		Artifacts: dir, ManifestSHA256: expectedManifest, WitnessPath: witnessPath,
		ExpectedClaim: expectedClaim, GoVersion: runtime.Version(),
		NumCPU: runtime.NumCPU(), GOMAXPROCS: runtime.GOMAXPROCS(0),
		WarmupRuns: 1, MeasuredRuns: measured,
		CPUProfilePath:  filepath.Join(out, "cpu.pprof"),
		CPUProfileScope: "Measured run 1 only: StartCPUProfile immediately before plonk.Prove, StopCPUProfile immediately after it. Artifact/witness preparation, verification, proof serialization, warmup and other measured runs are excluded. ProveSeconds excludes profiler startup/shutdown.",
		LoadSeconds:     make(map[string]float64), Environment: make(map[string]string),
	}
	report.BuildInfo, _ = debug.ReadBuildInfo()
	for _, name := range []string{"GOMAXPROCS", "GOGC", "GOMEMLIMIT", "GODEBUG", "CUDA_VISIBLE_DEVICES"} {
		if value, present := os.LookupEnv(name); present {
			report.Environment[name] = value
		}
	}
	defer func() {
		report.WallSeconds = time.Since(started).Seconds()
		report.Complete = report.Stage == "complete" && !t.Failed()
		if err := writeJSON(filepath.Join(out, "report.json"), &report); err != nil {
			t.Error(err)
		}
	}()
	report.TestBinaryPath, err = os.Executable()
	if err != nil {
		t.Fatal(err)
	}
	report.TestBinary, err = fileHash(report.TestBinaryPath)
	if err != nil {
		t.Fatal(err)
	}
	validationStarted := time.Now()
	m, err := cpuProfileManifest(dir, expectedManifest)
	if err != nil {
		t.Fatal(err)
	}
	report.SourceManifest = m
	report.ValidationSeconds = time.Since(validationStarted).Seconds()
	report.Stage = "artifact-load"
	ccs := plonk.NewCS(curveID)
	pk := plonk.NewProvingKey(curveID)
	vk := plonk.NewVerifyingKey(curveID)
	for _, entry := range []struct {
		name  string
		value io.ReaderFrom
	}{{"circuit.bin", ccs}, {"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
		loadStarted := time.Now()
		if err := cpuProfileReadBinary(filepath.Join(dir, entry.name), m.Files[entry.name], entry.value); err != nil {
			t.Fatal(err)
		}
		report.LoadSeconds[entry.name] = time.Since(loadStarted).Seconds()
	}
	loadStarted := time.Now()
	p, err := loadVerifyingKey(filepath.Join(dir, "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := m.checkFile(dir, "vk.json"); err != nil {
		t.Fatal(err)
	}
	report.LoadSeconds["vk.json"] = time.Since(loadStarted).Seconds()
	if ccs.GetNbConstraints() != m.Constraints || ccs.GetNbPublicVariables() != m.PublicInputs || ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints()+ccs.GetNbPublicVariables())) != m.Domain || len(ccs.GetCommitments().CommitmentIndexes()) != m.Commitments {
		t.Fatal("loaded circuit metadata differs from the authenticated manifest")
	}
	nativePK := pk.(*plonkbn254.ProvingKey)
	nativeVK := vk.(*plonkbn254.VerifyingKey)
	if nativePK.Accelerator() != nil || nativePK.Vk == nil || uint64(len(nativePK.Kzg.G1)) != m.Domain+3 || uint64(len(nativePK.KzgLagrange.G1)) != m.Domain || nativeVK.Size != m.Domain || nativeVK.NbPublicVariables != 2 || len(nativeVK.Qcp) != m.Commitments {
		t.Fatal("loaded key shape differs or an accelerator is attached")
	}
	pkVerifierHash := sha256.New()
	pkVerifierBytes, err := nativePK.Vk.WriteTo(pkVerifierHash)
	if err != nil {
		t.Fatal(err)
	}
	if pkVerifierBytes != m.Files["verifying-key.bin"].Bytes || hex.EncodeToString(pkVerifierHash.Sum(nil)) != m.Files["verifying-key.bin"].SHA256 {
		t.Fatal("proving key embeds a different verifying key")
	}
	g1, err := p.Generator.native()
	if err != nil {
		t.Fatal(err)
	}
	g2, err := g2Keys(p.OuterKeys)
	if err != nil {
		t.Fatal(err)
	}
	if !nativeVK.Kzg.G1.Equal(&g1) || !nativeVK.Kzg.G2[0].Equal(&g2[0]) || !nativeVK.Kzg.G2[1].Equal(&g2[1]) {
		t.Fatal("verifying key anchors differ from the authenticated verifying key")
	}
	report.Stage = "witness-setup"
	witnessStarted := time.Now()
	stat, err := os.Stat(witnessPath)
	if err != nil || !stat.Mode().IsRegular() || stat.Size() > 16<<20 {
		t.Fatal("profiling witness must be a regular file of at most 16 MiB")
	}
	report.Witness, err = fileHash(witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	assignment, err := witnessAssignment(p, witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	if after, err := fileHash(witnessPath); err != nil || after != report.Witness {
		t.Fatal("profiling witness changed during loading")
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	digest, _ := hex.DecodeString(expectedClaim)
	expectedPublic, err := frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, curveID.ScalarField(), frontend.PublicOnly())
	if err != nil {
		t.Fatal(err)
	}
	actualPublic, err := w.Public()
	if err != nil {
		t.Fatal(err)
	}
	actualBytes, err := actualPublic.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	expectedBytes, err := expectedPublic.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(actualBytes, expectedBytes) {
		t.Fatal("witness claim differs from the independently expected claim")
	}
	report.WitnessSetupSeconds = time.Since(witnessStarted).Seconds()
	seenProofs := make(map[string]bool)
	for index := 0; index <= measured; index++ {
		kind := "measured"
		if index == 0 {
			kind = "warmup"
		}
		report.Stage = fmt.Sprintf("%s-%d", kind, index)
		t.Logf("stage=%s retained_cs_pk_vk=true accelerator=none gomaxprocs=%d", report.Stage, runtime.GOMAXPROCS(0))
		runStarted := time.Now()
		row := cpuProfileRun{Kind: kind, Index: index, StartedUTC: runStarted.UTC().Format(time.RFC3339Nano), CPUProfiled: index == 1, Before: cpuProfileMemorySnapshot()}
		profilePath := ""
		if row.CPUProfiled {
			profilePath = report.CPUProfilePath
		}
		proof, proveSeconds, profileStart, profileStop, err := cpuProfileProve(ccs, pk, w, profilePath, index)
		if err != nil {
			t.Fatal(err)
		}
		row.ProveSeconds, row.ProfileStartSeconds, row.ProfileStopSeconds = proveSeconds, profileStart, profileStop
		serializeStarted := time.Now()
		var encoded bytes.Buffer
		if _, err := proof.WriteTo(&encoded); err != nil {
			t.Fatal(err)
		}
		decoded, err := decodeProof(encoded.Bytes(), m.Commitments)
		if err != nil {
			t.Fatal(err)
		}
		solidityBytes := decoded.MarshalSolidity()
		row.SerializeSeconds = time.Since(serializeStarted).Seconds()
		verifyStarted := time.Now()
		if err := plonk.Verify(decoded, vk, expectedPublic, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
			t.Fatal(err)
		}
		row.VerifySeconds = time.Since(verifyStarted).Seconds()
		row.Proof = artifact{SHA256: fmt.Sprintf("%x", sha256.Sum256(encoded.Bytes())), Bytes: int64(encoded.Len())}
		row.SolidityProof = artifact{SHA256: fmt.Sprintf("%x", sha256.Sum256(solidityBytes)), Bytes: int64(len(solidityBytes))}
		if seenProofs[row.Proof.SHA256] {
			t.Fatal("repeated proof bytes despite fresh gnark blinding")
		}
		seenProofs[row.Proof.SHA256] = true
		row.ProofPath = filepath.Join(out, fmt.Sprintf("%s-%d.proof.bin", kind, index))
		row.SolidityProofPath = filepath.Join(out, fmt.Sprintf("%s-%d.proof.solidity.bin", kind, index))
		if err := os.WriteFile(row.ProofPath, encoded.Bytes(), 0600); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(row.SolidityProofPath, solidityBytes, 0600); err != nil {
			t.Fatal(err)
		}
		row.After = cpuProfileMemorySnapshot()
		row.WallSeconds = time.Since(runStarted).Seconds()
		report.Runs = append(report.Runs, row)
		if row.CPUProfiled {
			report.CPUProfile, err = fileHash(report.CPUProfilePath)
			if err != nil {
				t.Fatal(err)
			}
		}
		if err := writeJSON(filepath.Join(out, "report.json"), &report); err != nil {
			t.Fatal(err)
		}
		t.Logf("stage=%s prove_seconds=%.6f verify_seconds=%.6f cpu_profiled=%t proof_sha256=%s", report.Stage, row.ProveSeconds, row.VerifySeconds, row.CPUProfiled, row.Proof.SHA256)
	}
	report.Stage = "complete"
}
