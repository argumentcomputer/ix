package main

import (
	"crypto/sha256"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"runtime"
	"runtime/debug"
	"sort"
	"strconv"
	"strings"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	g16 "github.com/consensys/gnark/backend/groth16/bn254"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/consensys/gnark/test/unsafekzg"
)

type terminalSample struct {
	ProveSeconds  float64 `json:"proveSeconds"`
	VerifySeconds float64 `json:"verifySeconds"`
	NativeBytes   int64   `json:"nativeBytes"`
	SolidityBytes int     `json:"solidityBytes"`
	EnvelopeBytes int64   `json:"envelopeBytes"`
}

type terminalMeasurement struct {
	System             string           `json:"system"`
	Device             string           `json:"device"`
	PinKeys            bool             `json:"pinKeys"`
	Constraints        int              `json:"constraints"`
	Domain             uint64           `json:"domain"`
	Commitments        int              `json:"commitments"`
	LoadSeconds        float64          `json:"openSeconds"`
	First              terminalSample   `json:"first"`
	Warm               []terminalSample `json:"warm"`
	MedianProveSeconds float64          `json:"medianProveSeconds"`
}

type terminalComparison struct {
	Scope               string                `json:"scope"`
	Setup               string                `json:"setup"`
	Schema              artifact              `json:"schema"`
	Witness             artifact              `json:"witness"`
	GoVersion           string                `json:"goVersion"`
	CPUs                int                   `json:"cpus"`
	GOMAXPROCS          int                   `json:"gomaxprocs"`
	PlonkCompileSeconds float64               `json:"plonkCompileSeconds"`
	PlonkSRSSeconds     float64               `json:"plonkSRSSeconds"`
	PlonkSetupSeconds   float64               `json:"plonkSetupSeconds"`
	Groth16KeysReused   bool                  `json:"groth16KeysReused"`
	PlonkKeysReused     bool                  `json:"plonkKeysReused"`
	Results             []terminalMeasurement `json:"results"`
}

func TestBN254TerminalComparison(t *testing.T) {
	if os.Getenv("IX_TERMINAL_COMPARE") != "1" {
		t.Skip("set IX_TERMINAL_COMPARE=1 for the matched terminal benchmark")
	}
	out := os.Getenv("IX_TERMINAL_COMPARE_OUT")
	grothDir := os.Getenv("IX_TERMINAL_GROTH16_ARTIFACTS")
	if out == "" || grothDir == "" {
		t.Fatal("set IX_TERMINAL_COMPARE_OUT and IX_TERMINAL_GROTH16_ARTIFACTS")
	}
	input := os.Getenv("IX_TERMINAL_COMPARE_INPUT")
	if input == "" {
		input = filepath.Join("testdata", "bn254")
	}
	repeats := 3
	if value := os.Getenv("IX_TERMINAL_COMPARE_REPEATS"); value != "" {
		var err error
		repeats, err = strconv.Atoi(value)
		if err != nil || repeats < 1 || repeats > 10 {
			t.Fatal("repeats must be in 1..10")
		}
	}
	devices := strings.Split(os.Getenv("IX_TERMINAL_COMPARE_DEVICES"), ",")
	if devices[0] == "" {
		devices = []string{"cpu"}
	}
	for _, device := range devices {
		if device != "cpu" && device != "cuda" {
			t.Fatal("devices must be cpu or cuda")
		}
	}
	keyPath, witnessPath := filepath.Join(input, "vk.json"), filepath.Join(input, "witness.json")
	p, err := loadVerifyingKey(keyPath)
	if err != nil {
		t.Fatal(err)
	}
	assignment, err := witnessAssignment(p, witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	public, err := w.Public()
	if err != nil {
		t.Fatal(err)
	}
	report := terminalComparison{Scope: "actual Init recursive KZG verifier and witness; terminal proving only", Setup: "Groth16 development keys; PLONK setup is recorded by the selected cache",
		GoVersion: runtime.Version(), CPUs: runtime.NumCPU(), GOMAXPROCS: runtime.GOMAXPROCS(0), Groth16KeysReused: true}
	report.Schema, err = fileHash(keyPath)
	if err != nil {
		t.Fatal(err)
	}
	report.Witness, err = fileHash(witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	gm := new(groth16Manifest)
	if err := decodeJSON(filepath.Join(grothDir, "manifest.json"), gm); err != nil {
		t.Fatal(err)
	}
	if err := gm.validate(); err != nil {
		t.Fatal(err)
	}
	if gm.InnerVK != report.Schema.SHA256 || gm.Setup != "development" {
		t.Fatal("Groth16 cache does not match the comparison fixture")
	}
	plonkDir := filepath.Join(out, "plonk")
	externalPlonk := os.Getenv("IX_TERMINAL_PLONK_ARTIFACTS")
	if externalPlonk != "" {
		plonkDir = externalPlonk
		metadata, err := fileHash(filepath.Join(plonkDir, "manifest.json"))
		if err != nil {
			t.Fatal(err)
		}
		if metadata.SHA256 != os.Getenv("IX_TERMINAL_PLONK_MANIFEST_SHA256") {
			t.Fatal("PLONK manifest differs from the comparison pin")
		}
		var m manifest
		if err := decodeJSON(filepath.Join(plonkDir, "manifest.json"), &m); err != nil {
			t.Fatal(err)
		}
		if m.InnerVKSHA256 != report.Schema.SHA256 || !m.KeysReady || m.PublicInputs != 2 {
			t.Fatal("PLONK artifacts describe another circuit")
		}
		for _, name := range []string{"vk.json", "circuit.bin", "proving-key.bin", "verifying-key.bin"} {
			if err := m.checkFile(plonkDir, name); err != nil {
				t.Fatal(err)
			}
		}
		report.PlonkKeysReused = true
	} else if _, err := os.Stat(filepath.Join(plonkDir, "ready.json")); os.IsNotExist(err) {
		start := time.Now()
		ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, newCircuit(p))
		if err != nil {
			t.Fatal(err)
		}
		report.PlonkCompileSeconds = time.Since(start).Seconds()
		if err := atomicFile(filepath.Join(plonkDir, "circuit.bin"), func(w io.Writer) error { _, err := ccs.WriteTo(w); return err }); err != nil {
			t.Fatal(err)
		}
		t.Logf("PLONK constraints=%d domain=%d; Groth16 constraints=%d domain=%d", ccs.GetNbConstraints(), ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints()+ccs.GetNbPublicVariables())), gm.Constraints, gm.Domain)
		if os.Getenv("IX_TERMINAL_COMPARE_COMPILE_ONLY") == "1" {
			return
		}
		start = time.Now()
		srs, lagrange, err := unsafekzg.NewSRS(ccs)
		if err != nil {
			t.Fatal(err)
		}
		report.PlonkSRSSeconds = time.Since(start).Seconds()
		start = time.Now()
		pk, vk, err := plonk.Setup(ccs, srs, lagrange)
		if err != nil {
			t.Fatal(err)
		}
		report.PlonkSetupSeconds = time.Since(start).Seconds()
		for _, item := range []struct {
			name  string
			value io.WriterTo
		}{{"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
			if err := atomicFile(filepath.Join(plonkDir, item.name), func(w io.Writer) error { _, err := item.value.WriteTo(w); return err }); err != nil {
				t.Fatal(err)
			}
		}
		if err := writeJSON(filepath.Join(plonkDir, "ready.json"), report); err != nil {
			t.Fatal(err)
		}
	} else if err != nil {
		t.Fatal(err)
	}
	if externalPlonk == "" {
		var cached terminalComparison
		if err := decodeJSON(filepath.Join(plonkDir, "ready.json"), &cached); err != nil {
			t.Fatal(err)
		}
		if cached.Schema != report.Schema || cached.Witness != report.Witness {
			t.Fatal("PLONK cache belongs to another fixture")
		}
		report.PlonkCompileSeconds, report.PlonkSRSSeconds, report.PlonkSetupSeconds = cached.PlonkCompileSeconds, cached.PlonkSRSSeconds, cached.PlonkSetupSeconds
	}
	if os.Getenv("IX_TERMINAL_COMPARE_PREPARE_ONLY") == "1" {
		return
	}
	systems := strings.Split(os.Getenv("IX_TERMINAL_COMPARE_SYSTEMS"), ",")
	if systems[0] == "" {
		systems = []string{"groth16", "plonk"}
	}
	for _, system := range systems {
		if system != "groth16" && system != "plonk" {
			t.Fatal("systems must be groth16 or plonk")
		}
	}
	debug.FreeOSMemory()
	for _, device := range devices {
		for _, system := range systems {
			measurement := terminalMeasurement{System: system, Device: device, PinKeys: system == "groth16" && device == "cuda" && os.Getenv("IX_GROTH16_PIN_KEY") == "1"}
			start := time.Now()
			var prove func() (terminalSample, error)
			var close func()
			if system == "groth16" {
				t.Setenv("IX_GROTH16_BACKEND", device)
				engine, err := newGroth16Engine(groth16Backend{CUDA: device == "cuda", PinKeys: measurement.PinKeys, Library: os.Getenv("ICICLE_BACKEND_INSTALL_DIR")})
				if err != nil {
					t.Fatal(err)
				}
				ccs, vk := groth16.NewCS(curveID), new(g16.VerifyingKey)
				for _, item := range []struct {
					name  string
					value io.ReaderFrom
				}{{"circuit.bin", ccs}, {"proving-key.bin", engine.key}, {"verifying-key.bin", vk}} {
					if err := readBinary(filepath.Join(grothDir, item.name), item.value); err != nil {
						engine.close()
						t.Fatal(err)
					}
				}
				close = engine.close
				measurement.Constraints, measurement.Domain, measurement.Commitments = gm.Constraints, gm.Domain, gm.Commitments
				prove = func() (terminalSample, error) {
					start := time.Now()
					proof, err := engine.prove(ccs, w)
					if err != nil {
						return terminalSample{}, err
					}
					result := terminalSample{ProveSeconds: time.Since(start).Seconds()}
					start = time.Now()
					err = groth16.Verify(proof, vk, public, backend.WithVerifierHashToFieldFunction(sha256.New()))
					result.VerifySeconds = time.Since(start).Seconds()
					if err != nil {
						return result, err
					}
					result.NativeBytes, err = proof.WriteTo(io.Discard)
					result.SolidityBytes = len(proof.(*g16.Proof).MarshalSolidity())
					result.EnvelopeBytes = 40 + result.NativeBytes
					return result, err
				}
			} else {
				t.Setenv("IX_PLONK_BACKEND", device)
				ccs := plonk.NewCS(curveID)
				pk, vk := plonk.NewProvingKey(curveID), plonk.NewVerifyingKey(curveID)
				for _, item := range []struct {
					name  string
					value io.ReaderFrom
				}{{"circuit.bin", ccs}, {"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
					if err := readBinary(filepath.Join(plonkDir, item.name), item.value); err != nil {
						t.Fatal(err)
					}
				}
				cleanup, err := configureBackend(pk, backendConfig{CUDA: device == "cuda", MemoryBytes: 64 << 30})
				if err != nil {
					t.Fatal(err)
				}
				close = func() {
					if err := cleanup(); err != nil {
						t.Error(err)
					}
				}
				measurement.Constraints, measurement.Domain, measurement.Commitments = ccs.GetNbConstraints(), vk.(*nativeVerifyingKey).Size, len(vk.(*nativeVerifyingKey).Qcp)
				prove = func() (terminalSample, error) {
					start := time.Now()
					proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
					if err != nil {
						return terminalSample{}, err
					}
					result := terminalSample{ProveSeconds: time.Since(start).Seconds()}
					start = time.Now()
					err = plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK))
					result.VerifySeconds = time.Since(start).Seconds()
					if err != nil {
						return result, err
					}
					result.NativeBytes, err = proof.WriteTo(io.Discard)
					result.SolidityBytes = len(proof.(*nativeProof).MarshalSolidity())
					result.EnvelopeBytes = 40 + result.NativeBytes
					return result, err
				}
			}
			measurement.LoadSeconds = time.Since(start).Seconds()
			func() {
				defer close()
				var err error
				measurement.First, err = prove()
				if err != nil {
					t.Fatal(err)
				}
				for range repeats {
					sample, err := prove()
					if err != nil {
						t.Fatal(err)
					}
					measurement.Warm = append(measurement.Warm, sample)
				}
			}()
			times := make([]float64, len(measurement.Warm))
			for i, sample := range measurement.Warm {
				times[i] = sample.ProveSeconds
			}
			sort.Float64s(times)
			measurement.MedianProveSeconds = times[len(times)/2]
			if len(times)%2 == 0 {
				measurement.MedianProveSeconds = (times[len(times)/2-1] + times[len(times)/2]) / 2
			}
			report.Results = append(report.Results, measurement)
			if err := writeJSON(filepath.Join(out, "comparison.json"), report); err != nil {
				t.Fatal(err)
			}
			t.Logf("%s %s: median=%.3fs native=%d envelope=%d Solidity=%d", system, device, measurement.MedianProveSeconds, measurement.First.NativeBytes, measurement.First.EnvelopeBytes, measurement.First.SolidityBytes)
			prove, close = nil, nil
			debug.FreeOSMemory()
		}
	}
	fmt.Println("Matched comparison:", filepath.Join(out, "comparison.json"))
}
