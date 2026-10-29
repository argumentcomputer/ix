//go:build (plonk && groth16) || (!plonk && !groth16)

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"runtime"
	"runtime/pprof"
	"strconv"
	"strings"
	"testing"
	"time"
)

func TestBN254FinalComparison(t *testing.T) {
	if os.Getenv("IX_FINAL_COMPARE") != "1" {
		t.Skip("set IX_FINAL_COMPARE=1 with prepared artifact and manifest pins")
	}
	out := os.Getenv("IX_FINAL_COMPARE_OUT")
	if out == "" {
		t.Fatal("IX_FINAL_COMPARE_OUT is required")
	}
	if err := os.MkdirAll(out, 0755); err != nil {
		t.Fatal(err)
	}
	input := os.Getenv("IX_FINAL_COMPARE_INPUT")
	if input == "" {
		input = filepath.Join("testdata", "bn254")
	}
	schema, err := readDescription(filepath.Join(input, "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	witness, err := readDescription(filepath.Join(input, "witness.json"))
	if err != nil {
		t.Fatal(err)
	}
	var assignment witnessJSON
	if err := json.Unmarshal(witness, &assignment); err != nil {
		t.Fatal(err)
	}
	claim, err := unhex(assignment.ClaimDigest, 32)
	if err != nil {
		t.Fatal(err)
	}
	schemaHash := sha256.Sum256(schema)
	witnessHash := sha256.Sum256(witness)
	count := 3
	if value := os.Getenv("IX_FINAL_COMPARE_REPEATS"); value != "" {
		count, err = strconv.Atoi(value)
		if err != nil || count < 1 || count > 10 {
			t.Fatal("repeats must be in 1..10")
		}
	}
	selectValues := func(name, fallback string) []string {
		value := os.Getenv(name)
		if value == "" {
			value = fallback
		}
		return strings.Split(value, ",")
	}
	boolean := func(name string) bool {
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
	report := map[string]any{"scope": "final proving, verification, and serialization through retained production provers", "go": runtime.Version(), "cpus": runtime.NumCPU(), "gomaxprocs": runtime.GOMAXPROCS(0), "schemaSHA256": hex.EncodeToString(schemaHash[:]), "witnessSHA256": hex.EncodeToString(witnessHash[:])}
	var runs []map[string]any
	for _, device := range selectValues("IX_FINAL_COMPARE_DEVICES", "cpu") {
		if device != "cpu" && device != "cuda" {
			t.Fatal("devices must be cpu or cuda")
		}
		for _, system := range selectValues("IX_FINAL_COMPARE_SYSTEMS", "groth16,plonk") {
			if system != "plonk" && system != "groth16" {
				t.Fatal("systems must be plonk or groth16")
			}
			prefix := "IX_FINAL_" + strings.ToUpper(system)
			dir := os.Getenv(prefix + "_ARTIFACTS")
			if dir == "" {
				t.Fatalf("%s_ARTIFACTS is required", prefix)
			}
			metadata, err := readDescription(filepath.Join(dir, "manifest.json"))
			if err != nil {
				t.Fatal(err)
			}
			hash := sha256.Sum256(metadata)
			if hex.EncodeToString(hash[:]) != os.Getenv(prefix+"_MANIFEST_SHA256") {
				t.Fatalf("%s manifest differs from its pin", system)
			}
			started := time.Now()
			var open func() (retainedProver, error)
			var inner string
			var constraints int
			var domain uint64
			if system == "plonk" {
				var m manifest
				if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
					t.Fatal(err)
				}
				inner, constraints, domain = m.InnerVKSHA256, m.Constraints, m.Domain
				open = func() (retainedProver, error) {
					return openProver(dir, metadata, backendConfig{CUDA: device == "cuda", MemoryBytes: 64 << 30})
				}
			} else {
				var m groth16Manifest
				if err := decodeReader(bytes.NewReader(metadata), &m); err != nil {
					t.Fatal(err)
				}
				inner, constraints, domain = m.InnerVK, m.Constraints, m.Domain
				open = func() (retainedProver, error) {
					return openGroth16(dir, metadata, groth16Backend{CUDA: device == "cuda", Library: os.Getenv("ICICLE_BACKEND_INSTALL_DIR")})
				}
			}
			if inner != hex.EncodeToString(schemaHash[:]) {
				t.Fatal("artifacts describe another verifier schema")
			}
			prover, err := open()
			if err != nil {
				t.Fatal(err)
			}
			run := map[string]any{"system": system, "device": device, "pinKeys": false, "constraints": constraints, "domain": domain, "manifestSHA256": hex.EncodeToString(hash[:]), "openSeconds": time.Since(started).Seconds()}
			func() {
				defer func() {
					if err := prover.close(); err != nil {
						t.Error(err)
					}
				}()
				if _, _, err := prover.prove(witness, claim); err != nil {
					t.Fatal(err)
				}
				if boolean("IX_FINAL_COMPARE_CPU_PROFILE") {
					path := filepath.Join(out, system+"-"+device+".pprof")
					file, err := os.Create(path)
					if err != nil {
						t.Fatal(err)
					}
					defer file.Close()
					if err := pprof.StartCPUProfile(file); err != nil {
						t.Fatal(err)
					}
					defer pprof.StopCPUProfile()
					run["cpuProfile"] = path
				}
				times := make([]float64, 0, count)
				for i := 0; i < count; i++ {
					started := time.Now()
					native, solidity, err := prover.prove(witness, claim)
					if err != nil {
						t.Fatal(err)
					}
					times = append(times, time.Since(started).Seconds())
					run["nativeBytes"], run["solidityBytes"] = len(native), len(solidity)
				}
				run["proveVerifySeconds"] = times
			}()
			runs = append(runs, run)
			report["runs"] = runs
			if err := writeJSON(filepath.Join(out, "report.json"), report); err != nil {
				t.Fatal(err)
			}
			t.Log(fmt.Sprint(run))
		}
	}
}
