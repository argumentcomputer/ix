package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"runtime"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

type componentCircuit struct {
	Inner   wrapperCircuit
	Phase   int            `gnark:"-"`
	Options circuitOptions `gnark:"-"`
}

func (c *componentCircuit) Define(api frontend.API) error {
	return c.Inner.constrainWithOptions(api, c.Phase, c.Options)
}

func TestComponentSizing(t *testing.T) {
	if os.Getenv("IX_PLONK_SIZE") != "1" {
		t.Skip("set IX_PLONK_SIZE=1 for full component compilation")
	}
	path := os.Getenv("IX_PLONK_SIZE_VK")
	if path == "" {
		fixture := "outer"
		if curveID == ecc.BN254 {
			fixture = "bn254"
		}
		path = filepath.Join("testdata", fixture, "vk.json")
	}
	p, err := loadVerifyingKey(path)
	if err != nil {
		t.Fatal(err)
	}
	options := circuitOptions{classicGLV: true}
	switch variant := os.Getenv("IX_PLONK_SIZE_VARIANT"); variant {
	case "", "classic-glv":
	case "baseline":
		options.classicGLV = false
	default:
		t.Fatalf("component sizing requires baseline or classic-glv, got %q", variant)
	}
	type measurement struct {
		Phase                    string
		Constraints, Commitments int
		Domain                   uint64
		Seconds                  float64
	}
	var measurements []measurement
	for phase, name := range []string{"point validation and public binding", "transcript", "scalar relation", "opening MSMs", "outer pairing", "deferred pairing"} {
		runtime.GC()
		start := time.Now()
		ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder,
			&componentCircuit{Inner: *newCircuit(p), Phase: phase + 1, Options: options}, frontend.IgnoreUnconstrainedInputs())
		if err != nil {
			t.Fatal(err)
		}
		row := measurement{name, ccs.GetNbConstraints(), len(ccs.GetCommitments().CommitmentIndexes()), ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + 2)), time.Since(start).Seconds()}
		measurements = append(measurements, row)
		t.Logf("through %s: constraints=%d N=%d commitments=%d seconds=%.2f", row.Phase, row.Constraints, row.Domain, row.Commitments, row.Seconds)
	}
	if path := os.Getenv("IX_PLONK_SIZE_REPORT"); path != "" {
		data, err := json.MarshalIndent(measurements, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, data, 0600); err != nil {
			t.Fatal(err)
		}
	}
}
