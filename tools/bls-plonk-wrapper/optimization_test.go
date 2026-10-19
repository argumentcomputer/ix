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

type optimizedCircuit struct {
	Inner   wrapperCircuit
	Options circuitOptions `gnark:"-"`
}

func (c *optimizedCircuit) Define(api frontend.API) error {
	return c.Inner.constrainWithOptions(api, 6, c.Options)
}

func TestOptimizationSizing(t *testing.T) {
	if os.Getenv("IX_PLONK_SIZE") != "1" {
		t.Skip("set IX_PLONK_SIZE=1 for full variant compilation")
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
	type measurement struct {
		Variant                                 string
		Constraints, Rows, GapTo24, Commitments int
		Domain                                  uint64
		Seconds                                 float64
	}
	var measurements []measurement
	for _, variant := range []struct {
		name    string
		options circuitOptions
	}{
		{"baseline", circuitOptions{}},
		{"batched", circuitOptions{batchPairings: true}},
		{"classic-glv", circuitOptions{classicGLV: true}},
		{"batched-classic-glv", circuitOptions{batchPairings: true, classicGLV: true}},
	} {
		if selectVariant := os.Getenv("IX_PLONK_SIZE_VARIANT"); selectVariant != "" && selectVariant != variant.name {
			continue
		}
		runtime.GC()
		start := time.Now()
		ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder,
			&optimizedCircuit{Inner: *newCircuit(p), Options: variant.options})
		if err != nil {
			t.Fatal(err)
		}
		rows := ccs.GetNbConstraints() + ccs.GetNbPublicVariables()
		row := measurement{variant.name, ccs.GetNbConstraints(), rows, rows - (1 << 24), len(ccs.GetCommitments().CommitmentIndexes()), ecc.NextPowerOfTwo(uint64(rows)), time.Since(start).Seconds()}
		measurements = append(measurements, row)
		t.Logf("%s: constraints=%d rows=%d gap_to_2p24=%d domain=%d seconds=%.2f", row.Variant, row.Constraints, row.Rows, row.GapTo24, row.Domain, row.Seconds)
		if path := os.Getenv("IX_PLONK_SIZE_REPORT"); path != "" {
			encoded, err := json.MarshalIndent(measurements, "", "  ")
			if err != nil {
				t.Fatal(err)
			}
			if err := os.WriteFile(path, encoded, 0600); err != nil {
				t.Fatal(err)
			}
		}
	}
}
