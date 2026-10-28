package main

import (
	"bytes"
	"encoding/json"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	bn "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark/test"
)

func TestBN254RustPointEncodingVectors(t *testing.T) {
	var diagnostic struct {
		Challenges, Compositions, Quotients, PointEncodings []string
		PublicAccumulator, OuterL, OuterR                   string
	}
	var witness witnessJSON
	if err := decodeJSON(filepath.Join("testdata", "bn254", "witness-diagnostic.json"), &diagnostic); err != nil {
		t.Fatal(err)
	}
	if err := decodeJSON(filepath.Join("testdata", "bn254", "witness.json"), &witness); err != nil {
		t.Fatal(err)
	}
	if len(diagnostic.PointEncodings) != len(witness.Points) {
		t.Fatal("point vector lengths differ")
	}
	for i, input := range witness.Points {
		point, err := input.native()
		if err != nil {
			t.Fatal(err)
		}
		expected, err := unhex(diagnostic.PointEncodings[i], 32)
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(encodePoint(point), expected) {
			t.Fatalf("Rust point encoding differs at %d", i)
		}
	}
}

func TestBN254FullVerifierRejectsTampering(t *testing.T) {
	p, err := loadVerifyingKey(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	assignment := func() *wrapperCircuit {
		w, err := witnessAssignment(p, filepath.Join("testdata", "bn254", "witness.json"))
		if err != nil {
			t.Fatal(err)
		}
		return w
	}
	if err := test.IsSolved(newCircuit(p), assignment(), curveID.ScalarField()); err != nil {
		t.Fatal(err)
	}
	for _, kind := range []string{"claim", "evaluation", "commitment", "deferred", "deferred-key", "outer-key"} {
		w := assignment()
		vkCopy := *p
		switch kind {
		case "claim":
			w.Claim[0] = new(big.Int).Add(w.Claim[0].(*big.Int), big.NewInt(1))
		case "evaluation":
			w.Values[1] = new(big.Int).Add(w.Values[1].(*big.Int), big.NewInt(1))
		case "commitment":
			_, _, g, _ := bn.Generators()
			w.Points[0] = newCircuitG1(g)
		case "deferred":
			_, _, g, _ := bn.Generators()
			w.Deferred[0] = newCircuitG1(g)
		case "deferred-key":
			vkCopy.DeferredKeys = []string{p.DeferredKeys[0], p.DeferredKeys[0]}
		case "outer-key":
			vkCopy.OuterKeys = []string{p.OuterKeys[0], p.OuterKeys[0]}
		}
		if err := test.IsSolved(newCircuit(&vkCopy), w, curveID.ScalarField()); err == nil {
			t.Fatalf("accepted %s mutation", kind)
		}
	}
}

func TestVerifyingKeyRequiresExplicitSchema(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	for _, field := range []string{"accumulatorCount", "claims", "publics"} {
		for _, null := range []bool{false, true} {
			var fields map[string]json.RawMessage
			if err := json.Unmarshal(data, &fields); err != nil {
				t.Fatal(err)
			}
			if null {
				fields[field] = json.RawMessage("null")
			} else {
				delete(fields, field)
			}
			encoded, err := json.Marshal(fields)
			if err != nil {
				t.Fatal(err)
			}
			path := filepath.Join(t.TempDir(), "vk.json")
			if err := os.WriteFile(path, encoded, 0600); err != nil {
				t.Fatal(err)
			}
			if _, err := loadVerifyingKey(path); err == nil {
				t.Fatalf("accepted missing or null %s", field)
			}
		}
	}
}
