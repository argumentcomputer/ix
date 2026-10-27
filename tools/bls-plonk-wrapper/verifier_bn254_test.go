//go:build bn254

package main

import (
	"bytes"
	"math/big"
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
	p, err := loadProfile(filepath.Join("testdata", "bn254", "profile.json"))
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
	for _, kind := range []string{"claim", "evaluation", "commitment", "deferred-key", "outer-key"} {
		w := assignment()
		profileCopy := *p
		switch kind {
		case "claim":
			w.Claim[0] = new(big.Int).Add(w.Claim[0].(*big.Int), big.NewInt(1))
		case "evaluation":
			w.Values[1] = new(big.Int).Add(w.Values[1].(*big.Int), big.NewInt(1))
		case "commitment":
			_, _, g, _ := bn.Generators()
			w.Points[0] = newCircuitG1(g)
		case "deferred-key":
			profileCopy.DeferredKeys = []string{p.DeferredKeys[0], p.DeferredKeys[0]}
		case "outer-key":
			profileCopy.OuterKeys = []string{p.OuterKeys[0], p.OuterKeys[0]}
		}
		if err := test.IsSolved(newCircuit(&profileCopy), w, curveID.ScalarField()); err == nil {
			t.Fatalf("accepted %s mutation", kind)
		}
	}
}
