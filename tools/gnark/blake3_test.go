package main

import (
	"io"
	"testing"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/test"
	"github.com/zeebo/blake3"
)

type blakeCircuit struct {
	Input  []uints.U8
	Output [96]uints.U8
}

func (c *blakeCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	result := blakeXOF(api, u, c.Input, len(c.Output))
	for i := range result {
		u.Bytes.AssertIsEqual(result[i], c.Output[i])
	}
	return nil
}

func TestBlake3Boundaries(t *testing.T) {
	for _, n := range []int{0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 3073} {
		input := make([]byte, n)
		for i := range input {
			input[i] = byte(i % 251)
		}
		h := blake3.New()
		h.Write(input)
		var expected [96]byte
		if _, err := io.ReadFull(h.Digest(), expected[:]); err != nil {
			t.Fatal(err)
		}
		circuit := &blakeCircuit{Input: make([]uints.U8, n)}
		assignment := &blakeCircuit{Input: uints.NewU8Array(input)}
		copy(assignment.Output[:], uints.NewU8Array(expected[:]))
		if err := test.IsSolved(circuit, assignment, curveID.ScalarField()); err != nil {
			t.Fatalf("length %d: %v", n, err)
		}
		assignment.Output[95] = uints.NewU8(expected[95] ^ 1)
		if err := test.IsSolved(circuit, assignment, curveID.ScalarField()); err == nil {
			t.Fatalf("length %d accepted changed XOF state", n)
		}
	}
}

func TestBlake3CompiledConstraints(t *testing.T) {
	input := []byte("ix BLAKE3 wrapper")
	h := blake3.New()
	h.Write(input)
	var expected [96]byte
	io.ReadFull(h.Digest(), expected[:])
	circuit := &blakeCircuit{Input: make([]uints.U8, len(input))}
	assignment := &blakeCircuit{Input: uints.NewU8Array(input)}
	copy(assignment.Output[:], uints.NewU8Array(expected[:]))
	ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, circuit)
	if err != nil {
		t.Fatal(err)
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err != nil {
		t.Fatal(err)
	}
	t.Logf("one-block BLAKE3 XOF: %d constraints", ccs.GetNbConstraints())
	assignment.Input[0] = uints.NewU8(input[0] ^ 1)
	w, err = frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccs.IsSolved(w); err == nil {
		t.Fatal("compiled circuit accepted changed input")
	}
}

type blakeConstPrefixCircuit struct {
	Prefix []byte `gnark:"-"`
	Suffix []uints.U8
	Output [64]uints.U8
}

func (c *blakeConstPrefixCircuit) Define(api frontend.API) error {
	u, err := uints.NewBinaryField[uints.U32](api)
	if err != nil {
		return err
	}
	input := append(uints.NewU8Array(c.Prefix), c.Suffix...)
	result := blakeXOF(api, u, input, len(c.Output))
	for i := range result {
		u.Bytes.AssertIsEqual(result[i], c.Output[i])
	}
	return nil
}

func TestBlake3ConstantPrefixFoldingMatchesNative(t *testing.T) {
	prefix := make([]byte, 1280) // > 1 full 1024-byte chunk + 4 blocks
	for i := range prefix {
		prefix[i] = byte((i*37 + 11) % 251)
	}
	suffix := []byte("variable tail bytes after constant prefix")
	full := append(append([]byte(nil), prefix...), suffix...)
	h := blake3.New()
	h.Write(full)
	var expected [64]byte
	if _, err := io.ReadFull(h.Digest(), expected[:]); err != nil {
		t.Fatal(err)
	}
	circuit := &blakeConstPrefixCircuit{Prefix: prefix, Suffix: make([]uints.U8, len(suffix))}
	assignment := &blakeConstPrefixCircuit{Suffix: uints.NewU8Array(suffix)}
	copy(assignment.Output[:], uints.NewU8Array(expected[:]))
	ccsFolded, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, circuit)
	if err != nil {
		t.Fatal(err)
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	if err := ccsFolded.IsSolved(w); err != nil {
		t.Fatal(err)
	}
	// Compare against all-variable input of the same length.
	allVar := &blakeCircuit{Input: make([]uints.U8, len(full))}
	ccsVar, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, allVar)
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("1321-byte BLAKE3 XOF: all-variable=%d folded-prefix=%d constraints",
		ccsVar.GetNbConstraints(), ccsFolded.GetNbConstraints())
	if ccsFolded.GetNbConstraints() >= ccsVar.GetNbConstraints()/2 {
		t.Fatalf("expected constant prefix folding to cut >50%% constraints: folded=%d var=%d",
			ccsFolded.GetNbConstraints(), ccsVar.GetNbConstraints())
	}
}
