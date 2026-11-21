package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
)

const (
	goldenEmptyProgramDigest = "0x02d95030e924d62b65dcb11734967f540cddd90337d58184d90f02197df5a799"
	goldenProgramDigest      = "0x3841d46e6b5730d0f1d9faba16072a2c3caed66c64f8e32ee5ebdb69a57a2b28"
	fixtureVKProgramDigest   = "0x764a1979c109cbc92bff867f7f929950438365adfe3c502a82700ed4d6f7a7b0"
)

func goldenScalarProgram() scalarProgram {
	return scalarProgram{
		Nodes: []instruction{
			{Op: "constant", Value: "0x0000000000000000000000000000000000000000000000000000000000000000"},
			{Op: "constant", Value: "0x000000000000000000000000000000000000000000000000000000000000005e"},
			{Op: "constant", Value: "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000"},
			{Op: "input", Kind: "challenge", Index: 5},
			{Op: "input", Kind: "value", Index: 258},
			{Op: "input", Kind: "public", Index: 22},
			{Op: "add", A: 1, B: 3},
			{Op: "sub", A: 6, B: 4},
			{Op: "mul", A: 7, B: 2},
			{Op: "inverse", A: 8},
		},
		Assertions:   []int{9, 0},
		Coefficients: []int{6, 7, 8},
		Witnesses:    []int{5},
	}
}

func TestScalarProgramDigestEmpty(t *testing.T) {
	empty := scalarProgram{}
	encoded, err := empty.encode()
	if err != nil {
		t.Fatal(err)
	}
	wantEncoded := append([]byte(outerIRDomain), make([]byte, 16)...)
	if !bytes.Equal(encoded, wantEncoded) {
		t.Fatalf("empty encoding mismatch: got %x, want %x", encoded, wantEncoded)
	}
	got, err := empty.digest()
	if err != nil {
		t.Fatal(err)
	}
	if gotHex := "0x" + hex.EncodeToString(got[:]); gotHex != goldenEmptyProgramDigest {
		t.Fatalf("empty digest mismatch: got %s, want %s", gotHex, goldenEmptyProgramDigest)
	}
}

func TestScalarProgramDigestGoldenVector(t *testing.T) {
	golden := goldenScalarProgram()
	encoded, err := golden.encode()
	if err != nil {
		t.Fatal(err)
	}
	if len(encoded) != 203 {
		t.Fatalf("unexpected encoded length: got %d, want 203", len(encoded))
	}
	if !bytes.Equal(encoded[:14], []byte(outerIRDomain)) {
		t.Fatalf("unexpected domain prefix: %q", encoded[:14])
	}
	got, err := golden.digest()
	if err != nil {
		t.Fatal(err)
	}
	if gotHex := "0x" + hex.EncodeToString(got[:]); gotHex != goldenProgramDigest {
		t.Fatalf("golden digest mismatch: got %s, want %s", gotHex, goldenProgramDigest)
	}

	// Non-padded and decimal representations of canonical constants must hash identically.
	alt := goldenScalarProgram()
	alt.Nodes[0].Value = "0"
	alt.Nodes[1].Value = "94"
	altGot, err := alt.digest()
	if err != nil {
		t.Fatal(err)
	}
	if altGot != got {
		t.Fatalf("canonical scalar formatting changed digest: got 0x%x, want 0x%x", altGot, got)
	}
}

func TestScalarProgramDigestRejectsMalformed(t *testing.T) {
	cases := []struct {
		name string
		prog scalarProgram
	}{
		{"unknown op", scalarProgram{Nodes: []instruction{{Op: "pow"}}}},
		{"unknown input kind", scalarProgram{Nodes: []instruction{{Op: "input", Kind: "secret", Index: 0}}}},
		{"noncanonical constant equal modulus", scalarProgram{Nodes: []instruction{{Op: "constant", Value: scalarModulus().String()}}}},
		{"negative constant", scalarProgram{Nodes: []instruction{{Op: "constant", Value: "-1"}}}},
		{"negative input index", scalarProgram{Nodes: []instruction{{Op: "input", Kind: "challenge", Index: -1}}}},
		{"negative binary operand", scalarProgram{Nodes: []instruction{{Op: "add", A: -1, B: 0}}}},
		{"negative output id", scalarProgram{Assertions: []int{-1}}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if _, err := tc.prog.digest(); err == nil {
				t.Fatalf("expected error for %s", tc.name)
			}
		})
	}
}

func TestFixtureVKProgramDigest(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	vk, err := decodeVerifyingKey(data)
	if err != nil {
		t.Fatal(err)
	}
	if vk.ProgramDigest != fixtureVKProgramDigest {
		t.Fatalf("fixture programDigest mismatch: got %s, want %s", vk.ProgramDigest, fixtureVKProgramDigest)
	}
	got, err := vk.Program.digest()
	if err != nil {
		t.Fatal(err)
	}
	if gotHex := "0x" + hex.EncodeToString(got[:]); gotHex != fixtureVKProgramDigest {
		t.Fatalf("computed fixture digest mismatch: got %s, want %s", gotHex, fixtureVKProgramDigest)
	}
}

func TestVerifyingKeyRejectsTamperedProgram(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	base, err := decodeVerifyingKey(data)
	if err != nil {
		t.Fatal(err)
	}

	constIdx := -1
	addIdx := -1
	for i, n := range base.Program.Nodes {
		if constIdx < 0 && n.Op == "constant" {
			constIdx = i
		}
		if addIdx < 0 && n.Op == "add" && n.A != n.B {
			addIdx = i
		}
	}
	if constIdx < 0 || addIdx < 0 {
		t.Fatal("fixture program missing expected constant or add node")
	}

	cases := []struct {
		name   string
		mutate func(*verifyingKey)
	}{
		{
			name: "tampered constant value",
			mutate: func(vk *verifyingKey) {
				vk.Program.Nodes[constIdx].Value = "0x000000000000000000000000000000000000000000000000000000000000002a"
			},
		},
		{
			name: "tampered op kind",
			mutate: func(vk *verifyingKey) {
				vk.Program.Nodes[addIdx].Op = "mul"
			},
		},
		{
			name: "swapped operands",
			mutate: func(vk *verifyingKey) {
				vk.Program.Nodes[addIdx].A, vk.Program.Nodes[addIdx].B = vk.Program.Nodes[addIdx].B, vk.Program.Nodes[addIdx].A
			},
		},
		{
			name: "appended dead node",
			mutate: func(vk *verifyingKey) {
				vk.Program.Nodes = append(vk.Program.Nodes, instruction{
					Op:    "constant",
					Value: "0x0000000000000000000000000000000000000000000000000000000000000000",
				})
			},
		},
		{
			name: "tampered assertion output",
			mutate: func(vk *verifyingKey) {
				vk.Program.Assertions[0] = (vk.Program.Assertions[0] + 1) % len(vk.Program.Nodes)
			},
		},
		{
			name: "tampered coefficient output",
			mutate: func(vk *verifyingKey) {
				vk.Program.Coefficients[0] = (vk.Program.Coefficients[0] + 1) % len(vk.Program.Nodes)
			},
		},
		{
			name: "tampered witness output",
			mutate: func(vk *verifyingKey) {
				vk.Program.Witnesses[0] = (vk.Program.Witnesses[0] + 1) % len(vk.Program.Nodes)
			},
		},
		{
			name: "wrong programDigest",
			mutate: func(vk *verifyingKey) {
				b, err := unhex(vk.ProgramDigest, 32)
				if err != nil {
					t.Fatal(err)
				}
				b[0] ^= 0x01
				vk.ProgramDigest = "0x" + hex.EncodeToString(b)
			},
		},
		{
			name: "empty programDigest",
			mutate: func(vk *verifyingKey) {
				vk.ProgramDigest = ""
			},
		},
		{
			name: "truncated programDigest",
			mutate: func(vk *verifyingKey) {
				vk.ProgramDigest = "0x1234"
			},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			var vk verifyingKey
			if err := json.Unmarshal(data, &vk); err != nil {
				t.Fatal(err)
			}
			tc.mutate(&vk)
			if err := vk.validate(); err == nil {
				t.Fatalf("validate() accepted %s", tc.name)
			}
			encoded, err := json.Marshal(&vk)
			if err != nil {
				t.Fatal(err)
			}
			if _, err := decodeVerifyingKey(encoded); err == nil {
				t.Fatalf("decodeVerifyingKey() accepted %s", tc.name)
			}
		})
	}
}
