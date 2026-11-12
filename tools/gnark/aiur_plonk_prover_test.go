//go:build plonk || !groth16

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark/frontend"
)

func aiurBinaryFixture(t *testing.T) (*aiurSchema, []byte) {
	t.Helper()
	schema, values, _ := aiurFixture(t)
	w, err := frontend.NewWitness(aiurAssignment(t, schema, values), curveID.ScalarField())
	if err != nil {
		t.Fatal(err)
	}
	data, err := w.MarshalBinary()
	if err != nil {
		t.Fatal(err)
	}
	return schema, data
}

func TestAiurBinaryWitnessStrictDecoding(t *testing.T) {
	schema, data := aiurBinaryFixture(t)
	directory := os.Getenv("IX_AIUR_PLONK_FIXTURE")
	if directory == "" {
		directory = filepath.Join("testdata", "aiur")
	}
	exported, err := os.ReadFile(filepath.Join(directory, "witness.bin"))
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(data, exported) {
		t.Fatal("Rust and gnark binary witnesses differ")
	}
	secret, err := aiurDimensions(schema)
	if err != nil {
		t.Fatal(err)
	}
	decoded, err := decodeAiurWitness(data, schema.PublicInputs, secret)
	if err != nil {
		t.Fatal(err)
	}
	roundtrip, err := decoded.MarshalBinary()
	if err != nil || !bytes.Equal(roundtrip, data) {
		t.Fatal("binary witness round trip differs", err)
	}
	for _, index := range []int{0, 4, 8, 12} {
		bad := append([]byte(nil), data...)
		if index == 12 {
			for i := 12; i < 44; i++ {
				bad[i] = 0xff
			}
		} else {
			binary.BigEndian.PutUint32(bad[index:index+4], ^uint32(0))
		}
		if _, err := decodeAiurWitness(bad, schema.PublicInputs, secret); err == nil {
			t.Fatalf("accepted altered field/count at %d", index)
		}
	}
	for _, bad := range [][]byte{data[:len(data)-1], append(append([]byte(nil), data...), 0)} {
		if _, err := decodeAiurWitness(bad, schema.PublicInputs, secret); err == nil {
			t.Fatal("accepted wrong witness length")
		}
	}
	// A fixed-capacity trace can exceed the diagnostic JSON bridge's 16 MiB.
	const largeSecret = 1 << 19
	large := make([]byte, 12+32*(largeSecret+1))
	binary.BigEndian.PutUint32(large[:4], 1)
	binary.BigEndian.PutUint32(large[4:8], largeSecret)
	binary.BigEndian.PutUint32(large[8:12], largeSecret+1)
	if _, err := decodeAiurWitness(large, 1, largeSecret); err != nil {
		t.Fatal(err)
	}
}

func TestAiurRetainedIgnitionProver(t *testing.T) {
	path, pin := os.Getenv("IX_AIUR_PLONK_SRS"), os.Getenv("IX_AIUR_PLONK_SRS_BLAKE3")
	if path == "" || pin == "" {
		t.Skip("requires independently authenticated Ignition export and receipt")
	}
	schema, data := aiurBinaryFixture(t)
	encoded, err := json.Marshal(schema)
	if err != nil {
		t.Fatal(err)
	}
	directory := t.TempDir()
	circuit := filepath.Join(directory, "compiled.bin")
	info, err := compileAiur(encoded, circuit)
	if err != nil {
		t.Fatal(err)
	}
	digest, err := fileHash(circuit)
	if err != nil {
		t.Fatal(err)
	}
	request := aiurPreparation{Schema: encoded, Circuit: circuit, CircuitHash: digest, Info: info, SRS: path, SRSBLAKE3: pin, Lagrange: filepath.Join(directory, "lagrange.bin"), Output: filepath.Join(directory, "prepared")}
	metadata, err := prepareAiur(&request)
	if err != nil {
		t.Fatal(err)
	}
	manifest, err := json.Marshal(metadata)
	if err != nil {
		t.Fatal(err)
	}
	p, err := openAiurProver(request.Output, manifest, backendConfig{})
	if err != nil {
		t.Fatal(err)
	}
	defer p.close()
	expected := append([]byte(nil), data[12:12+32*schema.PublicInputs]...)
	wrong := append([]byte(nil), expected...)
	wrong[31] ^= 1
	if _, _, err := p.prove(data, wrong); err == nil {
		t.Fatal("accepted a different independently expected public call")
	}
	proof, solidity, err := p.prove(data, expected)
	if err != nil {
		t.Fatal(err)
	}
	if len(solidity) != 864 {
		t.Fatalf("unexpected Solidity size %d", len(solidity))
	}
	key, err := os.ReadFile(filepath.Join(request.Output, "verifying-key.bin"))
	if err != nil {
		t.Fatal(err)
	}
	keyPin := sha256.Sum256(key)
	anchors := encodeAnchors(p.vk)
	if err := verifyAiurProof(key, keyPin[:], proof, expected, anchors); err != nil {
		t.Fatal(err)
	}
	if err := verifyAiurProof(key, keyPin[:], proof, wrong, anchors); err == nil {
		t.Fatal("accepted changed public call")
	}
	badAnchors := append([]byte(nil), anchors...)
	badAnchors[0] ^= 1
	if err := verifyAiurProof(key, keyPin[:], proof, expected, badAnchors); err == nil {
		t.Fatal("accepted changed setup anchors")
	}
	badPin := keyPin
	badPin[0] ^= 1
	if err := verifyAiurProof(key, badPin[:], proof, expected, anchors); err == nil {
		t.Fatal("accepted changed key pin")
	}
	for _, bad := range [][]byte{proof[:len(proof)-1], append(append([]byte(nil), proof...), 0)} {
		if err := verifyAiurProof(key, keyPin[:], bad, expected, anchors); err == nil {
			t.Fatal("accepted malformed proof")
		}
	}
	if _, _, err := p.prove(data, expected); err != nil {
		t.Fatal("retained key could not prove again", err)
	}
	if err := p.close(); err != nil {
		t.Fatal(err)
	}
	if _, _, err := p.prove(data, expected); err == nil {
		t.Fatal("used closed prover")
	}
	original := metadata.Files["circuit.bin"]
	changed := original
	changed.SHA256 = metadata.Files["verifying-key.bin"].SHA256
	metadata.Files["circuit.bin"] = changed
	altered, _ := json.Marshal(metadata)
	if _, err := openAiurProver(request.Output, altered, backendConfig{}); err == nil {
		t.Fatal("opened circuit with wrong trusted digest")
	}
	metadata.Files["circuit.bin"] = original
	// An unsatisfied private assignment must fail in the PLONK solver.
	p, err = openAiurProver(request.Output, manifest, backendConfig{})
	if err != nil {
		t.Fatal(err)
	}
	defer p.close()
	bad := append([]byte(nil), data...)
	bad[len(bad)-1] ^= 1
	if _, _, err := p.prove(bad, expected); err == nil {
		t.Fatal("proved an altered private witness")
	}
	if _, _, err := p.prove(data, expected); err == nil {
		t.Fatal("reused failed prover")
	}
}
