package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
)

func TestAuthenticatedPrefixExtension(t *testing.T) {
	directory := t.TempDir()
	full, err := kzg.NewSRS(8, big.NewInt(7))
	if err != nil {
		t.Fatal(err)
	}
	source := filepath.Join(directory, "source.bin")
	prefix := &kzg.SRS{Pk: kzg.ProvingKey{G1: full.Pk.G1[:4]}, Vk: full.Vk}
	if err := writeSRS(source, prefix); err != nil {
		t.Fatal(err)
	}
	original, err := os.ReadFile(source)
	if err != nil {
		t.Fatal(err)
	}
	digest := sha256.Sum256(original)
	trusted := hex.EncodeToString(digest[:])
	var candidate []byte
	for _, point := range full.Pk.G1[4:7] {
		raw := point.RawBytes()
		candidate = append(candidate, raw[:]...)
	}
	path := filepath.Join(directory, "additional.bin")
	if err := os.WriteFile(path, candidate, 0600); err != nil {
		t.Fatal(err)
	}
	output := filepath.Join(directory, "extended.bin")
	if err := extendSRS(source, trusted, path, output, 7); err != nil {
		t.Fatal(err)
	}
	gold := filepath.Join(directory, "expected.bin")
	if err := writeSRS(gold, &kzg.SRS{Pk: kzg.ProvingKey{G1: full.Pk.G1[:7]}, Vk: full.Vk}); err != nil {
		t.Fatal(err)
	}
	got, _ := os.ReadFile(output)
	want, _ := os.ReadFile(gold)
	if !bytes.Equal(got, want) {
		t.Fatal("extended SRS differs from the same known powers and verifier key")
	}
	if err := extendSRS(source, trusted, path, output, 7); err == nil {
		t.Fatal("overwrote an existing output")
	}
	cases := map[string][]byte{
		"wrong-point": append([]byte(nil), candidate...),
		"zero-point":  append([]byte(nil), candidate...),
		"swapped":     append([]byte(nil), candidate...),
		"trailing":    append(append([]byte(nil), candidate...), 0),
	}
	wrong := full.Pk.G1[0].RawBytes()
	copy(cases["wrong-point"][:64], wrong[:])
	zeroPoint := bn254.G1Affine{}
	zero := zeroPoint.RawBytes()
	copy(cases["zero-point"][:64], zero[:])
	copy(cases["swapped"][:64], candidate[64:128])
	copy(cases["swapped"][64:128], candidate[:64])
	for name, data := range cases {
		t.Run(name, func(t *testing.T) {
			bad := filepath.Join(directory, name+".bin")
			if err := os.WriteFile(bad, data, 0600); err != nil {
				t.Fatal(err)
			}
			result := filepath.Join(directory, name+"-output.bin")
			if err := extendSRS(source, trusted, bad, result, 7); err == nil {
				t.Fatal("accepted invalid candidate powers")
			}
			if _, err := os.Stat(result); !os.IsNotExist(err) {
				t.Fatal("published a rejected extension")
			}
		})
	}
	wrongDigest := sha256.Sum256([]byte("another prefix"))
	if err := extendSRS(source, hex.EncodeToString(wrongDigest[:]), path, filepath.Join(directory, "wrong-pin.bin"), 7); err == nil {
		t.Fatal("accepted an unauthenticated prefix")
	}
	after, _ := os.ReadFile(source)
	if !bytes.Equal(original, after) {
		t.Fatal("modified the original prefix")
	}
}
