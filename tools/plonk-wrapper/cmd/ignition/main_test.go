package main

import (
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
)

func TestNativeSRSRoundTrip(t *testing.T) {
	srs, err := kzg.NewSRS(8, big.NewInt(7))
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "srs.bin")
	if err := writeSRS(path, srs); err != nil {
		t.Fatal(err)
	}
	file, err := os.Open(path)
	if err != nil {
		t.Fatal(err)
	}
	defer file.Close()
	var restored kzg.SRS
	if _, err := restored.ReadFrom(file); err != nil {
		t.Fatal(err)
	}
	if len(restored.Pk.G1) != len(srs.Pk.G1) || !restored.Vk.G2[1].Equal(&srs.Vk.G2[1]) {
		t.Fatal("SRS round trip differs")
	}
	for i := range srs.Pk.G1 {
		if !restored.Pk.G1[i].Equal(&srs.Pk.G1[i]) {
			t.Fatalf("power %d differs", i)
		}
	}
	if err := writeSRS(path, srs); err == nil {
		t.Fatal("replaced an existing release")
	}
}
