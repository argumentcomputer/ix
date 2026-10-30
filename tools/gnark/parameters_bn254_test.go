//go:build plonk || !groth16

package main

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
)

func TestLagrangeCacheAndBasisConversion(t *testing.T) {
	srs, err := readSRS(filepath.Join("testdata", "bn254", "srs.bin"), fixtureSRSBLAKE3, 128)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "points.bin")
	first, err := loadLagrange(srs, 8, path, "")
	if err != nil {
		t.Fatal(err)
	}
	identity, err := fileHash(path)
	if err != nil {
		t.Fatal(err)
	}
	second, err := loadLagrange(srs, 8, path, identity.SHA256)
	if err != nil {
		t.Fatal(err)
	}
	for i := range first.Pk.G1 {
		if !first.Pk.G1[i].Equal(&second.Pk.G1[i]) {
			t.Fatal("cache changed Lagrange points")
		}
	}
	coefficients := make([]fr.Element, 8)
	for i := 0; i < 3; i++ {
		coefficients[i].SetUint64(uint64(2*i + 1))
	}
	evaluations := append([]fr.Element(nil), coefficients...)
	fft.NewDomain(8).FFT(evaluations, fft.DIF)
	fft.BitReverse(evaluations)
	a, err := kzg.Commit(coefficients, srs.Pk)
	if err != nil {
		t.Fatal(err)
	}
	b, err := kzg.Commit(evaluations, second.Pk)
	if err != nil {
		t.Fatal(err)
	}
	if !a.Equal(&b) {
		t.Fatal("monomial and Lagrange commitments differ")
	}
	f, err := os.OpenFile(path, os.O_RDWR, 0)
	if err != nil {
		t.Fatal(err)
	}
	var changed [1]byte
	if _, err := f.ReadAt(changed[:], 30); err != nil {
		t.Fatal(err)
	}
	changed[0] ^= 1
	if _, err := f.WriteAt(changed[:], 30); err != nil {
		t.Fatal(err)
	}
	if err := f.Close(); err != nil {
		t.Fatal(err)
	}
	if _, err := loadLagrange(srs, 8, path, identity.SHA256); err == nil {
		t.Fatal("accepted corrupted Lagrange cache")
	}
	if _, err := loadLagrange(srs, 16, path, identity.SHA256); err == nil {
		t.Fatal("accepted wrong Lagrange domain")
	}
}
