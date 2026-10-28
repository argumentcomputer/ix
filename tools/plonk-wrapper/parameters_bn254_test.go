package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/fft"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
)

func TestLagrangeCacheAndBasisConversion(t *testing.T) {
	p, err := loadVerifyingKey(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	var receipt struct {
		Format, Blake3, SetupID, IgnitionManifest string
		PublicMaxDegree, Powers                   uint64
	}
	if err := decodeJSON(filepath.Join("testdata", "bn254", "srs.json"), &receipt); err != nil {
		t.Fatal(err)
	}
	srs, err := readSRS(filepath.Join("testdata", "bn254", "srs.bin"), receipt.Blake3, 128, p)
	if err != nil {
		t.Fatal(err)
	}
	root := t.TempDir()
	executable := strings.Repeat("a", 64)
	first, reused, err := lagrangeParameters(root, srs, 8, p.SetupID, receipt.Blake3, executable)
	if err != nil || reused {
		t.Fatalf("initial derivation: reused=%t error=%v", reused, err)
	}
	second, reused, err := lagrangeParameters(root, srs, 8, p.SetupID, receipt.Blake3, executable)
	if err != nil || !reused {
		t.Fatalf("cached derivation: reused=%t error=%v", reused, err)
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
	files, err := filepath.Glob(filepath.Join(root, "8", "*", "points.bin"))
	if err != nil || len(files) != 1 {
		t.Fatalf("cache files: %v %v", files, err)
	}
	f, err := os.OpenFile(files[0], os.O_RDWR, 0)
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
	if _, _, err := lagrangeParameters(root, srs, 8, p.SetupID, receipt.Blake3, executable); err == nil {
		t.Fatal("accepted corrupted Lagrange cache")
	}
	if _, reused, err := lagrangeParameters(root, srs, 8, p.SetupID, receipt.Blake3, strings.Repeat("b", 64)); err != nil || reused {
		t.Fatalf("new backend reused old cache: %t %v", reused, err)
	}
}
