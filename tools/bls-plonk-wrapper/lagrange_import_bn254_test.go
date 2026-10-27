//go:build !bls12381

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"os"
	"path/filepath"
	"testing"

	bn "github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend/plonk"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

func importedFixture(t *testing.T) (*verifyingKey, *nativeSRS, string) {
	t.Helper()
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
	return p, srs, receipt.Blake3
}

func candidateDigest(points []nativeG1) [32]byte {
	var out bytes.Buffer
	if err := bn.NewEncoder(&out).Encode(points); err != nil {
		panic(err)
	}
	return sha256.Sum256(out.Bytes())
}

func TestImportedLagrangeBasisRejectsAlteredAndWrongDomainPoints(t *testing.T) {
	p, srs, receipt := importedFixture(t)
	points, err := toLagrange(srs.Pk.G1[:8])
	if err != nil {
		t.Fatal(err)
	}
	if _, err := validateLagrange(srs, points, p.SetupID, receipt, candidateDigest(points)); err != nil {
		t.Fatal(err)
	}
	for _, kind := range []string{"changed", "permuted", "truncated"} {
		bad := append([]nativeG1(nil), points...)
		switch kind {
		case "changed":
			bad[0].Add(&bad[0], &srs.Pk.G1[0])
		case "permuted":
			bad[0], bad[1] = bad[1], bad[0]
		case "truncated":
			bad = bad[:4]
		}
		if _, err := validateLagrange(srs, bad, p.SetupID, receipt, candidateDigest(bad)); err == nil {
			t.Fatalf("accepted %s basis", kind)
		}
	}
}

func TestLegacySP1ReaderBoundsAndAnchors(t *testing.T) {
	_, srs, _ := importedFixture(t)
	ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, &backendCircuit{Commit: true})
	if err != nil {
		t.Fatal(err)
	}
	points, err := toLagrange(srs.Pk.G1[:8])
	if err != nil {
		t.Fatal(err)
	}
	pk, _, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: points}, Vk: srs.Vk})
	if err != nil {
		t.Fatal(err)
	}
	var encoded bytes.Buffer
	if _, err := pk.WriteTo(&encoded); err != nil {
		t.Fatal(err)
	}
	legacy := append([]byte(nil), encoded.Bytes()[16:]...)
	if binary.BigEndian.Uint64(legacy[:8]) != 8 {
		t.Fatal("unexpected key version framing")
	}
	path := filepath.Join(t.TempDir(), "key.bin")
	if err := os.WriteFile(path, legacy, 0600); err != nil {
		t.Fatal(err)
	}
	got, digest, err := readSP1Lagrange(path, 8, srs)
	if err != nil {
		t.Fatal(err)
	}
	if digest != candidateDigest(points) {
		t.Fatal("candidate digest differs")
	}
	for i := range points {
		if !got[i].Equal(&points[i]) {
			t.Fatal("extraction changed points")
		}
	}
	for _, kind := range []string{"count", "domain", "truncated", "trailing"} {
		bad := append([]byte(nil), legacy...)
		switch kind {
		case "count":
			binary.BigEndian.PutUint32(bad[112+8*32:], ^uint32(0))
		case "domain":
			binary.BigEndian.PutUint64(bad[:8], 16)
		case "truncated":
			bad = bad[:len(bad)-1]
		case "trailing":
			bad = append(bad, 0)
		}
		if err := os.WriteFile(path, bad, 0600); err != nil {
			t.Fatal(err)
		}
		if _, _, err := readSP1Lagrange(path, 8, srs); err == nil {
			t.Fatalf("accepted %s key", kind)
		}
	}
	if err := os.WriteFile(path, legacy, 0600); err != nil {
		t.Fatal(err)
	}
	other := *srs
	other.Vk.G1 = srs.Pk.G1[1]
	if _, _, err := readSP1Lagrange(path, 8, &other); err == nil {
		t.Fatal("accepted different setup anchor")
	}
}
