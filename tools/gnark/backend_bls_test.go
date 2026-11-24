//go:build plonk || !groth16

package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	blsfr "github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr/fft"
	kzgbls "github.com/consensys/gnark-crypto/ecc/bls12-381/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbls "github.com/consensys/gnark/backend/plonk/bls12-381"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/zeebo/blake3"
)

// fixtureBLSSRSBLAKE3 pins testdata/bls12-381/srs.bin (Filecoin challenge_19 128-power prefix).
const fixtureBLSSRSBLAKE3 = "187d35e08e47a1a33117a26a1bde25b0b9dfc2c0651c617d5226ec5096acc6fd"

func TestBLS12381FilecoinBackendAndProofCodec(t *testing.T) {
	srsPath := filepath.Join("testdata", "bls12-381", "srs.bin")
	srs, err := readSRSBLS(srsPath, fixtureBLSSRSBLAKE3, 128)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := readSRSBLS(srsPath, fixtureBLSSRSBLAKE3, 64); err == nil {
		t.Fatal("accepted wrong power count")
	}
	if _, err := readSRSBLS(srsPath, string(bytes.Repeat([]byte{'0'}, 64)), 128); err == nil {
		t.Fatal("accepted wrong export receipt")
	}
	for _, commit := range []bool{false, true} {
		ccs, err := frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &backendCircuit{Commit: commit})
		if err != nil {
			t.Fatal(err)
		}
		n := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + 2))
		if n > 128 {
			t.Fatalf("tiny circuit exceeded Filecoin fixture SRS: %d", n)
		}
		lagrange, err := kzgbls.ToLagrangeG1(srs.Pk.G1[:n])
		if err != nil {
			t.Fatal(err)
		}
		pk, vk, err := plonk.Setup(ccs, srs, &kzgbls.SRS{Pk: kzgbls.ProvingKey{G1: lagrange}, Vk: srs.Vk})
		if err != nil {
			t.Fatal(err)
		}
		w, err := frontend.NewWitness(&backendCircuit{Claim: [2]frontend.Variable{49, 1}, X: 7}, ecc.BLS12_381.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
		if err != nil {
			t.Fatal(err)
		}
		public, _ := w.Public()
		if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
			t.Fatal(err)
		}
		var encoded bytes.Buffer
		if _, err := proof.WriteTo(&encoded); err != nil {
			t.Fatal(err)
		}
		nativeVK := vk.(*plonkbls.VerifyingKey)
		m := len(nativeVK.Qcp)
		decoded, err := decodeProofBLS(encoded.Bytes(), m)
		if err != nil {
			t.Fatal(err)
		}
		if err := plonk.Verify(decoded, vk, public); err != nil {
			t.Fatal(err)
		}
		for _, offset := range []int{0, 384, 660 + 32*m} {
			bad := append([]byte(nil), encoded.Bytes()...)
			bad[offset] = 0xff
			if _, err := decodeProofBLS(bad, m); err == nil {
				t.Fatalf("accepted malformed BLS12-381 proof at %d", offset)
			}
		}
		if _, err := decodeProofBLS(append(encoded.Bytes(), 0), m); err == nil {
			t.Fatal("accepted trailing BLS12-381 proof bytes")
		}
		if commit {
			dir := os.Getenv("IX_BLS_PLONK_TEST_OUTPUT")
			if dir == "" {
				dir = t.TempDir()
			}
			keyPath := filepath.Join(dir, "verifying-key.bin")
			if err := atomicFile(keyPath, func(w io.Writer) error { _, err := vk.WriteTo(w); return err }); err != nil {
				t.Fatal(err)
			}
			keyHash, err := fileHash(keyPath)
			if err != nil {
				t.Fatal(err)
			}
			keyBytes, err := os.ReadFile(keyPath)
			if err != nil {
				t.Fatal(err)
			}
			trusted, err := hex.DecodeString(keyHash.SHA256)
			if err != nil {
				t.Fatal(err)
			}
			var digest [32]byte
			digest[0], digest[16] = 49, 1
			anchors := encodeAnchorsBLS(nativeVK)
			if err := verifyProofBLS(keyBytes, trusted, encoded.Bytes(), digest[:], anchors); err != nil {
				t.Fatal(err)
			}
			wrongDigest := digest
			wrongDigest[31] = 1
			if err := verifyProofBLS(keyBytes, trusted, encoded.Bytes(), wrongDigest[:], anchors); err == nil {
				t.Fatal("accepted changed BLS12-381 public digest")
			}
			wrongAnchors := append([]byte(nil), anchors...)
			wrongAnchors[0] ^= 1
			if err := verifyProofBLS(keyBytes, trusted, encoded.Bytes(), digest[:], wrongAnchors); err == nil {
				t.Fatal("accepted changed BLS12-381 setup anchors")
			}
			if err := atomicFile(filepath.Join(dir, "Bls12381PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) }); err != nil {
				t.Fatal(err)
			}
			payload := proof.(*plonkbls.Proof).MarshalSolidity()
			if len(payload) != 1056+128*m {
				t.Fatalf("unexpected BLS12-381 Solidity proof length: got %d, want %d", len(payload), 1056+128*m)
			}
			vector := map[string]any{
				"scope":              "filecoin-bls12-381-backend-fixture-not-an-ix-wrapper",
				"curve":              "bls12-381",
				"verifyingKeySHA256": keyHash.SHA256,
				"proof":              "0x" + hex.EncodeToString(payload),
				"claimDigest":        "0x" + hex.EncodeToString(digest[:]),
				"commitments":        m,
				"domain":             n,
			}
			data, _ := json.MarshalIndent(vector, "", "  ")
			if err := atomicFile(filepath.Join(dir, "proof.json"), func(w io.Writer) error { _, err := w.Write(data); return err }); err != nil {
				t.Fatal(err)
			}
		}
		t.Logf("Filecoin BLS12-381 PLONK backend: N=%d commitments=%d native_bytes=%d solidity_bytes=%d", n, m, encoded.Len(), len(proof.(*plonkbls.Proof).MarshalSolidity()))
	}
}

func TestBLS12381LagrangeCacheAndBasisConversion(t *testing.T) {
	srs, err := readSRSBLS(filepath.Join("testdata", "bls12-381", "srs.bin"), fixtureBLSSRSBLAKE3, 128)
	if err != nil {
		t.Fatal(err)
	}
	path := filepath.Join(t.TempDir(), "points.bin")
	first, err := loadLagrangeBLS(srs, 8, path, "")
	if err != nil {
		t.Fatal(err)
	}
	identity, err := fileHash(path)
	if err != nil {
		t.Fatal(err)
	}
	second, err := loadLagrangeBLS(srs, 8, path, identity.SHA256)
	if err != nil {
		t.Fatal(err)
	}
	for i := range first.Pk.G1 {
		if !first.Pk.G1[i].Equal(&second.Pk.G1[i]) {
			t.Fatal("cache changed BLS12-381 Lagrange points")
		}
	}
	coefficients := make([]blsfr.Element, 8)
	for i := 0; i < 3; i++ {
		coefficients[i].SetUint64(uint64(2*i + 1))
	}
	evaluations := append([]blsfr.Element(nil), coefficients...)
	fft.NewDomain(8).FFT(evaluations, fft.DIF)
	fft.BitReverse(evaluations)
	a, err := kzgbls.Commit(coefficients, srs.Pk)
	if err != nil {
		t.Fatal(err)
	}
	b, err := kzgbls.Commit(evaluations, second.Pk)
	if err != nil {
		t.Fatal(err)
	}
	if !a.Equal(&b) {
		t.Fatal("BLS12-381 monomial and Lagrange commitments differ")
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
	if _, err := loadLagrangeBLS(srs, 8, path, identity.SHA256); err == nil {
		t.Fatal("accepted corrupted BLS12-381 Lagrange cache")
	}
	if _, err := loadLagrangeBLS(srs, 16, path, identity.SHA256); err == nil {
		t.Fatal("accepted wrong BLS12-381 Lagrange domain")
	}
}

func TestBLS12381IndependentSRSExportAndRead(t *testing.T) {
	domain := uint64(16)
	development, err := kzgbls.NewSRS(domain+3, big.NewInt(42))
	if err != nil {
		t.Fatal(err)
	}
	var source bytes.Buffer
	var header [88]byte
	copy(header[:8], blsSRSMagic)
	identity := blake3.Sum256([]byte("independent-bls-final-test-parameters"))
	copy(header[8:40], identity[:])
	binary.LittleEndian.PutUint64(header[40:48], domain+2)
	copy(header[48:80], identity[:])
	binary.LittleEndian.PutUint64(header[80:88], domain+3)
	source.Write(header[:])
	for _, point := range development.Vk.G2 {
		encoded := point.Bytes()
		source.Write(encoded[:])
	}
	if err := writeAffinePointsBLS(&source, development.Pk.G1); err != nil {
		t.Fatal(err)
	}
	receipt := blake3.Sum256(source.Bytes())
	srsPath := filepath.Join(t.TempDir(), "srs.bin")
	if err := os.WriteFile(srsPath, source.Bytes(), 0600); err != nil {
		t.Fatal(err)
	}
	loaded, err := readSRSBLS(srsPath, hex.EncodeToString(receipt[:]), domain)
	if err != nil {
		t.Fatal(err)
	}
	if !loaded.Vk.G1.Equal(&development.Vk.G1) || !loaded.Vk.G2[1].Equal(&development.Vk.G2[1]) {
		t.Fatal("loaded BLS12-381 SRS anchors differ")
	}
}
