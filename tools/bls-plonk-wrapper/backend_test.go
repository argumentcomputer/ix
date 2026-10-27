//go:build bls12381

package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bls12-381/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbls "github.com/consensys/gnark/backend/plonk/bls12-381"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

type backendCircuit struct {
	Claim  [2]frontend.Variable `gnark:",public"`
	X      frontend.Variable
	Commit bool `gnark:"-"`
}

func (c *backendCircuit) Define(api frontend.API) error {
	api.AssertIsEqual(api.Mul(c.X, c.X), c.Claim[0])
	api.AssertIsEqual(c.Claim[1], 1)
	if c.Commit {
		challenge, err := api.(frontend.Committer).Commit(c.X)
		if err != nil {
			return err
		}
		api.AssertIsDifferent(challenge, 0)
	}
	return nil
}

func TestFilecoinBackendAndProofCodec(t *testing.T) {
	p, err := loadVerifyingKey(filepath.Join("testdata", "outer", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	var receipt struct {
		Format, Blake3, SetupID, FilecoinManifest string
		PublicMaxDegree, Powers                   uint64
	}
	if err := decodeJSON(filepath.Join("testdata", "srs.json"), &receipt); err != nil {
		t.Fatal(err)
	}
	srsPath := filepath.Join("testdata", "srs.bin")
	srs, err := readSRS(srsPath, receipt.Blake3, 128, p)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := readSRS(srsPath, receipt.Blake3, 64, p); err == nil {
		t.Fatal("accepted wrong power count")
	}
	if _, err := readSRS(srsPath, string(bytes.Repeat([]byte{'0'}, 64)), 128, p); err == nil {
		t.Fatal("accepted wrong export receipt")
	}
	for _, commit := range []bool{false, true} {
		ccs, err := frontend.Compile(ecc.BLS12_381.ScalarField(), scs.NewBuilder, &backendCircuit{Commit: commit})
		if err != nil {
			t.Fatal(err)
		}
		n := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + 2))
		if n > 128 {
			t.Fatalf("tiny circuit exceeded fixture SRS: %d", n)
		}
		lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:n])
		if err != nil {
			t.Fatal(err)
		}
		pk, vk, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: lagrange}, Vk: srs.Vk})
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
		proof.WriteTo(&encoded)
		m := len(vk.(*plonkbls.VerifyingKey).Qcp)
		decoded, err := decodeProof(encoded.Bytes(), m)
		if err != nil {
			t.Fatal(err)
		}
		if err := plonk.Verify(decoded, vk, public); err != nil {
			t.Fatal(err)
		}
		for _, offset := range []int{0, 384, 660 + 32*m} {
			bad := append([]byte(nil), encoded.Bytes()...)
			bad[offset] = 0xff
			if _, err := decodeProof(bad, m); err == nil {
				t.Fatalf("accepted malformed proof at %d", offset)
			}
		}
		if _, err := decodeProof(append(encoded.Bytes(), 0), m); err == nil {
			t.Fatal("accepted trailing proof bytes")
		}
		if commit {
			dir := os.Getenv("IX_PLONK_TEST_OUTPUT")
			if dir == "" {
				dir = t.TempDir()
			}
			keyPath := filepath.Join(dir, "verifying-key.bin")
			if err := atomicFile(keyPath, func(w io.Writer) error { _, err := vk.WriteTo(w); return err }); err != nil {
				t.Fatal(err)
			}
			keyHash, _ := fileHash(keyPath)
			proofPath := filepath.Join(dir, "proof.bin")
			if err := atomicFile(proofPath, func(w io.Writer) error { _, err := w.Write(encoded.Bytes()); return err }); err != nil {
				t.Fatal(err)
			}
			var digest [32]byte
			digest[0], digest[16] = 49, 1
			if err := verify(keyPath, keyHash.SHA256, proofPath, hex.EncodeToString(digest[:])); err != nil {
				t.Fatal(err)
			}
			digest[31] = 1
			if err := verify(keyPath, keyHash.SHA256, proofPath, hex.EncodeToString(digest[:])); err == nil {
				t.Fatal("accepted changed public digest")
			}
			digest[31] = 0
			if err := atomicFile(filepath.Join(dir, "PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) }); err != nil {
				t.Fatal(err)
			}
			payload := proof.(*plonkbls.Proof).MarshalSolidity()
			if len(payload) != 1056+128*m {
				t.Fatal("unexpected Solidity proof length")
			}
			vector := map[string]any{"scope": "tiny-backend-test-not-an-ix-wrapper", "proof": "0x" + hex.EncodeToString(payload), "digest": "0x" + hex.EncodeToString(digest[:]), "commitments": m, "domain": n}
			data, _ := json.MarshalIndent(vector, "", "  ")
			if err := atomicFile(filepath.Join(dir, "proof.json"), func(w io.Writer) error { _, err := w.Write(data); return err }); err != nil {
				t.Fatal(err)
			}
		}
		t.Logf("Filecoin PLONK backend: N=%d commitments=%d native_bytes=%d solidity_bytes=%d", n, m, encoded.Len(), len(proof.(*plonkbls.Proof).MarshalSolidity()))
	}
}
