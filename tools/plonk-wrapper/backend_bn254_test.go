package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
	"github.com/zeebo/blake3"
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

func TestIgnitionBackendAndProofCodec(t *testing.T) {
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
	srsPath := filepath.Join("testdata", "bn254", "srs.bin")
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
		ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &backendCircuit{Commit: commit})
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
		w, err := frontend.NewWitness(&backendCircuit{Claim: [2]frontend.Variable{49, 1}, X: 7}, ecc.BN254.ScalarField())
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
		m := len(vk.(*plonkbn254.VerifyingKey).Qcp)
		decoded, err := decodeProof(encoded.Bytes(), m)
		if err != nil {
			t.Fatal(err)
		}
		if err := plonk.Verify(decoded, vk, public); err != nil {
			t.Fatal(err)
		}
		for _, offset := range []int{0, 256, 516 + 32*m} {
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
			if err := verifyFixture(keyPath, keyHash.SHA256, proofPath, digest[:]); err != nil {
				t.Fatal(err)
			}
			digest[31] = 1
			if err := verifyFixture(keyPath, keyHash.SHA256, proofPath, digest[:]); err == nil {
				t.Fatal("accepted changed public digest")
			}
			digest[31] = 0
			if err := atomicFile(filepath.Join(dir, "PlonkVerifier.sol"), func(w io.Writer) error { return vk.ExportSolidity(w) }); err != nil {
				t.Fatal(err)
			}
			payload := proof.(*plonkbn254.Proof).MarshalSolidity()
			if len(payload) != 768+96*m {
				t.Fatal("unexpected Solidity proof length")
			}
			vector := map[string]any{"scope": "tiny-backend-test-not-an-ix-wrapper", "proof": "0x" + hex.EncodeToString(payload), "digest": "0x" + hex.EncodeToString(digest[:]), "commitments": m, "domain": n}
			data, _ := json.MarshalIndent(vector, "", "  ")
			if err := atomicFile(filepath.Join(dir, "proof.json"), func(w io.Writer) error { _, err := w.Write(data); return err }); err != nil {
				t.Fatal(err)
			}
		}
		t.Logf("Ignition PLONK backend: N=%d commitments=%d native_bytes=%d solidity_bytes=%d", n, m, encoded.Len(), len(proof.(*plonkbn254.Proof).MarshalSolidity()))
	}
}

func verifyFixture(keyPath, trusted, proofPath string, claim []byte) error {
	key, err := os.ReadFile(keyPath)
	if err != nil {
		return err
	}
	proof, err := os.ReadFile(proofPath)
	if err != nil {
		return err
	}
	hash, err := hex.DecodeString(trusted)
	if err != nil {
		return err
	}
	vk := new(nativeVerifyingKey)
	if _, err := vk.ReadFrom(bytes.NewReader(key)); err != nil {
		return err
	}
	return verifyProof(key, hash, proof, claim, encodeAnchors(vk))
}

func TestPrepareCircuitMatchesGnarkSetup(t *testing.T) {
	schema, err := os.ReadFile(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	ccs, err := frontend.Compile(curveID.ScalarField(), scs.NewBuilder, &backendCircuit{Commit: true})
	if err != nil {
		t.Fatal(err)
	}
	domain := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + 2))
	dir := t.TempDir()
	circuit := filepath.Join(dir, "circuit.bin")
	if err := atomicFile(circuit, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err }); err != nil {
		t.Fatal(err)
	}
	circuitHash, err := fileHash(circuit)
	if err != nil {
		t.Fatal(err)
	}
	source, err := os.ReadFile(filepath.Join("testdata", "bn254", "srs.bin"))
	if err != nil {
		t.Fatal(err)
	}
	powers := domain + 3
	source = source[:88+2*g2ExportBytes+2*baseBytes*powers]
	binary.LittleEndian.PutUint64(source[80:88], powers)
	receipt := blake3.Sum256(source)
	srsPath := filepath.Join(dir, "srs.bin")
	if err := os.WriteFile(srsPath, source, 0600); err != nil {
		t.Fatal(err)
	}
	lagrangePath := filepath.Join(dir, "lagrange.bin")
	if err := prepareCircuit(schema, circuit, circuitHash, domain, srsPath, hex.EncodeToString(receipt[:]), lagrangePath, "", dir); err != nil {
		t.Fatal(err)
	}
	key, err := decodeVerifyingKey(schema)
	if err != nil {
		t.Fatal(err)
	}
	srs, err := readSRS(srsPath, hex.EncodeToString(receipt[:]), domain, key)
	if err != nil {
		t.Fatal(err)
	}
	lagrange, err := kzg.ToLagrangeG1(srs.Pk.G1[:domain])
	if err != nil {
		t.Fatal(err)
	}
	_, expected, err := plonk.Setup(ccs, srs, &kzg.SRS{Pk: kzg.ProvingKey{G1: lagrange}, Vk: srs.Vk})
	if err != nil {
		t.Fatal(err)
	}
	var encoded bytes.Buffer
	if _, err := expected.WriteTo(&encoded); err != nil {
		t.Fatal(err)
	}
	actual, err := os.ReadFile(filepath.Join(dir, "verifying-key.bin"))
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(actual, encoded.Bytes()) {
		t.Fatal("prepared verifying key differs from gnark Setup")
	}
	cached, err := fileHash(lagrangePath)
	if err != nil {
		t.Fatal(err)
	}
	if err := prepareCircuit(schema, circuit, circuitHash, domain, srsPath, hex.EncodeToString(receipt[:]), lagrangePath, cached.SHA256, dir); err != nil {
		t.Fatal(err)
	}
	circuitHash.SHA256 = hex.EncodeToString(make([]byte, 32))
	if err := prepareCircuit(schema, circuit, circuitHash, domain, srsPath, hex.EncodeToString(receipt[:]), lagrangePath, cached.SHA256, dir); err == nil {
		t.Fatal("accepted a different circuit digest")
	}
}
