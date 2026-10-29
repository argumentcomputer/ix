package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	g16 "github.com/consensys/gnark/backend/groth16/bn254"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

func TestGroth16BackendInterop(t *testing.T) {
	for _, committed := range []bool{false, true} {
		t.Run(fmt.Sprintf("commitment_%t", committed), func(t *testing.T) {
			ccs, err := frontend.Compile(curveID.ScalarField(), r1cs.NewBuilder, &backendCircuit{Commit: committed})
			if err != nil {
				t.Fatal(err)
			}
			domain, commitments, err := groth16Shape(ccs)
			if err != nil {
				t.Fatal(err)
			}
			if (commitments == 1) != committed {
				t.Fatal("commitment census differs")
			}
			pk, vk, err := groth16.Setup(ccs)
			if err != nil {
				t.Fatal(err)
			}
			m := &groth16Manifest{InnerVK: hex.EncodeToString(make([]byte, 32)),
				Domain: domain, Constraints: ccs.GetNbConstraints(), PublicInputs: 2,
				Commitments: commitments, Files: make(map[string]artifact)}
			engine := &groth16Engine{key: pk, close: func() {}, prove: func(c constraint.ConstraintSystem, w witness.Witness) (groth16.Proof, error) {
				return groth16.Prove(c, pk, w, backend.WithProverHashToFieldFunction(sha256.New()))
			}}
			p := &groth16Session{ccs: ccs, vk: vk.(*g16.VerifyingKey), engine: engine, manifest: m}
			defer p.close()
			var digest [32]byte
			digest[0], digest[16] = 49, 1
			assignment := &backendCircuit{Claim: [2]frontend.Variable{49, 1}, X: 7, Commit: committed}
			var native, payload []byte
			for range 2 {
				native, payload, err = p.proveAssignment(assignment, digest[:])
				if err != nil {
					t.Fatal(err)
				}
			}
			wantSolidity := 256
			if committed {
				wantSolidity = 384
			}
			if len(payload) != wantSolidity || len(native) != 164+32*commitments {
				t.Fatal("unexpected proof encoding")
			}
			dir := t.TempDir()
			if root := os.Getenv("IX_GROTH16_TEST_OUTPUT"); root != "" {
				dir = filepath.Join(root, fmt.Sprintf("commitment_%t", committed))
			}
			if err := groth16SaveKeys(dir, m, pk, vk, "development", ""); err != nil {
				t.Fatal(err)
			}
			proofPath := filepath.Join(dir, "proof.bin")
			if err := atomicFile(proofPath, func(w io.Writer) error { _, err := w.Write(native); return err }); err != nil {
				t.Fatal(err)
			}
			keyPath, keyHash := filepath.Join(dir, "verifying-key.bin"), m.Files["verifying-key.bin"].SHA256
			if err := verifyGroth16Files(keyPath, keyHash, proofPath, hex.EncodeToString(digest[:])); err != nil {
				t.Fatal(err)
			}
			wrong := digest
			wrong[31] ^= 1
			if err := verifyGroth16Files(keyPath, keyHash, proofPath, hex.EncodeToString(wrong[:])); err == nil {
				t.Fatal("accepted another claim")
			}
			if err := verifyGroth16Files(keyPath, hex.EncodeToString(make([]byte, 32)), proofPath, hex.EncodeToString(digest[:])); err == nil {
				t.Fatal("accepted another key")
			}
			for _, malformed := range [][]byte{native[:len(native)-1], append(append([]byte(nil), native...), 0)} {
				if _, err := decodeGroth16Proof(malformed, commitments); err == nil {
					t.Fatal("accepted malformed length")
				}
			}
			bad := append([]byte(nil), native...)
			binary.BigEndian.PutUint32(bad[128:132], ^uint32(0))
			if _, err := decodeGroth16Proof(bad, commitments); err == nil {
				t.Fatal("accepted unbounded commitment count")
			}
			bad = append([]byte(nil), native...)
			copy(bad[:32], bytes.Repeat([]byte{0xff}, 32))
			if _, err := decodeGroth16Proof(bad, commitments); err == nil {
				t.Fatal("accepted invalid curve point")
			}
			if err := writeJSON(filepath.Join(dir, "proof.json"), map[string]any{
				"scope": "development-backend-fixture-not-an-ix-proof", "proof": "0x" + hex.EncodeToString(payload),
				"digest": "0x" + hex.EncodeToString(digest[:]), "commitments": commitments,
			}); err != nil {
				t.Fatal(err)
			}
			if _, _, err := p.proveAssignment(assignment, wrong[:]); err == nil {
				t.Fatal("accepted mismatched independently expected claim")
			}
			if _, _, err := p.proveAssignment(assignment, digest[:]); err == nil {
				t.Fatal("reused failed prover")
			}
			t.Logf("constraints=%d domain=%d commitments=%d native=%d solidity=%d", m.Constraints, domain, commitments, len(native), len(payload))
		})
	}
}

func TestGroth16BackendSelection(t *testing.T) {

	if _, err := newGroth16Engine(groth16Backend{Device: -1}); err == nil {
		t.Fatal("accepted invalid backend")
	}
	if !groth16CUDAAvailable() {

		if _, err := newGroth16Engine(groth16Backend{CUDA: true}); err == nil {
			t.Fatal("silently accepted unavailable CUDA")
		}
	}
}
