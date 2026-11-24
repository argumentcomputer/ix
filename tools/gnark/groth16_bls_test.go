//go:build groth16 || !plonk

package main

import (
	"bytes"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark/backend/groth16"
	g16bls "github.com/consensys/gnark/backend/groth16/bls12-381"
	mpcbls "github.com/consensys/gnark/backend/groth16/bls12-381/mpcsetup"
	csbls "github.com/consensys/gnark/constraint/bls12-381"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

func verifyGroth16FilesBLS(keyPath, trusted, proofPath, claimHex string) error {
	key, err := os.ReadFile(keyPath)
	if err != nil {
		return err
	}
	proof, err := os.ReadFile(proofPath)
	if err != nil {
		return err
	}
	digest, err := hex.DecodeString(trusted)
	if err != nil {
		return err
	}
	claim, err := hex.DecodeString(claimHex)
	if err != nil {
		return err
	}
	return verifyGroth16BLS(key, digest, proof, claim)
}

func TestBLS12381Groth16BackendInterop(t *testing.T) {
	for _, committed := range []bool{false, true} {
		t.Run(fmt.Sprintf("commitment_%t", committed), func(t *testing.T) {
			ccs, err := frontend.Compile(blsCurveID.ScalarField(), r1cs.NewBuilder, &backendCircuit{Commit: committed})
			if err != nil {
				t.Fatal(err)
			}
			domain, commitments, err := groth16ShapeBLS(ccs)
			if err != nil {
				t.Fatal(err)
			}
			if (commitments == 1) != committed {
				t.Fatal("BLS12-381 commitment census differs")
			}
			pk, vk, err := groth16.Setup(ccs)
			if err != nil {
				t.Fatal(err)
			}
			m := &groth16Manifest{
				InnerVK:      hex.EncodeToString(make([]byte, 32)),
				Domain:       domain,
				Constraints:  ccs.GetNbConstraints(),
				PublicInputs: 2,
				Commitments:  commitments,
				Files:        make(map[string]artifact),
			}
			p := &groth16SessionBLS{ccs: ccs, pk: pk, vk: vk.(*g16bls.VerifyingKey), manifest: m}
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
			wantSolidity := 384
			if committed {
				wantSolidity = 576
			}
			if len(payload) != wantSolidity || len(native) != 244+48*commitments {
				t.Fatalf("unexpected BLS12-381 Groth16 proof encoding: native=%d solidity=%d", len(native), len(payload))
			}
			dir := t.TempDir()
			if root := os.Getenv("IX_BLS_GROTH16_TEST_OUTPUT"); root != "" {
				name := "plain"
				if committed {
					name = "committed"
				}
				dir = filepath.Join(root, name)
			}
			if err := groth16SaveKeysBLS(dir, m, pk, vk, "development", ""); err != nil {
				t.Fatal(err)
			}
			proofPath := filepath.Join(dir, "proof.bin")
			if err := atomicFile(proofPath, func(w io.Writer) error { _, err := w.Write(native); return err }); err != nil {
				t.Fatal(err)
			}
			keyPath, keyHash := filepath.Join(dir, "verifying-key.bin"), m.Files["verifying-key.bin"].SHA256
			if err := verifyGroth16FilesBLS(keyPath, keyHash, proofPath, hex.EncodeToString(digest[:])); err != nil {
				t.Fatal(err)
			}
			wrong := digest
			wrong[31] ^= 1
			if err := verifyGroth16FilesBLS(keyPath, keyHash, proofPath, hex.EncodeToString(wrong[:])); err == nil {
				t.Fatal("accepted another BLS12-381 Groth16 claim")
			}
			if err := verifyGroth16FilesBLS(keyPath, hex.EncodeToString(make([]byte, 32)), proofPath, hex.EncodeToString(digest[:])); err == nil {
				t.Fatal("accepted another BLS12-381 Groth16 key")
			}
			for _, malformed := range [][]byte{native[:len(native)-1], append(append([]byte(nil), native...), 0)} {
				if _, err := decodeGroth16ProofBLS(malformed, commitments); err == nil {
					t.Fatal("accepted malformed BLS12-381 Groth16 proof length")
				}
			}
			bad := append([]byte(nil), native...)
			binary.BigEndian.PutUint32(bad[192:196], ^uint32(0))
			if _, err := decodeGroth16ProofBLS(bad, commitments); err == nil {
				t.Fatal("accepted unbounded BLS12-381 Groth16 commitment count")
			}
			bad = append([]byte(nil), native...)
			copy(bad[:48], bytes.Repeat([]byte{0xff}, 48))
			if _, err := decodeGroth16ProofBLS(bad, commitments); err == nil {
				t.Fatal("accepted invalid BLS12-381 Groth16 curve point")
			}
			if err := writeJSON(filepath.Join(dir, "proof.json"), map[string]any{
				"scope":       "bls12-381-development-backend-fixture-not-an-ix-proof",
				"curve":       "bls12-381",
				"proof":       "0x" + hex.EncodeToString(payload),
				"digest":      "0x" + hex.EncodeToString(digest[:]),
				"commitments": commitments,
			}); err != nil {
				t.Fatal(err)
			}
			if _, _, err := p.proveAssignment(assignment, wrong[:]); err == nil {
				t.Fatal("accepted mismatched independently expected BLS12-381 Groth16 claim")
			}
			if _, _, err := p.proveAssignment(assignment, digest[:]); err == nil {
				t.Fatal("reused failed BLS12-381 Groth16 prover")
			}
			t.Logf("BLS12-381 Groth16: constraints=%d domain=%d commitments=%d native=%d solidity=%d", m.Constraints, domain, commitments, len(native), len(payload))
		})
	}
}

func TestBLS12381Groth16MPCSetup(t *testing.T) {
	ccs, err := frontend.Compile(blsCurveID.ScalarField(), r1cs.NewBuilder, &backendCircuit{Commit: true})
	if err != nil {
		t.Fatal(err)
	}
	domain, commitments, err := groth16ShapeBLS(ccs)
	if err != nil {
		t.Fatal(err)
	}
	firstBeacon, secondBeacon := bytes.Repeat([]byte{3}, 32), bytes.Repeat([]byte{4}, 32)
	phase1 := mpcbls.NewPhase1(domain)
	phase1.Contribute()
	commons, err := mpcbls.VerifyPhase1(domain, firstBeacon, phase1)
	if err != nil {
		t.Fatal(err)
	}
	phase2 := new(mpcbls.Phase2)
	evaluations := phase2.Initialize(ccs.(*csbls.R1CS), &commons)
	phase2.Contribute()
	pk, vk := phase2.Seal(&commons, &evaluations, secondBeacon)

	m := &groth16Manifest{
		InnerVK:      hex.EncodeToString(make([]byte, 32)),
		Domain:       domain,
		Constraints:  ccs.GetNbConstraints(),
		PublicInputs: 2,
		Commitments:  commitments,
		Files:        make(map[string]artifact),
	}
	dir := t.TempDir()
	if err := groth16SaveKeysBLS(dir, m, pk, vk, "mpc", hex.EncodeToString(firstBeacon)); err != nil {
		t.Fatal(err)
	}
	p := &groth16SessionBLS{ccs: ccs, pk: pk, vk: vk.(*g16bls.VerifyingKey), manifest: m}
	defer p.close()
	var digest [32]byte
	digest[0], digest[16] = 49, 1
	native, _, err := p.proveAssignment(&backendCircuit{Claim: [2]frontend.Variable{49, 1}, X: 7, Commit: true}, digest[:])
	if err != nil {
		t.Fatal(err)
	}
	keyBytes, err := os.ReadFile(filepath.Join(dir, "verifying-key.bin"))
	if err != nil {
		t.Fatal(err)
	}
	trusted, err := hex.DecodeString(m.Files["verifying-key.bin"].SHA256)
	if err != nil {
		t.Fatal(err)
	}
	if err := verifyGroth16BLS(keyBytes, trusted, native, digest[:]); err != nil {
		t.Fatal(err)
	}
}
