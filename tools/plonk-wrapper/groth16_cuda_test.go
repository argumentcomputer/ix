//go:build icicle

package main

import (
	"bytes"
	"crypto/sha256"
	"os"
	"testing"

	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

func TestGroth16CUDAInterop(t *testing.T) {
	if os.Getenv("IX_GROTH16_CUDA_TEST") != "1" {
		t.Skip("set IX_GROTH16_CUDA_TEST=1 on a CUDA host")
	}
	t.Setenv("IX_GROTH16_BACKEND", "cuda")
	for _, committed := range []bool{false, true} {
		ccs, err := frontend.Compile(curveID.ScalarField(), r1cs.NewBuilder, &backendCircuit{Commit: committed})
		if err != nil {
			t.Fatal(err)
		}
		pk, vk, err := groth16.Setup(ccs)
		if err != nil {
			t.Fatal(err)
		}
		var encoded bytes.Buffer
		if _, err := pk.WriteTo(&encoded); err != nil {
			t.Fatal(err)
		}
		w, err := frontend.NewWitness(&backendCircuit{Claim: [2]frontend.Variable{49, 1}, X: 7, Commit: committed}, curveID.ScalarField())
		if err != nil {
			t.Fatal(err)
		}
		public, err := w.Public()
		if err != nil {
			t.Fatal(err)
		}
		for _, pin := range []string{"0", "1"} {
			t.Setenv("IX_GROTH16_PIN_KEY", pin)
			engine, err := newGroth16Engine(groth16Backend{CUDA: true, PinKeys: pin == "1", Library: os.Getenv("ICICLE_BACKEND_INSTALL_DIR")})
			if err != nil {
				t.Fatal(err)
			}
			func() {
				defer engine.close()
				if _, err := engine.key.ReadFrom(bytes.NewReader(encoded.Bytes())); err != nil {
					t.Fatal(err)
				}
				for range 2 {
					proof, err := engine.prove(ccs, w)
					if err != nil {
						t.Fatal(err)
					}
					if err := groth16.Verify(proof, vk, public, backend.WithVerifierHashToFieldFunction(sha256.New())); err != nil {
						t.Fatal(err)
					}
				}
			}()
		}
	}
}
