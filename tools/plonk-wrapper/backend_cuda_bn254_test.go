//go:build cuda

package main

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/argumentcomputer/ix/tools/plonk-wrapper/internal/cuda"
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/plonk"
	native "github.com/consensys/gnark/backend/plonk/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/scs"
)

func TestCUDAProvingBackendFactory(t *testing.T) {
	if os.Getenv("IX_PLONK_CUDA_TEST") != "1" {
		t.Skip("set IX_PLONK_CUDA_TEST=1 for the native CUDA backend factory proof test")
	}
	t.Setenv("IX_PLONK_BACKEND", "cuda")
	t.Setenv("IX_PLONK_CUDA_MEMORY_GIB", "8")
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
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), scs.NewBuilder, &backendCircuit{Commit: true})
	if err != nil {
		t.Fatal(err)
	}
	n := ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints() + ccs.GetNbPublicVariables()))
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
	public, err := frontend.NewWitness(&publicClaim{Claim: [2]frontend.Variable{49, 1}}, ecc.BN254.ScalarField(), frontend.PublicOnly())
	if err != nil {
		t.Fatal(err)
	}
	cleanup, err := configureProvingBackend(pk)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := cleanup(); err != nil {
			t.Error(err)
		}
	})
	nativePK := pk.(*native.ProvingKey)
	accelerator, ok := nativePK.Accelerator().(*cuda.Accelerator)
	if !ok {
		t.Fatal("CUDA factory did not attach its accelerator")
	}
	proof, err := plonk.Prove(ccs, pk, w, solidity.WithProverTargetSolidityVerifier(backend.PLONK))
	if err != nil {
		t.Fatal(err)
	}
	if err := plonk.Verify(proof, vk, public, solidity.WithVerifierTargetSolidityVerifier(backend.PLONK)); err != nil {
		t.Fatal(err)
	}
	stats, err := accelerator.Stats()
	if err != nil {
		t.Fatal(err)
	}
	if stats.MSMCalls == 0 || stats.QuotientCalls != 1 || stats.NumeratorCalls != 0 {
		t.Fatalf("factory proof did not execute fused CUDA operations: %+v", stats)
	}
	for range 2 {
		if err := cleanup(); err != nil {
			t.Fatal(err)
		}
		if nativePK.Accelerator() != nil {
			t.Fatal("CUDA factory cleanup left an attached accelerator")
		}
	}
}
