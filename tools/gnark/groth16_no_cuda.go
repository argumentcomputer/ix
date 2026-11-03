//go:build (groth16 || !plonk) && !icicle

package main

import "fmt"

func groth16CUDAAvailable() bool { return false }

func newGroth16CUDAEngine(config groth16Backend) (*groth16Engine, error) {
	return nil, fmt.Errorf("ix was built without Groth16 CUDA support; rebuild it with IX_CUDA=1 IX_GROTH16=1 and the BN254 ICICLE libraries")
}
