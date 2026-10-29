//go:build (groth16 || !plonk) && !icicle

package main

import "fmt"

func groth16CUDAAvailable() bool { return false }

func newGroth16CUDAEngine(config groth16Backend) (*groth16Engine, error) {
	return nil, fmt.Errorf("CUDA Groth16 requires the worker built with groth16 and cuda and BN254 ICICLE libraries")
}
