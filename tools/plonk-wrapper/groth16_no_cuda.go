//go:build !icicle

package main

import "fmt"

func groth16CUDAAvailable() bool { return false }

func newGroth16CUDAEngine() (*groth16Engine, error) {
	return nil, fmt.Errorf("CUDA Groth16 requires the helper built with the icicle tag and BN254 ICICLE libraries")
}
