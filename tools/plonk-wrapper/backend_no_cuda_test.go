//go:build (plonk || !groth16) && !cuda

package main

import "testing"

func TestCUDARequestRequiresBuiltBackend(t *testing.T) {
	if _, err := configureBackend(nil, backendConfig{CUDA: true}); err == nil {
		t.Fatal("accepted unavailable CUDA backend")
	}
}
