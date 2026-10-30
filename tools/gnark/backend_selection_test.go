//go:build plonk || !groth16

package main

import "testing"

func TestCPUBackendSelectionNeedsNoGPU(t *testing.T) {
	close, err := configureBackend(nil, backendConfig{})
	if err != nil {
		t.Fatal(err)
	}
	if err := close(); err != nil {
		t.Fatal(err)
	}
	if err := close(); err != nil {
		t.Fatal(err)
	}
}

func TestCUDARequestRequiresBuiltBackend(t *testing.T) {
	if plonkCUDAAvailable() {
		t.Skip("PLONK CUDA backend is built")
	}
	if _, err := configureBackend(nil, backendConfig{CUDA: true}); err == nil {
		t.Fatal("accepted unavailable CUDA backend")
	}
}
