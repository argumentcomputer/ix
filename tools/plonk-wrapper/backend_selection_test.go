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
