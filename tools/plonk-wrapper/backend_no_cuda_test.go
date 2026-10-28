//go:build !cuda

package main

import "testing"

func TestCUDARequestRequiresBuiltBackend(t *testing.T) {
	t.Setenv("IX_PLONK_BACKEND", "cuda")
	if err := validateProvingBackend(); err == nil {
		t.Fatal("accepted unavailable CUDA backend")
	}
	if _, err := configureProvingBackend(nil); err == nil {
		t.Fatal("configured unavailable CUDA backend")
	}
}
