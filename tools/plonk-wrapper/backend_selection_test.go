package main

import "testing"

func TestCPUBackendSelectionNeedsNoGPU(t *testing.T) {
	t.Setenv("IX_PLONK_BACKEND", "cpu")
	t.Setenv("IX_PLONK_CUDA_DEVICE", "invalid")
	t.Setenv("IX_PLONK_CUDA_MEMORY_GIB", "invalid")
	t.Setenv("IX_PLONK_CUDA_MSM_STRATEGY", "invalid")
	if err := validateProvingBackend(); err != nil {
		t.Fatal(err)
	}
	close, err := configureProvingBackend(nil)
	if err != nil {
		t.Fatal(err)
	}
	if err := close(); err != nil {
		t.Fatal(err)
	}
	if err := close(); err != nil {
		t.Fatal(err)
	}
	t.Setenv("IX_PLONK_BACKEND", "unknown")
	if err := validateProvingBackend(); err == nil {
		t.Fatal("accepted unknown backend")
	}
}
