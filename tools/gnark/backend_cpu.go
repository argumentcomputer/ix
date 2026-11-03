//go:build (plonk || !groth16) && !cuda

package main

import (
	"fmt"
	"github.com/consensys/gnark/backend/plonk"
)

func plonkCUDAAvailable() bool { return false }

func configureBackend(_ plonk.ProvingKey, config backendConfig) (func() error, error) {
	if config.CUDA {
		return nil, fmt.Errorf("ix was built without PLONK CUDA support; rebuild it with IX_CUDA=1 IX_PLONK=1")
	}
	return func() error { return nil }, nil
}
