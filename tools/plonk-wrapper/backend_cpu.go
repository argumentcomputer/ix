//go:build (plonk || !groth16) && !cuda

package main

import (
	"fmt"
	"github.com/consensys/gnark/backend/plonk"
)

func configureBackend(_ plonk.ProvingKey, config backendConfig) (func() error, error) {
	if config.CUDA {
		return nil, fmt.Errorf("this worker was built without PLONK CUDA support")
	}
	return func() error { return nil }, nil
}
