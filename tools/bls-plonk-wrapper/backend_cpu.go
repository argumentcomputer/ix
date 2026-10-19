//go:build bls12381 || !cuda

package main

import (
	"fmt"
	"os"

	"github.com/consensys/gnark/backend/plonk"
)

func validateProvingBackend() error {
	switch os.Getenv("IX_PLONK_BACKEND") {
	case "", "cpu":
		return nil
	case "cuda":
		return fmt.Errorf("CUDA PLONK requires a BN254 helper built with the cuda tag and cgo")
	default:
		return fmt.Errorf("IX_PLONK_BACKEND must be cpu or cuda")
	}
}

func configureProvingBackend(_ plonk.ProvingKey) (func() error, error) {
	if err := validateProvingBackend(); err != nil {
		return nil, err
	}
	return func() error { return nil }, nil
}
