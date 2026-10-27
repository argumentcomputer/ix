//go:build !bn254 || !cuda

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
		return fmt.Errorf("CUDA PLONK requires a helper built with bn254,cuda and cgo")
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
