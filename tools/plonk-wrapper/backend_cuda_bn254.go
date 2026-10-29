//go:build cuda

package main

import (
	"encoding/json"
	"fmt"
	"os"
	"sync"

	"github.com/argumentcomputer/ix/tools/plonk-wrapper/internal/cuda"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
)

func configureBackend(pk plonk.ProvingKey, options backendConfig) (func() error, error) {
	if !options.CUDA {
		return func() error { return nil }, nil
	}
	config := cuda.Config{Device: options.Device, MemoryBytes: options.MemoryBytes, HeadroomBytes: 8 << 30}
	if options.MaskMSM {
		config.MSMStrategy = cuda.MSMMask
	}
	nativePK, ok := pk.(*plonkbn254.ProvingKey)
	if !ok {
		return nil, fmt.Errorf("CUDA PLONK requires a BN254 proving key")
	}
	accelerator, err := cuda.Attach(nativePK, config)
	if err != nil {
		return nil, err
	}
	var once sync.Once
	var closeErr error
	return func() error {
		once.Do(func() {
			closeErr = accelerator.Close()
			stats, statsErr := accelerator.Stats()
			if statsErr == nil {
				data, err := json.Marshal(struct {
					Kind     string     `json:"kind"`
					Device   int        `json:"device"`
					Strategy string     `json:"msm_strategy"`
					Stats    cuda.Stats `json:"stats"`
				}{"plonk_cuda_metrics", config.Device, config.MSMStrategy.String(), stats})
				if err == nil {
					fmt.Fprintln(os.Stderr, string(data))
				}
			}
		})
		return closeErr
	}, nil
}
