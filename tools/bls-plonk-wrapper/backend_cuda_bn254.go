//go:build bn254 && cuda

package main

import (
	"encoding/json"
	"fmt"
	"math"
	"os"
	"strconv"
	"sync"

	"github.com/argumentcomputer/ix/tools/bls-plonk-wrapper/internal/cuda"
	"github.com/consensys/gnark/backend/plonk"
	plonkbn254 "github.com/consensys/gnark/backend/plonk/bn254"
)

func provingCUDAConfig() (cuda.Config, error) {
	config := cuda.Config{MemoryBytes: 64 << 30, HeadroomBytes: 8 << 30, Features: cuda.AllFeatures}
	switch os.Getenv("IX_PLONK_CUDA_MSM_STRATEGY") {
	case "", "split":
		config.MSMStrategy = cuda.MSMSplit
	case "mask":
		config.MSMStrategy = cuda.MSMMask
	default:
		return config, fmt.Errorf("IX_PLONK_CUDA_MSM_STRATEGY must be split or mask")
	}
	if value := os.Getenv("IX_PLONK_CUDA_DEVICE"); value != "" {
		device, err := strconv.ParseUint(value, 10, 31)
		if err != nil {
			return config, fmt.Errorf("invalid IX_PLONK_CUDA_DEVICE: %w", err)
		}
		config.Device = int(device)
	}
	if value := os.Getenv("IX_PLONK_CUDA_MEMORY_GIB"); value != "" {
		gib, err := strconv.ParseUint(value, 10, 64)
		if err != nil || gib == 0 || gib > math.MaxUint64>>30 {
			return config, fmt.Errorf("IX_PLONK_CUDA_MEMORY_GIB must be a positive bounded integer")
		}
		config.MemoryBytes = gib << 30
	}
	return config, nil
}

func validateProvingBackend() error {
	switch os.Getenv("IX_PLONK_BACKEND") {
	case "", "cpu":
		return nil
	case "cuda":
		_, err := provingCUDAConfig()
		return err
	default:
		return fmt.Errorf("IX_PLONK_BACKEND must be cpu or cuda")
	}
}

func configureProvingBackend(pk plonk.ProvingKey) (func() error, error) {
	if err := validateProvingBackend(); err != nil {
		return nil, err
	}
	if os.Getenv("IX_PLONK_BACKEND") != "cuda" {
		return func() error { return nil }, nil
	}
	config, err := provingCUDAConfig()
	if err != nil {
		return nil, err
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
