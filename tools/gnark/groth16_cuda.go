//go:build (groth16 || !plonk) && icicle

package main

import (
	"crypto/sha256"
	"fmt"
	"runtime"
	"sync"

	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/accelerated/icicle"
	accelerated "github.com/consensys/gnark/backend/accelerated/icicle/groth16/bn254"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	cs "github.com/consensys/gnark/constraint/bn254"
	cr "github.com/ingonyama-zk/icicle-gnark/v3/wrappers/golang/runtime"
)

var groth16CUDAInit sync.Once
var groth16CUDAInitError error
var groth16CUDADevices sync.Map

func groth16CUDAAvailable() bool { return true }

func onGroth16Device(device *cr.Device, call func() error) error {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()
	previous, previousStatus := cr.GetActiveDevice()
	if status := cr.SetDevice(device); status != cr.Success {
		return fmt.Errorf("select Groth16 CUDA device %d: %s", device.Id, status.AsString())
	}
	if previousStatus == cr.Success {
		defer cr.SetDevice(previous)
	}
	return call()
}

func newGroth16CUDAEngine(config groth16Backend) (*groth16Engine, error) {
	deviceID := config.Device
	groth16CUDAInit.Do(func() {
		var status cr.EIcicleError
		if config.Library != "" {
			status = cr.LoadBackend(config.Library, true)
		} else {
			status = cr.LoadBackendFromEnvOrDefault()
		}
		if status != cr.Success {
			groth16CUDAInitError = fmt.Errorf("load Groth16 CUDA backend: %s", status.AsString())
		}
	})
	if groth16CUDAInitError != nil {
		return nil, groth16CUDAInitError
	}
	device := cr.CreateDevice("CUDA", deviceID)
	if err := onGroth16Device(&device, func() error {
		_, status := cr.GetAvailableMemory()
		if status != cr.Success {
			return fmt.Errorf("Groth16 CUDA memory query: %s", status.AsString())
		}
		return nil
	}); err != nil {
		return nil, err
	}
	value, _ := groth16CUDADevices.LoadOrStore(deviceID, new(sync.Mutex))
	lock := value.(*sync.Mutex)
	pk := new(accelerated.ProvingKey)
	engine := &groth16Engine{key: pk, native: &pk.ProvingKey}
	engine.prove = func(ccs constraint.ConstraintSystem, w witness.Witness) (proof groth16.Proof, err error) {
		lock.Lock()
		defer lock.Unlock()
		config, err := icicle.NewConfig(icicle.WithDeviceID(deviceID), icicle.WithPinKeysToGPU(false),
			icicle.WithProverOptions(backend.WithProverHashToFieldFunction(sha256.New())))
		if err != nil {
			return nil, err
		}
		err = onGroth16Device(&device, func() error {
			var failure error
			proof, failure = accelerated.Prove(ccs.(*cs.R1CS), pk, w, config)
			return failure
		})
		return proof, err
	}
	engine.close = func() {
		lock.Lock()
		defer lock.Unlock()
		if err := onGroth16Device(&device, func() error { pk.FreeGPUResources(); return nil }); err != nil {
			panic(err)
		}
	}
	return engine, nil
}
