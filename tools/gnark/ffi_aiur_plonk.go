//go:build cgo && (plonk || !groth16)

package main

/*
#include "ffi.h"
*/
import "C"
import (
	"bytes"
	"encoding/json"
	"fmt"
	"runtime/cgo"
)

//export ix_gnark_aiur_compile
func ix_gnark_aiur_compile(schema C.ix_gnark_view, path C.ix_gnark_view) C.ix_gnark_result {
	return compileFFI(schema, path, compileAiur)
}

//export ix_gnark_aiur_prepare
func ix_gnark_aiur_prepare(request C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		data, err := borrowed(request, 17<<20)
		if err != nil {
			return result, err
		}
		var input aiurPreparation
		if err := decodeReader(bytes.NewReader(data), &input); err != nil {
			return result, err
		}
		metadata, err := prepareAiur(&input)
		if err != nil {
			return result, err
		}
		encoded, err := json.Marshal(metadata)
		if err != nil {
			return result, err
		}
		result.data, result.len = buffer(encoded)
		return result, nil
	})
}

//export ix_gnark_aiur_open
func ix_gnark_aiur_open(directory, metadata C.ix_gnark_view, options C.ix_gnark_backend) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		dir, err := text(directory)
		if err != nil {
			return result, err
		}
		data, err := borrowed(metadata, 1<<20)
		if err != nil {
			return result, err
		}
		if options.cuda > 1 || options.mask_msm > 1 || options.device < 0 {
			return result, fmt.Errorf("invalid Aiur backend configuration")
		}
		p, err := openAiurProver(dir, data, backendConfig{CUDA: options.cuda == 1, Device: int(options.device), MemoryBytes: uint64(options.memory_bytes), MaskMSM: options.mask_msm == 1})
		if err != nil {
			return result, err
		}
		result.handle = C.uintptr_t(cgo.NewHandle(p))
		return result, nil
	})
}

//export ix_gnark_aiur_prove
func ix_gnark_aiur_prove(handle C.uintptr_t, encoded, expected C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		p, ok := cgo.Handle(handle).Value().(*aiurProver)
		if !ok {
			return result, fmt.Errorf("handle is not an Aiur prover")
		}
		data, err := borrowed(encoded, aiurMaxWitnessBytes)
		if err != nil {
			return result, err
		}
		public, err := borrowed(expected, 32*aiurMaxPublic)
		if err != nil {
			return result, err
		}
		native, solidity, err := p.prove(data, public)
		if err != nil {
			return result, err
		}
		result.data, result.len = buffer(native)
		result.solidity, result.solidity_len = buffer(solidity)
		return result, nil
	})
}

//export ix_gnark_aiur_verify
func ix_gnark_aiur_verify(key, pin, proof, public, anchors C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		values := make([][]byte, 5)
		for i, view := range []C.ix_gnark_view{key, pin, proof, public, anchors} {
			values[i], err = borrowed(view, 1<<20)
			if err != nil {
				return result, err
			}
		}
		return result, verifyAiurProof(values[0], values[1], values[2], values[3], values[4])
	})
}
