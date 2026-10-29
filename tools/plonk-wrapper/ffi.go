//go:build cgo

package main

/*
#include "ffi.h"
#include <stdlib.h>
*/
import "C"

import (
	"encoding/json"
	"fmt"
	"os"
	"runtime/cgo"
	"unsafe"

	"github.com/consensys/gnark/logger"
)

type retainedProver interface {
	prove([]byte, []byte) ([]byte, []byte, error)
	close() error
}

func init() { logger.SetOutput(os.Stderr) }

func borrowed(view C.ix_gnark_view, limit uint64) ([]byte, error) {
	if uint64(view.len) > limit || (view.len != 0 && view.data == nil) {
		return nil, fmt.Errorf("invalid FFI buffer")
	}
	return unsafe.Slice((*byte)(unsafe.Pointer(view.data)), int(view.len)), nil
}
func text(view C.ix_gnark_view) (string, error) { b, e := borrowed(view, 16<<10); return string(b), e }
func buffer(data []byte) (*C.uint8_t, C.size_t) {
	if len(data) == 0 {
		return nil, 0
	}
	return (*C.uint8_t)(C.CBytes(data)), C.size_t(len(data))
}
func failure(err error) C.ix_gnark_result {
	message := []byte(err.Error())
	if len(message) == 0 {
		message = []byte("gnark operation failed")
	}
	if len(message) > 8192 {
		message = message[:8192]
	}
	var result C.ix_gnark_result
	result.error, result.error_len = buffer(message)
	return result
}
func guarded(call func() (C.ix_gnark_result, error)) (result C.ix_gnark_result) {
	defer func() {
		if r := recover(); r != nil {
			result = failure(fmt.Errorf("gnark panic: %v", r))
		}
	}()
	result, err := call()
	if err != nil {
		return failure(err)
	}
	return result
}

//export ix_gnark_compile
func ix_gnark_compile(schema C.ix_gnark_view, path C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		data, err := borrowed(schema, 16<<20)
		if err != nil {
			return result, err
		}
		output, err := text(path)
		if err != nil {
			return result, err
		}
		info, err := compileCircuit(data, output)
		if err != nil {
			return result, err
		}
		encoded, err := json.Marshal(info)
		if err != nil {
			return result, err
		}
		result.data, result.len = buffer(encoded)
		return result, nil
	})
}

//export ix_gnark_prepare
func ix_gnark_prepare(schema, circuit, circuitHash C.ix_gnark_view, circuitBytes, domain C.uint64_t, srs, receipt, lagrange, lagrangeHash, output C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		data, err := borrowed(schema, 16<<20)
		if err != nil {
			return result, err
		}
		strings := make([]string, 7)
		for i, view := range []C.ix_gnark_view{circuit, circuitHash, srs, receipt, lagrange, lagrangeHash, output} {
			strings[i], err = text(view)
			if err != nil {
				return result, err
			}
		}
		if uint64(circuitBytes) > 1<<40 {
			return result, fmt.Errorf("invalid circuit size")
		}
		return result, prepareCircuit(data, strings[0], artifact{SHA256: strings[1], Bytes: int64(circuitBytes)}, uint64(domain), strings[2], strings[3], strings[4], strings[5], strings[6])
	})
}

//export ix_gnark_open
func ix_gnark_open(directory, metadata C.ix_gnark_view, options C.ix_gnark_backend) C.ix_gnark_result {
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
			return result, fmt.Errorf("invalid backend configuration")
		}
		p, err := openProver(dir, data, backendConfig{CUDA: options.cuda == 1, Device: int(options.device), MemoryBytes: uint64(options.memory_bytes), MaskMSM: options.mask_msm == 1})
		if err != nil {
			return result, err
		}
		result.handle = C.uintptr_t(cgo.NewHandle(p))
		return result, nil
	})
}

//export ix_gnark_prove
func ix_gnark_prove(handle C.uintptr_t, witness, claim C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		p := cgo.Handle(handle).Value().(retainedProver)
		data, err := borrowed(witness, 16<<20)
		if err != nil {
			return result, err
		}
		digest, err := borrowed(claim, 32)
		if err != nil {
			return result, err
		}
		native, solidity, err := p.prove(data, digest)
		if err != nil {
			return result, err
		}
		result.data, result.len = buffer(native)
		result.solidity, result.solidity_len = buffer(solidity)
		return result, nil
	})
}

//export ix_gnark_verify
func ix_gnark_verify(key, keyHash, proof, claim, anchors C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		values := make([][]byte, 5)
		for i, view := range []C.ix_gnark_view{key, keyHash, proof, claim, anchors} {
			values[i], err = borrowed(view, 1<<20)
			if err != nil {
				return result, err
			}
		}
		return result, verifyProof(values[0], values[1], values[2], values[3], values[4])
	})
}

//export ix_gnark_close
func ix_gnark_close(handle C.uintptr_t) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		h := cgo.Handle(handle)
		p := h.Value().(retainedProver)
		defer h.Delete()
		return result, p.close()
	})
}

//export ix_gnark_free
func ix_gnark_free(pointer unsafe.Pointer) { C.free(pointer) }
