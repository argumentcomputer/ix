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

func compileFFI(schema C.ix_gnark_view, path C.ix_gnark_view, compile func([]byte, string) (circuitInfo, error)) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		data, err := borrowed(schema, 16<<20)
		if err != nil {
			return result, err
		}
		output, err := text(path)
		if err != nil {
			return result, err
		}
		info, err := compile(data, output)
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
