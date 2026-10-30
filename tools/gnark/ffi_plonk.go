//go:build cgo && (plonk || !groth16)

package main

/*
#include "ffi.h"
*/
import "C"
import (
	"fmt"
	"runtime/cgo"
)

//export ix_gnark_compile
func ix_gnark_compile(schema C.ix_gnark_view, path C.ix_gnark_view) C.ix_gnark_result {
	return compileFFI(schema, path, compileCircuit)
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
