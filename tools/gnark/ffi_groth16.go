//go:build cgo && (groth16 || !plonk)

package main

/*
#include "ffi.h"
*/
import "C"

import (
	"fmt"
	"runtime/cgo"
)

//export ix_gnark_groth16_compile
func ix_gnark_groth16_compile(schema, path C.ix_gnark_view) C.ix_gnark_result {
	return compileFFI(schema, path, compileGroth16)
}

//export ix_gnark_groth16_setup
func ix_gnark_groth16_setup(directory, metadata C.ix_gnark_view, kind C.uint32_t, descriptor, pin C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		dir, err := text(directory)
		if err != nil {
			return result, err
		}
		data, err := borrowed(metadata, 1<<20)
		if err != nil {
			return result, err
		}
		file, err := text(descriptor)
		if err != nil {
			return result, err
		}
		digest, err := text(pin)
		if err != nil {
			return result, err
		}
		encoded, err := setupGroth16(dir, data, uint32(kind), file, digest)
		if err != nil {
			return result, err
		}
		result.data, result.len = buffer(encoded)
		return result, nil
	})
}

//export ix_gnark_groth16_open
func ix_gnark_groth16_open(directory, metadata C.ix_gnark_view, options C.ix_gnark_groth16_backend) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		dir, err := text(directory)
		if err != nil {
			return result, err
		}
		data, err := borrowed(metadata, 1<<20)
		if err != nil {
			return result, err
		}
		library, err := text(options.library)
		if err != nil {
			return result, err
		}
		if options.cuda > 1 || options.device < 0 {
			return result, fmt.Errorf("invalid Groth16 backend configuration")
		}
		p, err := openGroth16(dir, data, groth16Backend{CUDA: options.cuda == 1, Device: int(options.device), Library: library})
		if err != nil {
			return result, err
		}
		result.handle = C.uintptr_t(cgo.NewHandle(p))
		return result, nil
	})
}

//export ix_gnark_groth16_verify
func ix_gnark_groth16_verify(key, digest, proof, claim C.ix_gnark_view) C.ix_gnark_result {
	return guarded(func() (result C.ix_gnark_result, err error) {
		values := make([][]byte, 4)
		for i, v := range []C.ix_gnark_view{key, digest, proof, claim} {
			values[i], err = borrowed(v, 1<<20)
			if err != nil {
				return result, err
			}
		}
		return result, verifyGroth16(values[0], values[1], values[2], values[3])
	})
}
