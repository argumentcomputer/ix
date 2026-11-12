//go:build cgo && (plonk || !groth16)

package main

/*
#include "ffi.h"
*/
import "C"

//export ix_gnark_aiur_compile
func ix_gnark_aiur_compile(schema C.ix_gnark_view, path C.ix_gnark_view) C.ix_gnark_result {
	return compileFFI(schema, path, compileAiur)
}
