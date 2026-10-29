//go:build cgo

package main

import (
	"errors"
	"testing"
	"unsafe"
)

func TestEmptyFFIErrorIsNotSuccess(t *testing.T) {
	result := failure(errors.New(""))
	if result.error == nil || result.error_len == 0 {
		t.Fatal("empty error message became a successful FFI result")
	}
	ix_gnark_free(unsafe.Pointer(result.error))
}
