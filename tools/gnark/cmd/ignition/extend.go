package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/kzg"
)

// WriteRawTo encodes two G2 anchors, one G1 anchor and the prepared lines.
const verificationKeyBytes = 2*128 + 64 + 2*2*66*2*64

func readCanonicalG1(encoded []byte) (bn254.G1Affine, error) {
	var point bn254.G1Affine
	used, err := point.SetBytes(encoded)
	if err != nil {
		return point, err
	}
	raw := point.RawBytes()
	if used != len(raw) || !bytes.Equal(raw[:], encoded) || point.IsInfinity() || !point.IsInSubGroup() {
		return point, fmt.Errorf("invalid canonical nonzero G1 point")
	}
	return point, nil
}

// The trusted digest authenticates the whole existing prefix and its anchors.
// Nondegeneracy fixes each added point uniquely through
// e(next, G2) = e(previous, tau*G2). Candidate bytes need no independent trust.
// The output preserves every old point and the complete verifier-key suffix.
func extendSRS(source, expectedDigest, candidates, output string, powers int) error {
	expected, err := hex.DecodeString(expectedDigest)
	if err != nil || len(expected) != sha256.Size || source == "" || candidates == "" {
		return fmt.Errorf("extension requires a source, trusted SHA-256 and additional G1 file")
	}
	if !validPowerCount(powers) {
		return fmt.Errorf("powers must be in [2, 100800000]")
	}
	input, err := os.Open(source)
	if err != nil {
		return err
	}
	defer input.Close()
	var header [4]byte
	if _, err := io.ReadFull(input, header[:]); err != nil {
		return err
	}
	count := int(binary.BigEndian.Uint32(header[:]))
	if !validPowerCount(count) || powers <= count {
		return fmt.Errorf("extension requires more powers than the existing valid prefix")
	}
	info, err := input.Stat()
	if err != nil {
		return err
	}
	if info.Size() != 4+int64(count)*64+verificationKeyBytes {
		return fmt.Errorf("invalid source WriteRawTo length")
	}
	additional, err := os.Open(candidates)
	if err != nil {
		return err
	}
	defer additional.Close()
	info, err = additional.Stat()
	if err != nil {
		return err
	}
	if info.Size() != int64(powers-count)*64 {
		return fmt.Errorf("additional G1 count differs from requested extension")
	}
	file, err := os.CreateTemp(filepath.Dir(output), ".ignition-extension-*.bin")
	if err != nil {
		return err
	}
	defer os.Remove(file.Name())
	defer file.Close()
	writer := bufio.NewWriterSize(file, 1<<20)
	digest := sha256.New()
	digest.Write(header[:])
	binary.BigEndian.PutUint32(header[:], uint32(powers))
	if _, err := writer.Write(header[:]); err != nil {
		return err
	}
	if _, err := io.CopyN(io.MultiWriter(writer, digest), input, int64(count-1)*64); err != nil {
		return err
	}
	var last [64]byte
	if _, err := io.ReadFull(input, last[:]); err != nil {
		return err
	}
	digest.Write(last[:])
	if _, err := writer.Write(last[:]); err != nil {
		return err
	}
	suffix := make([]byte, verificationKeyBytes)
	if _, err := io.ReadFull(input, suffix); err != nil {
		return err
	}
	digest.Write(suffix)
	if !bytes.Equal(digest.Sum(nil), expected) {
		return fmt.Errorf("source SRS differs from the independently trusted SHA-256")
	}
	var vk kzg.VerifyingKey
	reader := bytes.NewReader(suffix)
	if _, err := vk.ReadFrom(reader); err != nil {
		return err
	}
	if reader.Len() != 0 {
		return fmt.Errorf("trailing source verifier-key bytes")
	}
	for _, anchor := range vk.G2 {
		if anchor.IsInfinity() || !anchor.IsInSubGroup() {
			return fmt.Errorf("invalid source G2 anchor")
		}
	}
	previous, err := readCanonicalG1(last[:])
	if err != nil {
		return err
	}
	for index := count; index < powers; index++ {
		var encoded [64]byte
		if _, err := io.ReadFull(additional, encoded[:]); err != nil {
			return err
		}
		next, err := readCanonicalG1(encoded[:])
		if err != nil {
			return fmt.Errorf("power %d: %w", index, err)
		}
		var negative bn254.G1Affine
		negative.Neg(&previous)
		valid, err := bn254.PairingCheck([]bn254.G1Affine{next, negative}, vk.G2[:])
		if err != nil {
			return err
		}
		if !valid {
			return fmt.Errorf("power %d does not extend the authenticated prefix", index)
		}
		if _, err := writer.Write(encoded[:]); err != nil {
			return err
		}
		previous = next
	}
	if _, err := writer.Write(suffix); err != nil {
		return err
	}
	if err := writer.Flush(); err != nil {
		return err
	}
	if err := file.Close(); err != nil {
		return err
	}
	return os.Link(file.Name(), output)
}
