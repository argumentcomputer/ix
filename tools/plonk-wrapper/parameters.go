//go:build plonk || !groth16

package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
)

func readAffinePoints(r io.Reader, count uint64) ([]nativeG1, error) {
	points := make([]nativeG1, count)
	for i := range points {
		var raw [2 * baseBytes]byte
		if _, err := io.ReadFull(r, raw[:]); err != nil {
			return nil, err
		}
		if err := points[i].X.SetBytesCanonical(raw[:baseBytes]); err != nil {
			return nil, err
		}
		if err := points[i].Y.SetBytesCanonical(raw[baseBytes:]); err != nil {
			return nil, err
		}
	}
	return points, nil
}

func writeAffinePoints(w io.Writer, points []nativeG1) error {
	b := bufio.NewWriterSize(w, 1<<20)
	for _, point := range points {
		x, y := point.X.Bytes(), point.Y.Bytes()
		if _, err := b.Write(x[:]); err != nil {
			return err
		}
		if _, err := b.Write(y[:]); err != nil {
			return err
		}
	}
	return b.Flush()
}

func loadLagrange(srs *nativeSRS, domain uint64, path, expected string) (*nativeSRS, error) {
	if domain < 2 || domain > 1<<26 || domain&(domain-1) != 0 || uint64(len(srs.Pk.G1)) < domain+3 {
		return nil, fmt.Errorf("invalid Lagrange domain")
	}
	if expected != "" {
		f, err := os.Open(path)
		if err != nil {
			return nil, err
		}
		defer f.Close()
		info, err := f.Stat()
		if err != nil {
			return nil, err
		}
		if info.Size() != int64(2*baseBytes*domain) {
			return nil, fmt.Errorf("Lagrange cache size differs")
		}
		hash := sha256.New()
		reader := bufio.NewReaderSize(io.TeeReader(f, hash), 1<<20)
		points, err := readAffinePoints(reader, domain)
		if err != nil {
			return nil, err
		}
		if _, err := reader.ReadByte(); err != io.EOF {
			return nil, fmt.Errorf("trailing Lagrange cache data")
		}
		if hex.EncodeToString(hash.Sum(nil)) != expected {
			return nil, fmt.Errorf("Lagrange cache checksum differs")
		}
		return &nativeSRS{Pk: nativeKzgProvingKey{G1: points}, Vk: srs.Vk}, nil
	}
	points, err := toLagrange(srs.Pk.G1[:domain])
	if err != nil {
		return nil, err
	}
	if err := atomicFile(path, func(w io.Writer) error { return writeAffinePoints(w, points) }); err != nil {
		return nil, err
	}
	return &nativeSRS{Pk: nativeKzgProvingKey{G1: points}, Vk: srs.Vk}, nil
}
