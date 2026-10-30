package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
)

// TODO: Decide between SHA-256 and BLAKE3 for artifact/cache metadata.
// Coordinate Rust/Go encodings and any catalog or envelope key-ID changes;
// proof-protocol hashes have separate compatibility requirements.
type artifact struct {
	SHA256 string
	Bytes  int64
}

func fileHash(path string) (artifact, error) {
	f, err := os.Open(path)
	if err != nil {
		return artifact{}, err
	}
	defer f.Close()
	h := sha256.New()
	n, err := io.Copy(h, f)
	return artifact{SHA256: hex.EncodeToString(h.Sum(nil)), Bytes: n}, err
}

func atomicFile(path string, write func(io.Writer) error) error {
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return err
	}
	f, err := os.CreateTemp(filepath.Dir(path), ".plonk-*")
	if err != nil {
		return err
	}
	defer os.Remove(f.Name())
	defer f.Close()
	if err := write(f); err != nil {
		return err
	}
	if err := f.Sync(); err != nil {
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	if err := os.Rename(f.Name(), path); err != nil {
		return err
	}
	d, err := os.Open(filepath.Dir(path))
	if err != nil {
		return err
	}
	defer d.Close()
	return d.Sync()
}

func readVerified(path string, expected artifact, value io.ReaderFrom) error {
	if expected.Bytes < 1 {
		return fmt.Errorf("missing artifact %s", path)
	}
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	hash := sha256.New()
	n, err := value.ReadFrom(io.TeeReader(io.LimitReader(f, expected.Bytes+1), hash))
	if err != nil {
		return err
	}
	if n != expected.Bytes || hex.EncodeToString(hash.Sum(nil)) != expected.SHA256 {
		return fmt.Errorf("decoded artifact differs: %s", path)
	}
	var extra [1]byte
	if n, err := f.Read(extra[:]); n != 0 || err != io.EOF {
		return fmt.Errorf("trailing artifact bytes: %s", path)
	}
	return nil
}

func readDescription(path string) ([]byte, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, (16<<20)+1))
	if err != nil {
		return nil, err
	}
	if len(data) > 16<<20 {
		return nil, fmt.Errorf("verifier description is too large")
	}
	return data, nil
}
