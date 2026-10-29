package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
)

type artifact struct {
	SHA256 string
	Bytes  int64
}
type manifest struct {
	InnerVKSHA256                          string
	SRSBLAKE3                              string
	KeysReady                              bool
	Domain                                 uint64
	Constraints, PublicInputs, Commitments int
	Files                                  map[string]artifact
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

func (m *manifest) validate() error {
	if m.PublicInputs != 2 || m.Constraints < 1 || m.Constraints > 1<<26 || m.Domain < uint64(m.Constraints+2) || m.Domain > 1<<26 || m.Domain&(m.Domain-1) != 0 || m.Commitments < 0 || m.Commitments > 1024 || m.Files == nil {
		return fmt.Errorf("invalid wrapper artifact metadata")
	}
	if m.KeysReady {
		if _, err := unhex(m.SRSBLAKE3, 32); err != nil {
			return err
		}
	}
	if m.Files["vk.json"].SHA256 != m.InnerVKSHA256 {
		return fmt.Errorf("verifying key identity differs")
	}
	return nil
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
