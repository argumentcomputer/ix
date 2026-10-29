package main

import (
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
)

func writeJSON(path string, value any) error {
	return atomicFile(path, func(w io.Writer) error { enc := json.NewEncoder(w); enc.SetIndent("", "  "); return enc.Encode(value) })
}

func (m *manifest) checkFile(dir, name string) error {
	want, ok := m.Files[name]
	if !ok {
		return fmt.Errorf("artifact %s missing from manifest", name)
	}
	got, err := fileHash(filepath.Join(dir, name))
	if err != nil {
		return err
	}
	if got != want {
		return fmt.Errorf("artifact %s checksum or size differs", name)
	}
	return nil
}

func decodeJSON(path string, out any) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	return decodeReader(io.LimitReader(f, 16<<20), out)
}

func loadVerifyingKey(path string) (*verifyingKey, error) {
	var p verifyingKey
	if err := decodeJSON(path, &p); err != nil {
		return nil, err
	}
	if err := p.validate(); err != nil {
		return nil, err
	}
	return &p, nil
}

func witnessAssignment(p *verifyingKey, path string) (*wrapperCircuit, error) {
	var w witnessJSON
	if err := decodeJSON(path, &w); err != nil {
		return nil, err
	}
	return assignWitness(p, &w)
}

func readBinary(path string, value io.ReaderFrom) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	_, err = value.ReadFrom(f)
	return err
}

func verifyGroth16Files(keyPath, pin, proofPath, claim string) error {
	key, err := os.ReadFile(keyPath)
	if err != nil {
		return err
	}
	proof, err := os.ReadFile(proofPath)
	if err != nil {
		return err
	}
	trusted, err := unhex(pin, 32)
	if err != nil {
		return err
	}
	expected, err := unhex(claim, 32)
	if err != nil {
		return err
	}
	return verifyGroth16(key, trusted, proof, expected)
}
