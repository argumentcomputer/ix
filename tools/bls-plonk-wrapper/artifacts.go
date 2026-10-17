package main

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
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
	Format, ExecutableSHA256, ProfileSHA256 string
	SRSBLAKE3                               string
	KeysReady                               bool
	Domain                                  uint64
	Constraints, PublicInputs, Commitments  int
	Files                                   map[string]artifact
	Seconds                                 map[string]float64
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

func writeJSON(path string, value any) error {
	return atomicFile(path, func(w io.Writer) error { enc := json.NewEncoder(w); enc.SetIndent("", "  "); return enc.Encode(value) })
}

func saveBinary(dir, name string, value io.WriterTo, m *manifest) error {
	path := filepath.Join(dir, name)
	if err := atomicFile(path, func(w io.Writer) error { _, err := value.WriteTo(w); return err }); err != nil {
		return err
	}
	entry, err := fileHash(path)
	if err != nil {
		return err
	}
	m.Files[name] = entry
	return nil
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

func loadManifest(dir string) (*manifest, error) {
	var m manifest
	if err := decodeJSON(filepath.Join(dir, "manifest.json"), &m); err != nil {
		return nil, err
	}
	if m.Format != artifactFormat || m.PublicInputs != 2 || m.Constraints < 1 || m.Constraints > 1<<26 || m.Domain < uint64(m.Constraints+2) || m.Domain > 1<<26 || m.Domain&(m.Domain-1) != 0 || m.Commitments < 0 || m.Commitments > 1024 || m.Files == nil || m.Seconds == nil {
		return nil, fmt.Errorf("invalid wrapper artifact manifest")
	}
	if m.KeysReady {
		if _, err := unhex(m.SRSBLAKE3, 32); err != nil {
			return nil, fmt.Errorf("invalid parameter receipt: %w", err)
		}
	}
	executable, err := os.Executable()
	if err != nil {
		return nil, err
	}
	identity, err := fileHash(executable)
	if err != nil {
		return nil, err
	}
	if identity.SHA256 != m.ExecutableSHA256 {
		return nil, fmt.Errorf("wrapper executable changed; recompile circuit and keys")
	}
	if err := m.checkFile(dir, "profile.json"); err != nil {
		return nil, err
	}
	if m.Files["profile.json"].SHA256 != m.ProfileSHA256 {
		return nil, fmt.Errorf("profile identity differs")
	}
	return &m, nil
}

func executableHash() (string, error) {
	path, err := os.Executable()
	if err != nil {
		return "", err
	}
	entry, err := fileHash(path)
	return entry.SHA256, err
}

func (m *manifest) checkKeys(dir string) error {
	if !m.KeysReady {
		return fmt.Errorf("PLONK keys are not prepared")
	}
	for _, name := range []string{"proving-key.bin", "verifying-key.bin", "PlonkVerifier.sol"} {
		if err := m.checkFile(dir, name); err != nil {
			return err
		}
	}
	return nil
}

func readBinary(path string, value io.ReaderFrom) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	n, err := value.ReadFrom(f)
	if err != nil {
		return err
	}
	stat, err := f.Stat()
	if err != nil {
		return err
	}
	if n != stat.Size() {
		return fmt.Errorf("trailing binary data in %s", path)
	}
	return nil
}
