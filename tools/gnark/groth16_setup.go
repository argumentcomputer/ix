//go:build groth16 || !plonk

package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/consensys/gnark/backend/groth16"
	g16 "github.com/consensys/gnark/backend/groth16/bn254"
	"github.com/consensys/gnark/backend/groth16/bn254/mpcsetup"
	cs "github.com/consensys/gnark/constraint/bn254"
)

type groth16CeremonyFile struct {
	Path     string   `json:"path"`
	Artifact artifact `json:"artifact"`
}

type groth16Ceremony struct {
	Format       string                `json:"format"`
	Curve        string                `json:"curve"`
	Circuit      string                `json:"circuitSHA256"`
	Domain       uint64                `json:"domain"`
	Phase1Beacon string                `json:"phase1Beacon"`
	Phase2Beacon string                `json:"phase2Beacon"`
	Phase1       []groth16CeremonyFile `json:"phase1"`
	Phase2       []groth16CeremonyFile `json:"phase2"`
}

type groth16Release struct {
	Format         string              `json:"format"`
	Curve          string              `json:"curve"`
	Circuit        string              `json:"circuitSHA256"`
	InnerVK        string              `json:"innerVKSHA256"`
	Ceremony       string              `json:"ceremonySHA256"`
	CommitmentHash string              `json:"commitmentHash"`
	ProvingKey     groth16CeremonyFile `json:"provingKey"`
	VerifyingKey   groth16CeremonyFile `json:"verifyingKey"`
}

func readGroth16Artifact(path string, expected artifact, value io.ReaderFrom) error {
	if expected.Bytes < 1 || expected.Bytes > 1<<42 {
		return fmt.Errorf("invalid Groth16 artifact size")
	}
	return readVerified(path, expected, value)
}

func groth16BundlePath(metadata string, item groth16CeremonyFile) (string, error) {
	if item.Path == "" || filepath.IsAbs(item.Path) || strings.Contains(item.Path, "\\") {
		return "", fmt.Errorf("invalid Groth16 bundle path")
	}
	for _, part := range strings.Split(item.Path, "/") {
		if part == ".." {
			return "", fmt.Errorf("Groth16 bundle path escapes its directory")
		}
	}
	return filepath.Join(filepath.Dir(metadata), item.Path), nil
}

func groth16PinnedJSON(path, pin string, out any) error {
	if _, err := unhex(pin, 32); err != nil {
		return err
	}
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, (1<<20)+1))
	if err != nil {
		return err
	}
	if len(data) > 1<<20 {
		return fmt.Errorf("Groth16 setup metadata exceeds its size limit")
	}
	h := sha256.Sum256(data)
	if hex.EncodeToString(h[:]) != pin {
		return fmt.Errorf("Groth16 setup metadata differs from the independently trusted digest")
	}
	return decodeReader(bytes.NewReader(data), out)
}

func groth16MPCSetup(dir string, m *groth16Manifest, path, trusted string) error {
	_, ccs, err := groth16Load(dir, m)
	if err != nil {
		return err
	}
	if m.KeysReady {
		return fmt.Errorf("Groth16 keys are already prepared")
	}
	var ceremony groth16Ceremony
	if err := groth16PinnedJSON(path, trusted, &ceremony); err != nil {
		return err
	}
	if ceremony.Format != "ix-bn254-groth16-ceremony-v1" || ceremony.Curve != "bn254" ||
		ceremony.Circuit != m.Files["circuit.bin"].SHA256 || ceremony.Domain != m.Domain ||
		len(ceremony.Phase1) == 0 || len(ceremony.Phase2) == 0 || len(ceremony.Phase1) > 1024 || len(ceremony.Phase2) > 1024 {
		return fmt.Errorf("Groth16 ceremony does not match this circuit")
	}
	b1, err := unhex(ceremony.Phase1Beacon, 32)
	if err != nil {
		return err
	}
	b2, err := unhex(ceremony.Phase2Beacon, 32)
	if err != nil {
		return err
	}
	previous1 := mpcsetup.NewPhase1(m.Domain)
	for i, contribution := range ceremony.Phase1 {
		next := new(mpcsetup.Phase1)
		name, err := groth16BundlePath(path, contribution)
		if err != nil {
			return err
		}
		if err := readGroth16Artifact(name, contribution.Artifact, next); err != nil {
			return err
		}
		if err := previous1.Verify(next); err != nil {
			return fmt.Errorf("Groth16 phase one contribution %d: %w", i, err)
		}
		previous1 = next
	}
	commons := previous1.Seal(b1)
	previous2 := new(mpcsetup.Phase2)
	evaluations := previous2.Initialize(ccs.(*cs.R1CS), &commons)
	for i, contribution := range ceremony.Phase2 {
		next := new(mpcsetup.Phase2)
		name, err := groth16BundlePath(path, contribution)
		if err != nil {
			return err
		}
		if err := readGroth16Artifact(name, contribution.Artifact, next); err != nil {
			return err
		}
		if err := previous2.Verify(next); err != nil {
			return fmt.Errorf("Groth16 phase two contribution %d: %w", i, err)
		}
		previous2 = next
	}
	pk, vk := previous2.Seal(&commons, &evaluations, b2)
	return groth16SaveKeys(dir, m, pk, vk, "mpc", trusted)
}

func groth16Import(dir string, m *groth16Manifest, path, trusted string) error {
	_, _, err := groth16Load(dir, m)
	if err != nil {
		return err
	}
	if m.KeysReady {
		return fmt.Errorf("Groth16 keys are already prepared")
	}
	var release groth16Release
	if err := groth16PinnedJSON(path, trusted, &release); err != nil {
		return err
	}
	if release.Format != "ix-bn254-groth16-release-v1" || release.Curve != "bn254" ||
		release.Circuit != m.Files["circuit.bin"].SHA256 || release.InnerVK != m.InnerVK || release.CommitmentHash != "sha256" {
		return fmt.Errorf("Groth16 release does not match this circuit")
	}
	if _, err := unhex(release.Ceremony, 32); err != nil {
		return err
	}
	pk := groth16.NewProvingKey(curveID)
	vk := new(g16.VerifyingKey)
	for _, item := range []struct {
		source groth16CeremonyFile
		target io.ReaderFrom
	}{{release.ProvingKey, pk}, {release.VerifyingKey, vk}} {
		name, err := groth16BundlePath(path, item.source)
		if err != nil {
			return err
		}
		if err := readGroth16Artifact(name, item.source.Artifact, item.target); err != nil {
			return err
		}
	}
	if pk.(*g16.ProvingKey).Domain.Cardinality != m.Domain {
		return fmt.Errorf("Groth16 proving key domain differs")
	}
	return groth16SaveKeys(dir, m, pk, vk, "mpc", release.Ceremony)
}
