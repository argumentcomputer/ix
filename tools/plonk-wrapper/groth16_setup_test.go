package main

import (
	"bytes"
	"encoding/hex"
	"encoding/json"
	"io"
	"os"
	"path/filepath"
	"testing"

	"github.com/consensys/gnark/backend/groth16/bn254/mpcsetup"
	cs "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

func groth16TestArtifacts(t *testing.T, dir string) (*cs.R1CS, *groth16Manifest) {
	t.Helper()
	ccs, err := frontend.Compile(curveID.ScalarField(), r1cs.NewBuilder, &backendCircuit{Commit: true})
	if err != nil {
		t.Fatal(err)
	}
	domain, commitments, err := groth16Shape(ccs)
	if err != nil {
		t.Fatal(err)
	}
	data, err := os.ReadFile(filepath.Join("testdata", "bn254", "vk.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := atomicFile(filepath.Join(dir, "vk.json"), func(w io.Writer) error { _, err := w.Write(data); return err }); err != nil {
		t.Fatal(err)
	}
	if err := atomicFile(filepath.Join(dir, "circuit.bin"), func(w io.Writer) error { _, err := ccs.WriteTo(w); return err }); err != nil {
		t.Fatal(err)
	}
	m := &groth16Manifest{
		Constraints: ccs.GetNbConstraints(), Domain: domain, PublicInputs: 2, Commitments: commitments, Files: make(map[string]artifact)}
	for _, name := range []string{"vk.json", "circuit.bin"} {
		m.Files[name], err = fileHash(filepath.Join(dir, name))
		if err != nil {
			t.Fatal(err)
		}
	}
	m.InnerVK = m.Files["vk.json"].SHA256
	if err := writeJSON(filepath.Join(dir, "manifest.json"), m); err != nil {
		t.Fatal(err)
	}
	return ccs.(*cs.R1CS), m
}

func TestGroth16MPCAndAdmission(t *testing.T) {
	dir := t.TempDir()
	ccs, m := groth16TestArtifacts(t, dir)
	firstBeacon, secondBeacon := bytes.Repeat([]byte{1}, 32), bytes.Repeat([]byte{2}, 32)
	ceremony := groth16Ceremony{Format: "ix-bn254-groth16-ceremony-v1", Curve: "bn254", Circuit: m.Files["circuit.bin"].SHA256,
		Domain: m.Domain, Phase1Beacon: hex.EncodeToString(firstBeacon), Phase2Beacon: hex.EncodeToString(secondBeacon)}
	save := func(name string, object io.WriterTo) groth16CeremonyFile {
		t.Helper()
		path := filepath.Join(dir, name)
		if err := atomicFile(path, func(w io.Writer) error { _, err := object.WriteTo(w); return err }); err != nil {
			t.Fatal(err)
		}
		entry, err := fileHash(path)
		if err != nil {
			t.Fatal(err)
		}
		return groth16CeremonyFile{Path: name, Artifact: entry}
	}
	phase1 := mpcsetup.NewPhase1(m.Domain)
	phase1.Contribute()
	ceremony.Phase1 = []groth16CeremonyFile{save("phase1.bin", phase1)}
	commons, err := mpcsetup.VerifyPhase1(m.Domain, firstBeacon, phase1)
	if err != nil {
		t.Fatal(err)
	}
	phase2 := new(mpcsetup.Phase2)
	phase2.Initialize(ccs, &commons)
	phase2.Contribute()
	ceremony.Phase2 = []groth16CeremonyFile{save("phase2.bin", phase2)}
	metadata := filepath.Join(dir, "ceremony.json")
	publish := func() string {
		t.Helper()
		if err := writeJSON(metadata, ceremony); err != nil {
			t.Fatal(err)
		}
		entry, err := fileHash(metadata)
		if err != nil {
			t.Fatal(err)
		}
		return entry.SHA256
	}
	pin := publish()
	if err := groth16MPCSetup(dir, m, metadata, hex.EncodeToString(make([]byte, 32))); err == nil {
		t.Fatal("accepted untrusted ceremony metadata")
	}
	ceremony.Circuit = hex.EncodeToString(make([]byte, 32))
	if err := groth16MPCSetup(dir, m, metadata, publish()); err == nil {
		t.Fatal("accepted ceremony for another circuit")
	}
	ceremony.Circuit = m.Files["circuit.bin"].SHA256
	ceremony.Phase2 = append(ceremony.Phase2, ceremony.Phase2[0])
	if err := groth16MPCSetup(dir, m, metadata, publish()); err == nil {
		t.Fatal("accepted duplicated contribution")
	}
	ceremony.Phase2 = ceremony.Phase2[:1]
	pin = publish()
	if err := groth16MPCSetup(dir, m, metadata, pin); err != nil {
		t.Fatal(err)
	}
	_, _, err = groth16Load(dir, m)
	if err != nil {
		t.Fatal(err)
	}
	if m.Setup != "mpc" || m.Ceremony != pin {
		t.Fatal("missing ceremony binding")
	}
	release := groth16Release{Format: "ix-bn254-groth16-release-v1", Curve: "bn254", Circuit: m.Files["circuit.bin"].SHA256,
		InnerVK: m.InnerVK, Ceremony: pin, CommitmentHash: "sha256",
		ProvingKey:   groth16CeremonyFile{Path: "proving-key.bin", Artifact: m.Files["proving-key.bin"]},
		VerifyingKey: groth16CeremonyFile{Path: "verifying-key.bin", Artifact: m.Files["verifying-key.bin"]}}
	releasePath := filepath.Join(dir, "release.json")
	if err := writeJSON(releasePath, release); err != nil {
		t.Fatal(err)
	}
	releaseHash, err := fileHash(releasePath)
	if err != nil {
		t.Fatal(err)
	}
	imported := t.TempDir()
	_, importedMetadata := groth16TestArtifacts(t, imported)
	if err := groth16Import(imported, importedMetadata, releasePath, releaseHash.SHA256); err != nil {
		t.Fatal(err)
	}
	t.Setenv("IX_GROTH16_BACKEND", "cpu")
	encoded, err := json.Marshal(importedMetadata)
	if err != nil {
		t.Fatal(err)
	}
	p, err := openGroth16(imported, encoded, groth16Backend{})
	if err != nil {
		t.Fatal(err)
	}
	defer p.close()
	var digest [32]byte
	digest[0], digest[16] = 49, 1
	if _, _, err := p.proveAssignment(&backendCircuit{Claim: [2]frontend.Variable{49, 1}, X: 7, Commit: true}, digest[:]); err != nil {
		t.Fatal(err)
	}
	if p.manifest.Files["verifying-key.bin"].SHA256 != m.Files["verifying-key.bin"].SHA256 {
		t.Fatal("import changed verifying key")
	}
	if _, err := groth16BundlePath(metadata, groth16CeremonyFile{Path: "../secret"}); err == nil {
		t.Fatal("accepted escaping bundle path")
	}
}
