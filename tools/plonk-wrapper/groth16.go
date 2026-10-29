package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"sync"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	g16 "github.com/consensys/gnark/backend/groth16/bn254"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/backend/witness"
	"github.com/consensys/gnark/constraint"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
)

const groth16ArtifactFormat = "ix-bn254-groth16-artifacts-v1"
const groth16MaxProofBytes = 196

func decodeGroth16JSON(data []byte, out any) error {
	decoder := json.NewDecoder(bytes.NewReader(data))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(out); err != nil {
		return err
	}
	if err := decoder.Decode(new(any)); err != io.EOF {
		return fmt.Errorf("trailing Groth16 JSON data")
	}
	return nil
}

type groth16Manifest struct {
	Format         string              `json:"format"`
	Curve          string              `json:"curve"`
	InnerVK        string              `json:"innerVKSHA256"`
	CommitmentHash string              `json:"commitmentHash"`
	Constraints    int                 `json:"constraints"`
	Domain         uint64              `json:"domain"`
	PublicInputs   int                 `json:"publicInputs"`
	Commitments    int                 `json:"commitments"`
	Setup          string              `json:"setup"`
	Ceremony       string              `json:"ceremonySHA256,omitempty"`
	KeysReady      bool                `json:"keysReady"`
	Files          map[string]artifact `json:"files"`
}

func groth16Shape(ccs constraint.ConstraintSystem) (uint64, int, error) {
	commitments := len(ccs.GetCommitments().CommitmentIndexes())
	if ccs.Field().Cmp(curveID.ScalarField()) != 0 || ccs.GetNbPublicVariables() != 3 {
		return 0, 0, fmt.Errorf("Groth16 requires BN254 and two public digest limbs plus the implicit one")
	}
	if ccs.GetNbConstraints() < 1 || ccs.GetNbConstraints() > 1<<27 || commitments > 1 {
		return 0, 0, fmt.Errorf("Groth16 circuit exceeds the supported domain or Solidity commitment count")
	}
	return ecc.NextPowerOfTwo(uint64(ccs.GetNbConstraints())), commitments, nil
}

func (m *groth16Manifest) validate() error {
	if m.Format != groth16ArtifactFormat || m.Curve != "bn254" || m.CommitmentHash != "sha256" ||
		m.PublicInputs != 2 || m.Constraints < 1 || m.Constraints > 1<<27 ||
		m.Domain != ecc.NextPowerOfTwo(uint64(m.Constraints)) || m.Commitments < 0 || m.Commitments > 1 || m.Files == nil {
		return fmt.Errorf("invalid Groth16 artifact manifest")
	}
	if _, err := unhex(m.InnerVK, 32); err != nil {
		return err
	}
	if m.KeysReady {
		switch m.Setup {
		case "development":
			if m.Ceremony != "" {
				return fmt.Errorf("development keys cannot claim an MPC receipt")
			}
		case "mpc":
			if _, err := unhex(m.Ceremony, 32); err != nil {
				return err
			}
		default:
			return fmt.Errorf("unknown Groth16 setup class")
		}
	} else if m.Setup != "" || m.Ceremony != "" {
		return fmt.Errorf("unprepared Groth16 circuit carries setup metadata")
	}
	return nil
}

func (m *groth16Manifest) checkFile(dir, name string) error {
	want, ok := m.Files[name]
	if !ok || want.Bytes < 1 {
		return fmt.Errorf("missing Groth16 artifact %s", name)
	}
	if _, err := unhex(want.SHA256, 32); err != nil {
		return err
	}
	got, err := fileHash(filepath.Join(dir, name))
	if err != nil {
		return err
	}
	if got != want {
		return fmt.Errorf("Groth16 artifact %s differs from its receipt", name)
	}
	return nil
}

func groth16Load(dir string) (*verifyingKey, constraint.ConstraintSystem, *groth16Manifest, error) {
	var m groth16Manifest
	if err := decodeJSON(filepath.Join(dir, "manifest.json"), &m); err != nil {
		return nil, nil, nil, err
	}
	if err := m.validate(); err != nil {
		return nil, nil, nil, err
	}
	for _, name := range []string{"vk.json", "circuit.bin"} {
		if err := m.checkFile(dir, name); err != nil {
			return nil, nil, nil, err
		}
	}
	if m.Files["vk.json"].SHA256 != m.InnerVK {
		return nil, nil, nil, fmt.Errorf("Groth16 inner verifier identity differs")
	}
	p, err := loadVerifyingKey(filepath.Join(dir, "vk.json"))
	if err != nil {
		return nil, nil, nil, err
	}
	ccs := groth16.NewCS(curveID)
	if err := readBinary(filepath.Join(dir, "circuit.bin"), ccs); err != nil {
		return nil, nil, nil, err
	}
	domain, commitments, err := groth16Shape(ccs)
	if err != nil {
		return nil, nil, nil, err
	}
	if domain != m.Domain || commitments != m.Commitments || ccs.GetNbConstraints() != m.Constraints {
		return nil, nil, nil, fmt.Errorf("Groth16 circuit dimensions differ")
	}
	return p, ccs, &m, nil
}

func groth16Compile(path, dir string) error {
	p, err := loadVerifyingKey(path)
	if err != nil {
		return err
	}
	identity, err := fileHash(path)
	if err != nil {
		return err
	}
	var existing *groth16Manifest
	if _, err := os.Stat(filepath.Join(dir, "manifest.json")); err == nil {
		_, _, m, err := groth16Load(dir)
		if err != nil {
			return err
		}
		if m.InnerVK != identity.SHA256 {
			return fmt.Errorf("Groth16 circuit belongs to another inner verifier")
		}
		existing = m
	} else if !os.IsNotExist(err) {
		return err
	}
	ccs, err := frontend.Compile(curveID.ScalarField(), r1cs.NewBuilder, newCircuit(p))
	if err != nil {
		return err
	}
	domain, commitments, err := groth16Shape(ccs)
	if err != nil {
		return err
	}
	if existing != nil {
		hash := sha256.New()
		if _, err := ccs.WriteTo(hash); err != nil {
			return err
		}
		if hex.EncodeToString(hash.Sum(nil)) != existing.Files["circuit.bin"].SHA256 {
			return fmt.Errorf("compiled Groth16 circuit changed; use a new artifact directory and setup")
		}
		return nil
	}
	m := groth16Manifest{Format: groth16ArtifactFormat, Curve: "bn254", InnerVK: identity.SHA256,
		CommitmentHash: "sha256", Domain: domain, Constraints: ccs.GetNbConstraints(), PublicInputs: 2,
		Commitments: commitments, Files: make(map[string]artifact)}
	data, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	if err := atomicFile(filepath.Join(dir, "vk.json"), func(w io.Writer) error { _, err := w.Write(data); return err }); err != nil {
		return err
	}
	if err := atomicFile(filepath.Join(dir, "circuit.bin"), func(w io.Writer) error { _, err := ccs.WriteTo(w); return err }); err != nil {
		return err
	}
	for _, name := range []string{"vk.json", "circuit.bin"} {
		m.Files[name], err = fileHash(filepath.Join(dir, name))
		if err != nil {
			return err
		}
	}
	return writeJSON(filepath.Join(dir, "manifest.json"), m)
}

func groth16CheckKey(vk *g16.VerifyingKey, commitments int) error {
	if commitments < 0 || commitments > 1 || len(vk.PublicAndCommitmentCommitted) != commitments ||
		len(vk.CommitmentKeys) != commitments || len(vk.G1.K) != 3+commitments {
		return fmt.Errorf("Groth16 key has an unsupported public-input or commitment schema")
	}
	return nil
}

func groth16CheckPair(pk *g16.ProvingKey, vk *g16.VerifyingKey, domain uint64) error {
	if pk.Domain.Cardinality != domain || !pk.G1.Alpha.Equal(&vk.G1.Alpha) ||
		!pk.G1.Beta.Equal(&vk.G1.Beta) || !pk.G1.Delta.Equal(&vk.G1.Delta) ||
		!pk.G2.Beta.Equal(&vk.G2.Beta) || !pk.G2.Delta.Equal(&vk.G2.Delta) {
		return fmt.Errorf("Groth16 proving and verifying keys differ")
	}
	return nil
}

func groth16SaveKeys(dir string, m *groth16Manifest, pk groth16.ProvingKey, vk groth16.VerifyingKey, setup, ceremony string) error {
	native := vk.(*g16.VerifyingKey)
	if err := groth16CheckKey(native, m.Commitments); err != nil {
		return err
	}
	if err := groth16CheckPair(pk.(*g16.ProvingKey), native, m.Domain); err != nil {
		return err
	}
	for _, item := range []struct {
		name  string
		value io.WriterTo
	}{{"proving-key.bin", pk}, {"verifying-key.bin", vk}} {
		if err := atomicFile(filepath.Join(dir, item.name), func(w io.Writer) error { _, err := item.value.WriteTo(w); return err }); err != nil {
			return err
		}
	}
	if err := atomicFile(filepath.Join(dir, "Groth16Verifier.sol"), func(w io.Writer) error {
		return vk.ExportSolidity(w, solidity.WithHashToFieldFunction(sha256.New()), solidity.WithPragmaVersion("^0.8.28"))
	}); err != nil {
		return err
	}
	for _, name := range []string{"proving-key.bin", "verifying-key.bin", "Groth16Verifier.sol"} {
		entry, err := fileHash(filepath.Join(dir, name))
		if err != nil {
			return err
		}
		m.Files[name] = entry
	}
	m.Setup, m.Ceremony, m.KeysReady = setup, ceremony, true
	if err := m.validate(); err != nil {
		return err
	}
	return writeJSON(filepath.Join(dir, "manifest.json"), m)
}

func groth16DevelopmentSetup(dir string) error {
	_, ccs, m, err := groth16Load(dir)
	if err != nil {
		return err
	}
	if m.KeysReady {
		return fmt.Errorf("Groth16 keys are already prepared")
	}
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		return err
	}
	return groth16SaveKeys(dir, m, pk, vk, "development", "")
}

type groth16Engine struct {
	key    groth16.ProvingKey
	native *g16.ProvingKey
	prove  func(constraint.ConstraintSystem, witness.Witness) (groth16.Proof, error)
	close  func()
}

func newGroth16Engine() (*groth16Engine, error) {
	switch os.Getenv("IX_GROTH16_BACKEND") {
	case "", "cpu":
		pk := groth16.NewProvingKey(curveID)
		return &groth16Engine{key: pk, native: pk.(*g16.ProvingKey), close: func() {}, prove: func(ccs constraint.ConstraintSystem, w witness.Witness) (groth16.Proof, error) {
			return groth16.Prove(ccs, pk, w, backend.WithProverHashToFieldFunction(sha256.New()))
		}}, nil
	case "cuda":
		return newGroth16CUDAEngine()
	default:
		return nil, fmt.Errorf("IX_GROTH16_BACKEND must be cpu or cuda")
	}
}

type groth16Session struct {
	mu             sync.Mutex
	key            *verifyingKey
	ccs            constraint.ConstraintSystem
	vk             *g16.VerifyingKey
	engine         *groth16Engine
	manifest       *groth16Manifest
	closed, failed bool
}

func openGroth16(dir string) (*groth16Session, error) {
	p, ccs, m, err := groth16Load(dir)
	if err != nil {
		return nil, err
	}
	if !m.KeysReady {
		return nil, fmt.Errorf("Groth16 keys are not prepared")
	}
	for _, name := range []string{"proving-key.bin", "verifying-key.bin", "Groth16Verifier.sol"} {
		if err := m.checkFile(dir, name); err != nil {
			return nil, err
		}
	}
	engine, err := newGroth16Engine()
	if err != nil {
		return nil, err
	}
	vk := new(g16.VerifyingKey)
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"proving-key.bin", engine.key}, {"verifying-key.bin", vk}} {
		if err := readBinary(filepath.Join(dir, item.name), item.value); err != nil {
			engine.close()
			return nil, err
		}
	}
	if err := groth16CheckKey(vk, m.Commitments); err != nil {
		engine.close()
		return nil, err
	}
	if err := groth16CheckPair(engine.native, vk, m.Domain); err != nil {
		engine.close()
		return nil, err
	}
	return &groth16Session{key: p, ccs: ccs, vk: vk, engine: engine, manifest: m}, nil
}

func (p *groth16Session) close() {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.closed {
		engine := p.engine
		p.closed = true
		p.engine, p.ccs, p.key, p.vk = nil, nil, nil, nil
		engine.close()
	}
}

func groth16Public(digest []byte) (witness.Witness, error) {
	if len(digest) != 32 {
		return nil, fmt.Errorf("expected a 32-byte claim digest")
	}
	return frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, curveID.ScalarField(), frontend.PublicOnly())
}

func (p *groth16Session) prove(assignment frontend.Circuit, expected []byte) (native, solidityBytes []byte, err error) {
	p.mu.Lock()
	defer p.mu.Unlock()
	defer func() {
		if err != nil {
			p.failed = true
		}
		if failure := recover(); failure != nil {
			p.failed = true
			panic(failure)
		}
	}()
	if p.closed || p.failed {
		return nil, nil, fmt.Errorf("Groth16 prover is closed or failed")
	}
	w, err := frontend.NewWitness(assignment, curveID.ScalarField())
	if err != nil {
		return nil, nil, err
	}
	public, err := groth16Public(expected)
	if err != nil {
		return nil, nil, err
	}
	actual, err := w.Public()
	if err != nil {
		return nil, nil, err
	}
	got, err := actual.MarshalBinary()
	if err != nil {
		return nil, nil, err
	}
	want, err := public.MarshalBinary()
	if err != nil {
		return nil, nil, err
	}
	if !bytes.Equal(got, want) {
		return nil, nil, fmt.Errorf("Groth16 witness claim differs from the independently expected digest")
	}
	proof, err := p.engine.prove(p.ccs, w)
	if err != nil {
		return nil, nil, err
	}
	if err := groth16.Verify(proof, p.vk, public, backend.WithVerifierHashToFieldFunction(sha256.New())); err != nil {
		return nil, nil, err
	}
	var encoded bytes.Buffer
	if _, err := proof.WriteTo(&encoded); err != nil {
		return nil, nil, err
	}
	if _, err := decodeGroth16Proof(encoded.Bytes(), p.manifest.Commitments); err != nil {
		return nil, nil, err
	}
	return encoded.Bytes(), proof.(*g16.Proof).MarshalSolidity(), nil
}

func decodeGroth16Proof(data []byte, commitments int) (*g16.Proof, error) {
	if commitments < 0 || commitments > 1 || len(data) != 164+32*commitments {
		return nil, fmt.Errorf("invalid Groth16 proof length")
	}
	if binary.BigEndian.Uint32(data[128:132]) != uint32(commitments) {
		return nil, fmt.Errorf("Groth16 commitment count differs from the trusted key")
	}
	for _, offset := range []int{0, 32, 96, 132, 132 + 32*commitments} {
		if !isCompressedPoint(data[offset]) {
			return nil, fmt.Errorf("noncanonical Groth16 point encoding")
		}
	}
	proof := new(g16.Proof)
	n, err := proof.ReadFrom(bytes.NewReader(data))
	if err != nil {
		return nil, err
	}
	if n != int64(len(data)) {
		return nil, fmt.Errorf("trailing Groth16 proof data")
	}
	if commitments == 0 && !proof.CommitmentPok.IsInfinity() {
		return nil, fmt.Errorf("unexpected unused Groth16 commitment proof")
	}
	var canonical bytes.Buffer
	if _, err := proof.WriteTo(&canonical); err != nil {
		return nil, err
	}
	if !bytes.Equal(data, canonical.Bytes()) {
		return nil, fmt.Errorf("noncanonical Groth16 proof")
	}
	return proof, nil
}

func groth16Verify(keyPath, keyHash, proofPath, claim string) error {
	if _, err := unhex(keyHash, 32); err != nil {
		return err
	}
	key, err := fileHash(keyPath)
	if err != nil {
		return err
	}
	if key.Bytes > 1<<20 || key.SHA256 != keyHash {
		return fmt.Errorf("Groth16 key differs from the trusted digest")
	}
	vk := new(g16.VerifyingKey)
	if err := readBinary(keyPath, vk); err != nil {
		return err
	}
	commitments := len(vk.PublicAndCommitmentCommitted)
	if err := groth16CheckKey(vk, commitments); err != nil {
		return err
	}
	digest, err := unhex(claim, 32)
	if err != nil {
		return err
	}
	f, err := os.Open(proofPath)
	if err != nil {
		return err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, groth16MaxProofBytes+1))
	if err != nil {
		return err
	}
	proof, err := decodeGroth16Proof(data, commitments)
	if err != nil {
		return err
	}
	public, err := groth16Public(digest)
	if err != nil {
		return err
	}
	return groth16.Verify(proof, vk, public, backend.WithVerifierHashToFieldFunction(sha256.New()))
}

func groth16Prove(dir, path, claim, out string) error {
	expected, err := unhex(claim, 32)
	if err != nil {
		return err
	}
	p, err := openGroth16(dir)
	if err != nil {
		return err
	}
	defer p.close()
	assignment, err := witnessAssignment(p.key, path)
	if err != nil {
		return err
	}
	started := time.Now()
	native, payload, err := p.prove(assignment, expected)
	if err != nil {
		return err
	}
	for _, item := range []struct {
		name string
		data []byte
	}{{"proof.bin", native}, {"proof.solidity.bin", payload}} {
		if err := atomicFile(filepath.Join(out, item.name), func(w io.Writer) error { _, err := w.Write(item.data); return err }); err != nil {
			return err
		}
	}
	selected := os.Getenv("IX_GROTH16_BACKEND")
	if selected == "" {
		selected = "cpu"
	}
	return writeJSON(filepath.Join(out, "report.json"), map[string]any{
		"system": "groth16", "curve": "bn254", "backend": selected, "setup": p.manifest.Setup,
		"proveVerifySeconds": time.Since(started).Seconds(), "nativeBytes": len(native), "solidityBytes": len(payload),
		"claimDigest": hex.EncodeToString(expected), "verifyingKeySHA256": p.manifest.Files["verifying-key.bin"].SHA256,
	})
}

func runGroth16(args []string) error {
	if len(args) == 4 && args[0] == "setup-mpc" {
		return groth16MPCSetup(args[1], args[2], args[3])
	}
	if len(args) == 4 && args[0] == "import" {
		return groth16Import(args[1], args[2], args[3])
	}
	if len(args) == 1 && args[0] == "capabilities" {
		fmt.Printf("{\"system\":\"groth16\",\"curve\":\"bn254\",\"cuda\":%t}\n", groth16CUDAAvailable())
		return nil
	}
	if len(args) == 3 && args[0] == "compile" {
		return groth16Compile(args[1], args[2])
	}
	if len(args) == 2 && args[0] == "setup-development" {
		return groth16DevelopmentSetup(args[1])
	}
	if len(args) == 5 && args[0] == "prove" {
		return groth16Prove(args[1], args[2], args[3], args[4])
	}
	if len(args) == 5 && args[0] == "verify" {
		return groth16Verify(args[1], args[2], args[3], args[4])
	}
	return fmt.Errorf("usage: groth16 compile <vk.json> <artifacts> | setup-development <artifacts> | setup-mpc <artifacts> <ceremony.json> <trusted-sha256> | import <artifacts> <release.json> <trusted-sha256> | prove <artifacts> <witness.json> <expected-claim-digest> <out> | verify <key.bin> <trusted-key-sha256> <proof.bin> <expected-claim-digest> | capabilities")
}
