package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"path/filepath"
	"sync"

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
	InnerVK      string              `json:"innerVKSHA256"`
	Constraints  int                 `json:"constraints"`
	Domain       uint64              `json:"domain"`
	PublicInputs int                 `json:"publicInputs"`
	Commitments  int                 `json:"commitments"`
	Setup        string              `json:"setup"`
	Ceremony     string              `json:"ceremonySHA256,omitempty"`
	KeysReady    bool                `json:"keysReady"`
	Files        map[string]artifact `json:"files"`
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
	if m.PublicInputs != 2 || m.Constraints < 1 || m.Constraints > 1<<27 ||
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

func groth16Load(dir string, m *groth16Manifest) (*verifyingKey, constraint.ConstraintSystem, error) {
	if err := m.validate(); err != nil {
		return nil, nil, err
	}
	data, err := readDescription(filepath.Join(dir, "vk.json"))
	if err != nil {
		return nil, nil, err
	}
	hash := sha256.Sum256(data)
	if hex.EncodeToString(hash[:]) != m.InnerVK || m.Files["vk.json"].SHA256 != m.InnerVK || m.Files["vk.json"].Bytes != int64(len(data)) {
		return nil, nil, fmt.Errorf("Groth16 inner verifier identity differs")
	}
	key, err := decodeVerifyingKey(data)
	if err != nil {
		return nil, nil, err
	}
	ccs := groth16.NewCS(curveID)
	if err := readVerified(filepath.Join(dir, "circuit.bin"), m.Files["circuit.bin"], ccs); err != nil {
		return nil, nil, err
	}
	domain, commitments, err := groth16Shape(ccs)
	if err != nil {
		return nil, nil, err
	}
	if domain != m.Domain || commitments != m.Commitments || ccs.GetNbConstraints() != m.Constraints {
		return nil, nil, fmt.Errorf("Groth16 circuit dimensions differ")
	}
	return key, ccs, nil
}

// TODO: Evaluate commitment-free arithmetic and range-check gadgets for Groth16.
// The commitment extension adds a pairing check and 128 Solidity proof bytes;
// a replacement must preserve the soundness of the deferred arithmetic checks.
func compileGroth16(schema []byte, path string) (circuitInfo, error) {
	var info circuitInfo
	key, err := decodeVerifyingKey(schema)
	if err != nil {
		return info, err
	}
	ccs, err := frontend.Compile(curveID.ScalarField(), r1cs.NewBuilder, newCircuit(key))
	if err != nil {
		return info, err
	}
	domain, commitments, err := groth16Shape(ccs)
	if err != nil {
		return info, err
	}
	info = circuitInfo{Domain: domain, Constraints: ccs.GetNbConstraints(), PublicInputs: 2, Commitments: commitments}
	return info, atomicFile(path, func(w io.Writer) error { _, err := ccs.WriteTo(w); return err })
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
		hash := sha256.New()
		var size int64
		if err := atomicFile(filepath.Join(dir, item.name), func(w io.Writer) error {
			var err error
			size, err = item.value.WriteTo(io.MultiWriter(w, hash))
			return err
		}); err != nil {
			return err
		}
		m.Files[item.name] = artifact{SHA256: hex.EncodeToString(hash.Sum(nil)), Bytes: size}
	}
	if err := atomicFile(filepath.Join(dir, "Groth16Verifier.sol"), func(w io.Writer) error {
		return vk.ExportSolidity(w, solidity.WithHashToFieldFunction(sha256.New()), solidity.WithPragmaVersion("^0.8.28"))
	}); err != nil {
		return err
	}
	for _, name := range []string{"Groth16Verifier.sol"} {
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
	return nil
}

func groth16DevelopmentSetup(dir string, m *groth16Manifest) error {
	_, ccs, err := groth16Load(dir, m)
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

type groth16Backend struct {
	CUDA    bool
	Device  int
	PinKeys bool
	Library string
}

func newGroth16Engine(config groth16Backend) (*groth16Engine, error) {
	if config.Device < 0 {
		return nil, fmt.Errorf("invalid Groth16 device")
	}
	if config.CUDA {
		return newGroth16CUDAEngine(config)
	}
	pk := groth16.NewProvingKey(curveID)
	return &groth16Engine{key: pk, native: pk.(*g16.ProvingKey), close: func() {}, prove: func(ccs constraint.ConstraintSystem, w witness.Witness) (groth16.Proof, error) {
		return groth16.Prove(ccs, pk, w, backend.WithProverHashToFieldFunction(sha256.New()))
	}}, nil
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

func openGroth16(dir string, metadata []byte, config groth16Backend) (*groth16Session, error) {
	var m groth16Manifest
	if err := decodeGroth16JSON(metadata, &m); err != nil {
		return nil, err
	}
	p, ccs, err := groth16Load(dir, &m)
	if err != nil {
		return nil, err
	}
	if !m.KeysReady {
		return nil, fmt.Errorf("Groth16 keys are not prepared")
	}
	for _, name := range []string{"Groth16Verifier.sol"} {
		if err := m.checkFile(dir, name); err != nil {
			return nil, err
		}
	}
	engine, err := newGroth16Engine(config)
	if err != nil {
		return nil, err
	}
	vk := new(g16.VerifyingKey)
	for _, item := range []struct {
		name  string
		value io.ReaderFrom
	}{{"proving-key.bin", engine.key}, {"verifying-key.bin", vk}} {
		if err := readVerified(filepath.Join(dir, item.name), m.Files[item.name], item.value); err != nil {
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
	return &groth16Session{key: p, ccs: ccs, vk: vk, engine: engine, manifest: &m}, nil
}

func (p *groth16Session) close() error {
	p.mu.Lock()
	defer p.mu.Unlock()
	if !p.closed {
		engine := p.engine
		p.closed = true
		p.engine, p.ccs, p.key, p.vk = nil, nil, nil, nil
		engine.close()
	}
	return nil
}

func groth16Public(digest []byte) (witness.Witness, error) {
	if len(digest) != 32 {
		return nil, fmt.Errorf("expected a 32-byte claim digest")
	}
	return frontend.NewWitness(&publicClaim{Claim: digestLimbs(digest)}, curveID.ScalarField(), frontend.PublicOnly())
}

func (p *groth16Session) proveAssignment(assignment frontend.Circuit, expected []byte) (native, solidityBytes []byte, err error) {
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

func verifyGroth16(key, trusted, data, claim []byte) error {
	if len(key) > 1<<20 || len(trusted) != 32 {
		return fmt.Errorf("invalid Groth16 verifying key")
	}
	hash := sha256.Sum256(key)
	if !bytes.Equal(hash[:], trusted) {
		return fmt.Errorf("Groth16 key differs from the trusted digest")
	}
	vk := new(g16.VerifyingKey)
	n, err := vk.ReadFrom(bytes.NewReader(key))
	if err != nil {
		return err
	}
	if n != int64(len(key)) {
		return fmt.Errorf("trailing Groth16 verifying key data")
	}
	commitments := len(vk.PublicAndCommitmentCommitted)
	if err := groth16CheckKey(vk, commitments); err != nil {
		return err
	}
	proof, err := decodeGroth16Proof(data, commitments)
	if err != nil {
		return err
	}
	public, err := groth16Public(claim)
	if err != nil {
		return err
	}
	return groth16.Verify(proof, vk, public, backend.WithVerifierHashToFieldFunction(sha256.New()))
}

func (p *groth16Session) prove(data, claim []byte) ([]byte, []byte, error) {
	var witness witnessJSON
	if err := decodeReader(bytes.NewReader(data), &witness); err != nil {
		return nil, nil, err
	}
	p.mu.Lock()
	if p.closed || p.failed {
		p.mu.Unlock()
		return nil, nil, fmt.Errorf("Groth16 prover is closed or failed")
	}
	assignment, err := assignWitness(p.key, &witness)
	p.mu.Unlock()
	if err != nil {
		return nil, nil, err
	}
	return p.proveAssignment(assignment, claim)
}

func setupGroth16(dir string, metadata []byte, kind uint32, descriptor, pin string) ([]byte, error) {
	var m groth16Manifest
	if err := decodeGroth16JSON(metadata, &m); err != nil {
		return nil, err
	}
	var err error
	switch kind {
	case 0:
		err = groth16DevelopmentSetup(dir, &m)
	case 1:
		err = groth16MPCSetup(dir, &m, descriptor, pin)
	case 2:
		err = groth16Import(dir, &m, descriptor, pin)
	default:
		return nil, fmt.Errorf("unknown Groth16 setup operation")
	}
	if err != nil {
		return nil, err
	}
	return json.Marshal(m)
}
